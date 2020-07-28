/******************************************************************************
 * jpanic.c 
 *
 * GOAT-Plugs: GCC Obfuscation Augmentation Tools
 * 
 * JPanic plugin - Inserts junk instructions and functions throughout a program.
 *
 * Copyright (C) 2011,2015 Matt Davis (enferex) of 757Labs
 * (www.757Labs.org)
 *
 * Special thanks to JPanic for schooling me on ideas and junk instructions
 *
 * jpanic.c is part of the GOAT-Plugs GCC plugin set.
 * GOAT-Plugs is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * GOAT-Plugs is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with GOAT-Plugs.  If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************/

#include <stdio.h>
#include <gcc-plugin.h>
#include <coretypes.h>
#include <tree.h>
#include <tree-pass.h>
#include <tree-ssa-alias.h>
#include <function.h>
#include <cgraph.h>
#include <internal-fn.h>
#include <stringpool.h>
#include <gimple-expr.h>
#include <gimple.h>
#include <gimple-iterator.h>
#include <gimple-ssa.h>
#include <gimplify.h>
#include <vec.h>
#include <tree-vrp.h>
#include <tree-ssanames.h>
#include <time.h>

#define ENABLE_JUNK_MATH 0

/* Required for the plugin to work */
int plugin_is_GPL_compatible = 1;


/* Max junk statements to toss out throughout the program */
static int max_junk;


/* Help info about the plugin if one were to use gcc's --version --help */
static struct plugin_info jpanic_info =
{
    .version = "0.2",
    .help = "Inserts junk instructions and dummy functions throughout the "
            "program.\n"
            "The chance to insert junk occurs per each statement in the "
            "program.  A user specified value can set an upper bound to the "
            "amount of junk (new functions, or useless statements in an "
            "existing function, to add:\n"
            "-fplugin-arg-jpanic-maxjunk=<num>",
};


/* How we test to ensure the gcc version will work with our plugin */
static struct plugin_gcc_version jpanic_ver =
{
    .basever = "9",
};


typedef enum 
{
    JUNK_ASSIGN,
#if ENABLE_JUNK_MATH
    JUNK_ADD,
    JUNK_SUB,
    JUNK_MUL,
#endif
    JUNK_NEW_FN, /* Create and call a new function */
    JUNK_OLD_FN, /* Call an existing function      */
    N_JUNK_TYPES
} junk_type_e;


/* Global vector of junk function decl nodes */
vec<tree> junk_fns;

static inline void varpool_finalize_decl(tree decl)
{
	varpool_node::finalize_decl(decl);
}

static inline void varpool_add_new_variable(tree decl)
{
	varpool_node::add(decl);
}

/* Global variable we set the left-hand-side of junk statements assign to.
 * This should prevent gcc from trying to remove the junk :-)
 */
static tree jpanic = NULL_TREE;
static void init_jpanic_global(void)
{
    if (jpanic == NULL_TREE)
    {
        jpanic = build_decl(BUILTINS_LOCATION, VAR_DECL, NULL, integer_type_node);
        //jpanic = make_ssa_name(jpanic, gimple_build_nop());
        DECL_NAME(jpanic) = create_tmp_var_name("__el_jpanic");
        TREE_STATIC(jpanic) = 1;
        DECL_ARTIFICIAL(jpanic) = 1;
        varpool_add_new_variable(jpanic);
    }
}


static gimple *build_junk_assign(void)
{
    tree rhs;
    rhs = create_tmp_var(integer_type_node, "_junk");
    rhs = make_ssa_name(rhs, gimple_build_nop());
    return gimple_build_assign(jpanic, rhs);
}

static inline void cgraph_add_new_function(tree fndecl, bool lowerd)
{
    cgraph_node::add_new_function(fndecl, lowerd);
}

#if ENABLE_JUNK_MATH
/* lhs = rhs1 OP rhs2 */
static gimple *build_junk_math(junk_type_e op)
{
    tree rhs1, rhs2;
    enum tree_code code;

    if (op == JUNK_ADD)
      code = PLUS_EXPR;
    else if (op == JUNK_SUB)
      code = MINUS_EXPR;
    else /* (op == JUNK_MUL) */
      code = MULT_EXPR;

    rhs1 = create_tmp_var(integer_type_node, "_junk");
    rhs1 = make_ssa_name(rhs1, gimple_build_nop());	// TODO: this cause internal error
     
    DECL_ARTIFICIAL(rhs1) = 1;
    TREE_THIS_VOLATILE(rhs1) = 1;
    DECL_PRESERVE_P(rhs1) = 1;

    rhs2 = create_tmp_var(integer_type_node, "_junk");
    rhs2 = make_ssa_name(rhs2, gimple_build_nop());	// TODO: this cause internal error
    DECL_ARTIFICIAL(rhs2) = 1;
    TREE_THIS_VOLATILE(rhs2) = 1;
    DECL_PRESERVE_P(rhs2) = 1;

    //return gimple_build_assign(code, jpanic, rhs1, rhs2);
    return gimple_build_assign(jpanic, code, rhs1, rhs2);
}
#endif

/* Creates an empty function */
static tree create_junk_fn(void)
{
    char fnname[32] = {0};
    tree decl, resdecl, initial, proto;
    static unsigned id;

    /* Func decl */
    ++id;
    snprintf(fnname, 31, "__func%u", id);
    proto = build_varargs_function_type_list(integer_type_node, NULL_TREE);
    decl = build_fn_decl(fnname, proto);
    SET_DECL_ASSEMBLER_NAME(decl, get_identifier(fnname));
   
    /* Result */ 
    resdecl=build_decl(BUILTINS_LOCATION,RESULT_DECL,NULL_TREE,integer_type_node);
    DECL_ARTIFICIAL(resdecl) = 1;
    DECL_CONTEXT(resdecl) = decl;
    DECL_RESULT(decl) = resdecl;
    
    /* Initial */
    initial = make_node(BLOCK);
    TREE_USED(initial) = 1;
    DECL_INITIAL(decl) = initial;
    DECL_UNINLINABLE(decl) = 1;
    DECL_EXTERNAL(decl) = 0;
    DECL_PRESERVE_P(decl) = 1;

    /* Func decl */
    TREE_USED(decl) = 1;
    TREE_PUBLIC(decl) = 1;
    TREE_STATIC(decl) = 1;
    DECL_ARTIFICIAL(decl) = 1;

    /* Make the function */
    push_struct_function(decl);
    cfun->function_end_locus = BUILTINS_LOCATION;
    gimplify_function_tree(decl);

    /* Update */
    cgraph_add_new_function(decl, false);
    pop_cfun();

    /* Add to a vec of all junk funs we maintain */
    junk_fns.safe_push(decl);

    printf("Created unkfn\n");

    return decl;
}


static tree find_junk_fn(void)
{
    unsigned len = junk_fns.length();

    /* No junk functions added yet... heck, add one */
    if (len == 0)
      return create_junk_fn();

    return junk_fns[rand() % len];
}


/* Returns 'true' if the function 'decl' is one we have added */
static bool is_junk_fn(tree decl)
{
    unsigned i;
    tree junk;

    FOR_EACH_VEC_ELT(junk_fns, i, junk)
      if (junk == decl)
        return true;

    return false;
}


/* Craete a NOP (junk) instruction statement. 
 * Returns the junk statement created
 */
static gimple *create_junk_stmt(void)
{
    tree node;
    gimple *stmt;
    junk_type_e junk_type;

    /* Choose a thing to insert */
    junk_type = (junk_type_e)(rand() % N_JUNK_TYPES);
    switch (junk_type)
    {
        case JUNK_ASSIGN:
            stmt = build_junk_assign();
            break;
#if ENABLE_JUNK_MATH
        case JUNK_ADD:
        case JUNK_SUB:
        case JUNK_MUL:
            printf("junk math\n");
            stmt = build_junk_math(junk_type);
            break;
#endif
        case JUNK_NEW_FN:
            /* Do not add a call to a junk function if we are one */
            if (!is_junk_fn(cfun->decl))
            {
                node = create_junk_fn();
                stmt = gimple_build_call(node, 0);
            }
            else
              stmt = gimple_build_nop();
            break;

        case JUNK_OLD_FN:
            /* Do not add a call to a junk function if we are one */
            if (!is_junk_fn(cfun->decl))
            {
                node = find_junk_fn();
                stmt = gimple_build_call(node, 0);
            }
            else
              stmt = gimple_build_nop();
            break;
        default:
            abort();
    }

    return stmt;
}


/* Called once per function */
static unsigned int jpanic_exec(function *fun)
{
    basic_block bb;
    gimple *stmt;
    gimple_stmt_iterator gsi;
    static bool initted;

    if (!initted)
    {
        init_jpanic_global();
        initted = true;
    }

    printf("jpanic %s\n", function_name(fun));

    /* For each basic block ... for each statement ... if rand is true insert
     * junk before the statement
     */
    FOR_EACH_BB_FN(bb, fun)
      for (gsi=gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
        if ((max_junk > 0) && (rand() % 2 && max_junk))
        {
            stmt = create_junk_stmt();
            gsi_insert_before(&gsi, stmt, GSI_NEW_STMT);
            gsi_next(&gsi);

            /* If this is a junk function, assign the return value to the global
             * variable so that we make the junk actually get compiled in.  GCC
             * is smart and doesn't want to compile in junk.
             */
            if (is_junk_fn(fun->decl))
            {
                gsi_insert_before(&gsi, gimple_build_assign(jpanic,
                            DECL_RESULT(cfun->decl)), GSI_NEW_STMT);
            }
            --max_junk;
        }

#ifdef GOAT_DEBUG
    debug_function(cfun->decl, 0); 
#endif

    return 0;
}


namespace{
const pass_data pass_data_jpanic =
{
    .type = GIMPLE_PASS, /* Type           */
    .name = "jpanic",    /* Name           */
    .optinfo_flags = OPTGROUP_NONE,           /* opt-info flags */
    .tv_id = TV_NONE,     /* Time var id    */
    .properties_required = 0,           /* Prop. required */
    .properties_provided = 0,           /* Prop. provided */
    .properties_destroyed = 0,           /* Prop destroyed */
    .todo_flags_start = 0,           /* Flags start    */
    .todo_flags_finish = 0            /* Flags finish   */
};


class pass_jpanic : public gimple_opt_pass
{
public:
    pass_jpanic() : gimple_opt_pass(pass_data_jpanic, NULL) {;}
    virtual unsigned int execute(function *fun) override { return jpanic_exec(fun); }
};
} /* Anonymous namespace */

struct register_pass_info my_passinfo
{

    /* Setup the info to register with gcc telling when we want to be called and
     * to what gcc should call, when it's time to be called.
     */
    .pass = new pass_jpanic(),
    .reference_pass_name = "ssa",
    .ref_pass_instance_number = 1,
    .pos_op = PASS_POS_INSERT_AFTER
};

/* Return 0 on success or error code on failure */
int plugin_init(struct plugin_name_args   *info,  /* Argument info  */
                struct plugin_gcc_version *ver)   /* Version of GCC */
{
    int i;

    /* Check version */
    if (strncmp(ver->basever, jpanic_ver.basever, strlen(jpanic_ver.basever)))
      return -1;

    register_callback("jpanic", PLUGIN_PASS_MANAGER_SETUP, NULL, &my_passinfo);
    register_callback("jpanic", PLUGIN_INFO, NULL, &jpanic_info);

    /* Seed the rng */
    srand(time(NULL));

    /* How much junk we should create */
    for (i=0; i<info->argc; ++i)
      if (strncmp("maxjunk", info->argv[i].key, 7) == 0)
        max_junk = atoi(info->argv[i].value);

    if (max_junk < 0)
      max_junk = 0;

    printf("[jpanic] Max junk set to: %d\n", max_junk);

    /* Successful initialization */ 
    return 0;
}
