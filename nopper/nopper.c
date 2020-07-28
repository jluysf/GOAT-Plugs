/******************************************************************************
 * nopper.c 
 *
 * GOAT-Plugs: GCC Obfuscation Augmentation Tools
 * 
 * Nopper plugin - Example GCC plugin to insert no-ops into a program.
 *
 * Copyright (C) 2011,2015 Matt Davis (enferex) of 757Labs
 * (www.757Labs.org)
 *
 * nopper.c is part of the GOAT-Plugs GCC plugin set.
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
#include <basic-block.h>
#include <cgraph.h>
#include <function.h>
#include <internal-fn.h>
#include <is-a.h>
#include <gimple-expr.h>
#include <gimple.h>
#include <gimple-iterator.h>
#include <plugin.h>
#include <vec.h>


/* Required for the plugin to work */
int plugin_is_GPL_compatible = 1;


/* Global vect of functions to ignore (i.e., not insert nops into)
 * A function can be ignored by using the function attribute:
 * "__attribute__((nopper))" on the function declaration.
 */
vec<tree> ignorez = vNULL;


/* Help info about the plugin if one were to use gcc's --version --help */
static struct plugin_info nopper_info =
{
    .version = "0.4",
    .help = "Inserts user-defined amount of nop instructions throughout the "
            ".text section of the binary.\n"
            "-fplugin-arg-nopper-numnops=<value>\n"
            "Where value is the number of nops to randomly insert.",
};


/* How we test to ensure the gcc version will work with our plugin */
static struct plugin_gcc_version nopper_ver =
{
    .basever = "9",
};


/* Insert a nop instruction before this statement */
static void insert_nop(gimple_stmt_iterator gsi)
{
    gimple *nop;
    nop = gimple_build_asm_vec("mov %%eax, %%eax", NULL, NULL, NULL, NULL);
    gsi_insert_before(&gsi, nop, GSI_NEW_STMT);
}


/* Returns true if this function has been ignored */
static bool ignore_fn(tree decl)
{
    tree fn;
    unsigned ii;

    FOR_EACH_VEC_ELT(ignorez, ii, fn)
      if (fn == decl)
          return true;

    return false;
}


/* Count the number of stmts in this program */
static int count_stmts(void)
{
    int n_stmts;
    basic_block bb;
    gimple_stmt_iterator gsi;
    struct cgraph_node *node;
    struct function *func;

    n_stmts = 0;

    /* For each call graph node, for each function, for each bb in func, for
     * each stmt in bb
     */
    FOR_EACH_FUNCTION(node)
    {
        symtab_node *n = node;

        if (ignore_fn(n->decl))
          continue;

        if (!(func = DECL_STRUCT_FUNCTION(n->decl)))
          continue;

        FOR_EACH_BB_FN(bb, func)
          for (gsi=gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
            ++n_stmts;
    }

    return n_stmts;
}


/* This is the plugin callback that gets triggered based on data specified in
 * the pass struct defined below.
 * Returns 0 on success, error otherwise
 */
static int n_nops; /* Global value for the number of nops to insert */
static unsigned int nopper_exec(function *fun)
{
    int i;
    basic_block bb;
    gimple_stmt_iterator gsi;
    static int nops_per_stmt = 0;
    static int counted_stmts = 0;

    /* Only initialized once */
    if (!counted_stmts)
    {
        if (!(counted_stmts = count_stmts()))
          return -EINVAL;

        if (n_nops <= 0)
          n_nops = counted_stmts * 5;

        nops_per_stmt = n_nops / counted_stmts;

        printf("[nopper] Inserting %d nops between %d statements\n",
               n_nops, counted_stmts);
    }

    if (ignore_fn(current_function_decl)) 
      return 0;;

    /* Get nopping! */
    FOR_EACH_BB_FN(bb, fun) 
      for (gsi=gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi))
        for (i=0; i<nops_per_stmt; ++i)
          insert_nop(gsi);
    
    return 0;
}


static tree handle_ignore_attr(
    tree *node,
    tree  name,
    tree  args,
    int   flags, 
    bool *no_add_attrs)
{
    ignorez.safe_push(*node);
    return NULL_TREE;
}


/* Attribute __nopper-ignore__ only for functions */
static const struct attribute_spec ignore_attr = 
{
    "nopper",
     0, 0, 
     true, false, false, false,
     handle_ignore_attr,
     NULL
};


static void nopper_register_attrs(void *event_data, void *data)
{
    register_attribute(&ignore_attr);
}


namespace{
const pass_data pass_data_nopper =
{
    .type = GIMPLE_PASS, /* Type           */
    .name = "nopper",    /* Name           */
    .optinfo_flags = OPTGROUP_NONE,           /* opt-info flags */
    .tv_id = TV_NONE,     /* Time var id    */
    .properties_required = 0,           /* Prop. required */
    .properties_provided = 0,           /* Prop. provided */
    .properties_destroyed = 0,           /* Prop destroyed */
    .todo_flags_start = 0,           /* Flags start    */
    .todo_flags_finish = 0            /* Flags finish   */
};


class pass_nopper : public gimple_opt_pass
{
public:
    pass_nopper() : gimple_opt_pass(pass_data_nopper, NULL) {;}
    virtual unsigned int execute(function *fun) { return nopper_exec(fun); }
};
} /* Anonymous namespace */


/* Return 0 on success or error code on failure */
int plugin_init(struct plugin_name_args   *info,  /* Argument info  */
                struct plugin_gcc_version *ver)   /* Version of GCC */
{
    int i;

    /* Used to tell the plugin-framework about where we want to be called in the
     * set of all passes.  This is located in tree-pass.h
     */
    struct register_pass_info pass;

    /* We could call: plugin_default_version_check() to validate our plugin, but
     * we will skip that.  Instead, as mentioned it can be more useful if we
     * validate the version information ourselves
     */
     if (strncmp(ver->basever, nopper_ver.basever, strlen(nopper_ver.basever)))
       return -1; /* Incorrect version of gcc */

    /* Setup the info to register with gcc telling when we want to be called and
     * to what gcc should call, when it's time to be called.
     */
    pass.pass = new pass_nopper();

    /* Get called after gcc has produced the SSA representation of the program.
     * After the first SSA pass.
     */
    pass.reference_pass_name = "ssa";
    pass.ref_pass_instance_number = 1;
    pass.pos_op = PASS_POS_INSERT_AFTER;

    /* Register our attribute */
    register_callback("nopper", PLUGIN_ATTRIBUTES, nopper_register_attrs, NULL);

    /* Tell gcc we want to be called after the first SSA pass */
    register_callback("nopper", PLUGIN_PASS_MANAGER_SETUP, NULL, &pass);

    /* Tell gcc some information about us... just for use in invoking gcc with:
     * "-v --help --version
     */
    register_callback("nopper", PLUGIN_INFO, NULL, &nopper_info);

    /* Let's do some arg parsing (-fplugin-arg-nopper-numnops=xxx) */
    for (i=0; i<info->argc; ++i)
      if (strncmp("numnops", info->argv[i].key, 6) == 0)
        n_nops = atoi(info->argv[i].value);

    /* Successful initialization */ 
    return 0;
}
