/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    z3str3_tactic.cpp

Abstract:

    Tactic for string instances that synergizes with Z3str3

Author:

    Murphy Berzish (mtrberzi) 2019-01-10

Update:

    Federico Mora (FedericoAureliano) 2019-07-21

Notes:

--*/
#include "util/params.h"
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/str/ext_str_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "smt/params/smt_params.h"
#include "ast/ast_pp.h"
#include "tactic/core/ctx_simplify_tactic.h"


/*
// conjunctive fragment := cf
static bool is_cf_helper(ast_manager &m, expr * f, bool sign) 
{
    seq_util u(m);

    while (m.is_not(f, f))
    {
        TRACE("str_fl", tout << "negation " << mk_pp(f, m) << std::endl;);
        sign = !sign;
    }

    if (m.is_eq(f) && !sign && to_app(f)->get_arg(0)->get_sort()->get_family_id() == u.get_family_id())
    {
        TRACE("str_fl", tout << "Not conjunctive fragment! " << mk_pp(f, m) << std::endl;);
        return false;
    }
    else if ((u.str.is_prefix(f) || u.str.is_suffix(f)) && !sign)
    {
        TRACE("str_fl", tout << "Not conjunctive fragment! " << mk_pp(f, m) << std::endl;);
        return false;
    }
    else if (u.str.is_contains(f) || u.str.is_in_re(f) || u.str.is_replace(f) || u.str.is_index(f))
    {
        TRACE("str_fl", tout << "Not conjunctive fragment! " << mk_pp(f, m) << std::endl;);
        return false;
    }
    else {
        TRACE("str_fl", tout << "other " << mk_pp(f, m) << std::endl;);
        if (!is_app(f)) {
            return false;
        }
        for (unsigned int i = 0; i < to_app(f)->get_num_args(); i++)
        {
            if (!is_cf_helper(m, to_app(f)->get_arg(i), sign)) {
                return false;
            }
        }
        TRACE("str_fl", tout << "conjunctive" << std::endl;);
        return true;
    }
}

static bool is_cf(goal const &g)
{
    ast_manager &m = g.m();
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++)
    {
        expr *f = g.form(i);
        if (!is_cf_helper(m, f, true)){
            return false;
        }
    }
    TRACE("str_fl", tout << "Conjunctive fragment!" << std::endl;);
    // std::cout << "LAS:" << std::endl;
    return true;
}

class is_cf_probe : public probe {
public:
    result operator()(goal const & g) override {
        return is_cf(g);
    }
};

probe * mk_is_cf_probe() {
    return alloc(is_cf_probe);
}


static bool has_word_eq_helper(ast_manager &m, expr * f)
{
    seq_util u(m);

    if (m.is_eq(f) && to_app(f)->get_arg(0)->get_sort()->get_family_id() == u.get_family_id())
    {
        TRACE("str_fl", tout << "Found a word equation! " << mk_pp(f, m) << std::endl;);
        return true;
    }
    else {
        TRACE("str_fl", tout << "other " << mk_pp(f, m) << std::endl;);
        if (!is_app(f)) {
            return false;
        }
        for (unsigned int i = 0; i < to_app(f)->get_num_args(); i++)
        {
            if (has_word_eq_helper(m, to_app(f)->get_arg(i))) {
                return true;
            }
        }
        TRACE("str_fl", tout << "No word equation found! " << std::endl;);
        return false;
    }
}

static bool has_word_eq(goal const &g)
{
    unsigned n_word_equations = 0;
    unsigned n_non_word_equations = 0;
    ast_manager &m = g.m();
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++)
    {
        expr *f = g.form(i);
        if (has_word_eq_helper(m, f)){
            n_word_equations++;
        } else {
            n_non_word_equations++;
        }
    }
    TRACE("str_fl", tout << "Total formulas: " << sz << " Word equations: " << n_word_equations << " Non-word equations: " << n_non_word_equations << std::endl;);
    if (sz <= 5) {
        return (n_word_equations > 0);
    } else {
        return (n_word_equations > n_non_word_equations);
    }
}

class has_word_eq_probe : public probe {
public:
    result operator()(goal const & g) override {
        return has_word_eq(g);
    }
};

probe * mk_has_word_eq_probe() {
    return alloc(has_word_eq_probe);
}

static bool has_regex_helper(ast_manager &m, expr * f)
{
    seq_util u(m);

    if (u.str.is_in_re(f))
    {
        TRACE("str_fl", tout << "Found a regex! " << mk_pp(f, m) << std::endl;);
        return true;
    }
    else {
        TRACE("str_fl", tout << "other " << mk_pp(f, m) << std::endl;);
        if (!is_app(f)) {
            return false;
        }
        for (unsigned int i = 0; i < to_app(f)->get_num_args(); i++)
        {
            if (has_regex_helper(m, to_app(f)->get_arg(i))) {
                return true;
            }
        }
        TRACE("str_fl", tout << "No regex found! " << std::endl;);
        return false;
    }
}

static bool has_regex(goal const &g)
{
    ast_manager &m = g.m();
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++)
    {
        expr *f = g.form(i);
        if (has_regex_helper(m, f)){
            return true;
        }
    }
    TRACE("str_fl", tout << "Does not have regular expressions!" << std::endl;);
    return false;
}

class has_regex_probe : public probe {
public:
    result operator()(goal const & g) override {
        return has_regex(g);
    }
};

probe * mk_has_regex_probe() {
    return alloc(has_regex_probe);
}
*/
tactic * mk_rewriter_tactic(ast_manager & m, params_ref const & p) {
    smt_params m_smt_params;
    m_smt_params.updt_params(p);
   return and_then(mk_simplify_tactic(m, p), and_then(mk_ctx_simplify_tactic(m, p), and_then(mk_ext_str_tactic(m, p), mk_simplify_tactic(m, p))));
}

tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p) {
    smt_params m_smt_params;
    m_smt_params.updt_params(p);
    params_ref seq_p = p;
    seq_p.set_sym("string_solver", symbol("seq"));
    //seq_p.set_bool("tactic_model_validation", true);
    tactic * z3seq = using_params(mk_smt_tactic(m), seq_p);

    return using_params(and_then(mk_rewriter_tactic(m, p), z3seq), p);
    //return using_params(mk_smt_tactic(m), seq_p);

}

/*
tactic * mk_z3str3_tactic(ast_manager & m, params_ref const & p) {
    smt_params m_smt_params;
    m_smt_params.updt_params(p);
    TRACE("str", tout << "using Z3str3 portfolio tactic " << m_smt_params.m_StrTactic << std::endl;);

    params_ref preprocess_p = p;
    preprocess_p.set_bool("str.fixed_length_preprocessing", true);
    preprocess_p.set_bool("str.fixed_length_models", true);
    preprocess_p.set_bool("str.multiset_check", true);
    preprocess_p.set_bool("str.search_overlaps", false);
    preprocess_p.set_uint("str.regex_automata_length_attempt_threshold", 3);
    preprocess_p.set_uint("str.regex_automata_failed_automaton_threshold", 3);
    preprocess_p.set_uint("str.regex_automata_failed_intersection_threshold", 1);
    preprocess_p.set_sym("string_solver", symbol("z3str3"));

    params_ref general_p = p;
    general_p.set_bool("str.fixed_length_preprocessing", false);
    general_p.set_bool("str.fixed_length_models", true);
    general_p.set_bool("str.multiset_check", false);
    general_p.set_sym("string_solver", symbol("z3str3"));
    general_p.set_bool("str.search_overlaps", false);

    params_ref seq_p = p;
    seq_p.set_sym("string_solver", symbol("seq"));
    seq_p.set_bool("tactic_model_validation", true);

    params_ref search_overlaps_p = p;
    search_overlaps_p.set_bool("str.fixed_length_preprocessing", false);
    search_overlaps_p.set_bool("str.fixed_length_models", true);
    search_overlaps_p.set_bool("str.multiset_check", false);
    search_overlaps_p.set_sym("string_solver", symbol("z3str3"));
    search_overlaps_p.set_bool("str.search_overlaps", true);

    tactic * z3str3_2 = using_params(mk_smt_tactic(m), general_p);

    // introduce search_overlaps arm which is always used immediately after z3str3 fails
    if (m_smt_params.m_SearchOverlaps) {
        z3str3_2 = or_else(z3str3_2, using_params(try_for(mk_smt_tactic(m), m_smt_params.m_SearchOverlapsMilliseconds), search_overlaps_p));
    }

    tactic * z3str3_1 = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), preprocess_p);
    tactic * z3seq = nullptr;
    
    if (m_smt_params.m_StrTactic == symbol("all")) {
        // apply all tactics in the portfolio
        z3seq       = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), cond(mk_is_cf_probe(), or_else(z3str3_1, z3str3_2, z3seq), or_else(z3seq, z3str3_2, z3str3_1))), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("alwayscf")) {
        // test the case where the CF probe always returns "true"
        seq_p.set_uint("seq.giveup_point", 0);
        z3seq = using_params(mk_smt_tactic(m), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), or_else(z3str3_1, z3str3_2, z3seq)), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("nevercf")) {
        // test the case where the CF probe always returns "false"
        seq_p.set_uint("seq.giveup_point", 7);
        z3seq       = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), or_else(z3seq, z3str3_2, z3str3_1)), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("las")) {
        // fixed-length solver only
        TRACE("str", tout << "z3str3 tactic bypassed: performing length abstraction / fixed-length solving" << std::endl;);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), z3str3_1), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("arr")) {
        // arrangement solver only
        TRACE("str", tout << "z3str3 tactic bypassed: performing arrangement solving" << std::endl;);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), z3str3_2), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("seq")) {
        // sequence solver only
        TRACE("str", tout << "z3str3 tactic bypassed: using sequence solver" << std::endl;);
        z3seq = using_params(mk_smt_tactic(m), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), z3seq), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("z3str4")) {
        // Dynamic Algorithm Selection
        seq_p.set_uint("seq.giveup_point", 7);
        tactic * z3seqBefore = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        seq_p.set_uint("seq.giveup_point", 0);
        tactic * z3seqAfter = using_params(mk_smt_tactic(m), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), cond(mk_is_cf_probe(), or_else(z3str3_1, z3str3_2, z3seqAfter), or_else(z3seqBefore, z3str3_2, z3str3_1))), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("regex")) {
        seq_p.set_uint("seq.giveup_point", 7);
        tactic * z3seqBefore = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), or_else(z3seqBefore, z3str3_2)), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("ml")) {
        // machine-learning arm selection
        z3seq = using_params(mk_smt_tactic(m), seq_p);
        tactic * ml = mk_str_ml_tactic(m, p, z3str3_1, z3str3_2, z3seq);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), ml), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("cheese")) {
        tactic * cheese = mk_string_cheese_tactic(m, p);
        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), cheese), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("2probe")) {
        seq_p.set_uint("seq.giveup_point", 7);
        tactic * z3seqBefore = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        seq_p.set_uint("seq.giveup_point", 0);
        tactic * z3seqAfter = using_params(mk_smt_tactic(m), seq_p);

        tactic * tree =
            cond(mk_has_word_eq_probe(),
                cond(mk_is_cf_probe(),
                     or_else(z3str3_1, z3str3_2, z3seqAfter),
                     or_else(z3seqBefore, z3str3_2, z3str3_1)),
                z3seqAfter);

        tactic * st = using_params(and_then(mk_rewriter_tactic(m, p), tree), p);
        return st;
    } else if (m_smt_params.m_StrTactic == symbol("3probe")) {
        // don't apply ext_str_tactic before the regex probe, as it may introduce regexes

        seq_p.set_uint("seq.giveup_point", 7);
        tactic * z3seqBefore = using_params(try_for(mk_smt_tactic(m), m_smt_params.m_PreMilliseconds), seq_p);
        seq_p.set_uint("seq.giveup_point", 0);
        tactic * z3seqAfter = using_params(mk_smt_tactic(m), seq_p);

        tactic * innertree =
            cond(mk_has_word_eq_probe(),
                cond(mk_is_cf_probe(),
                     or_else(z3str3_1, z3str3_2, z3seqAfter),
                     or_else(z3seqBefore, z3str3_2, z3str3_1)),
                z3seqAfter);

        tactic * regextrue = or_else(z3seqBefore, z3str3_2);
        tactic * regexfalse = innertree;
        if (m_smt_params.m_RewriterTactic) {
            regextrue = and_then(mk_ext_str_tactic(m, p), regextrue);
            regexfalse = and_then(mk_ext_str_tactic(m, p), regexfalse);
        }

        tactic * tree = cond(mk_has_regex_probe(), regextrue, regexfalse);

        tactic * st = using_params(and_then(mk_simplify_tactic(m, p), tree), p);
        
        return st;
    } else {
        // unknown tactic
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }

}*/

