/*++
Module Name:

    str_decl_plugin.h

Abstract:

    <abstract>

Author:

    Murphy Berzish (mtrberzi) 2015-09-02.

Revision History:

--*/
#include<sstream>
#include"str_decl_plugin.h"
#include"string_buffer.h"
#include"warning.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"

str_decl_plugin::str_decl_plugin():
    m_strv_sym("String"),
    m_str_decl(0){
}

str_decl_plugin::~str_decl_plugin(){
}

void str_decl_plugin::finalize(void) {
    #define DEC_REF(decl) if (decl) { m_manager->dec_ref(decl); } ((void) 0)
    DEC_REF(m_str_decl);
}

void str_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_str_decl = m->mk_sort(symbol("String"), sort_info(id, STRING_SORT));
    m->inc_ref(m_str_decl);
    sort * s = m_str_decl;
    /* TODO mk_pred, etc. */
}

decl_plugin * str_decl_plugin::mk_fresh() {
    return alloc(str_decl_plugin);
}

sort * str_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    switch (k) {
    case STRING_SORT: return m_str_decl;
    default: return 0;
    }
}

func_decl * str_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                         unsigned arity, sort * const * domain, sort * range) {
    /* TODO */
    m_manager->raise_exception("str_decl_plugin::mk_func_decl() not yet implemented"); return 0;
}

app * str_decl_plugin::mk_string(const char * val) {
    parameter p[1] = {parameter(val)};
    func_decl * d;
    d = m_manager->mk_const_decl(m_strv_sym, m_str_decl, func_decl_info(m_family_id, OP_STR, 1, p));
    return m_manager->mk_const(d);
}

void str_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    // TODO
    // we would do something like:
    // op_names.push_back(builtin_name("<=",OP_LE));
}

void str_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("String", STRING_SORT));
}

bool str_recognizers::is_string(expr const * n, const char ** val) const {
    if (!is_app_of(n, m_afid, OP_STR))
            return false;
    func_decl * decl = to_app(n)->get_decl();
    *val    = decl->get_parameter(0).get_string();
    return true;
}

bool str_recognizers::is_string(expr const * n) const {
    const char * tmp = 0;
    return is_string(n, & tmp);
}

str_util::str_util(ast_manager &m) :
    str_recognizers(m.mk_family_id(symbol("str"))),
    m_manager(m) {
    SASSERT(m.has_plugin(symbol("str")));
    m_plugin = static_cast<str_decl_plugin*>(m.get_plugin(m.mk_family_id(symbol("str"))));
}
