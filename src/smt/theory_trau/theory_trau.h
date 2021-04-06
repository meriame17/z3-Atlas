#ifndef _THEORY_TRAU_H_
#define _THEORY_TRAU_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <smt/params/smt_params.h>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
//#include "smt/theory_trau/pf_automaton.h"
//#include "smt/theory_str/pf_automaton_def.h"

#define PRINT_CHAR_MIN 1
#define PRINT_CHAR_MAX 2

namespace smt
{

    class theory_trau : public theory
    {

        int m_scope_level = 0;
        static bool is_over_approximation;
        const theory_str_params &m_params;
        th_rewriter m_rewrite;
        arith_util m_util_a;
        seq_util m_util_s;
        //decl_plugin apl;

        ast_manager &m;

        obj_hashtable<expr> axiomatized_terms;
        obj_hashtable<expr> propgated_string_theory;
        obj_hashtable<expr> m_has_length; // is length applied
        expr_ref_vector m_length;         // length applications themselves
        unsigned m_fresh_id;
        unsigned p_bound = unsigned(2);
        unsigned q_bound = unsigned(5);
        unsigned p_r;
        unsigned p_l;


        std::set<std::pair<int, int>> axiomatized_eq_vars;
        using expr_pair = std::pair<expr_ref, expr_ref>;
        using tvar_pair = std::pair<theory_var, theory_var>;

        //PFA for variables ;
        //typedef automaton<expr, ast_manager> pautomaton;
       // typedef pf_automaton<expr, ast_manager> pf_automaton_t;
       // scoped_ptr<pf_automaton_t> m_pfa;

        scoped_vector<tvar_pair> m_word_eq_var_todo;
        scoped_vector<app *> m_int_eq_todo;

        scoped_vector<tvar_pair> m_word_diseq_var_todo;

        scoped_vector<expr_pair> m_word_eq_todo;
        scoped_vector<expr_pair> m_word_diseq_todo;
        scoped_vector<expr_pair> m_not_contains_todo;
        scoped_vector<expr_pair> m_membership_todo;

    public:

        theory_trau(context& c, ast_manager & m, theory_str_params const & params);
        ~theory_trau() override;
        typedef automaton<expr, ast_manager> pautomaton;

        char const *get_name() const override { return "trau"; }
        void display(std::ostream &os) const override;
        theory *mk_fresh(context *c) override { return alloc(theory_trau, *c, c->get_manager(), m_params); }
        void init() override;
        theory_var mk_var(enode *n) override;
        void apply_sort_cnstr(enode *n, sort *s) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        void handle_word_eq(expr_ref lhs, expr_ref rhs);
        void handle_word_diseq(expr_ref lhs, expr_ref rhs);
        ptr_vector<expr> get_int_vars_from_aut(pautomaton *aut, unsigned s);
        app* construct_basic_str_ctr( ast_manager& m,std::vector<std::pair<expr_ref, expr_ref>> vars, unsigned l_bound, unsigned s_bound);
        std::vector<std::pair<expr_ref,expr_ref>>  init_int_vars(unsigned p,unsigned q, std::string s);
        app *mk_fresh_const(char const *name, sort *s);
     
        final_check_status final_check_eh() override;
        model_value_proc *mk_value(enode *n, model_generator &mg) override;
        void init_model(model_generator &m) override;
        void finalize_model(model_generator &mg) override;
        lbool validate_unsat_core(expr_ref_vector &unsat_core) override;

        void add_length_axiom(expr *n);
        bool contains_elt(app *elt, scoped_vector<app *> vec);
        void word_eq_under_approx(expr *lhs, expr *rhs, expr_ref_vector &items);
        void get_nodes_in_concat(expr *node, ptr_vector<expr> &nodeList);
        /**
          * 
          * 
          * */
        //void theory_trau::handle_word_eq(expr * lhs, expr * rhs);

        /**
          * 
          * 
          * */

        expr_ref mk_str_var(symbol const &);
        enode *ensure_enode(expr *a);
        expr_ref mk_skolem(symbol const &s, expr *e1, expr *e2 = nullptr, expr *e3 = nullptr,
                           expr *e4 = nullptr, sort *sort = nullptr);
        expr_ref mk_len(expr *s) const { return expr_ref(m_util_s.str.mk_length(s), m); }

        void add_axiom(expr *e);
        literal mk_eq_empty(expr *n, bool phase = true);
        expr_ref mk_last(expr *e);
        expr_ref mk_first(expr *e);
        expr_ref mk_concat(expr *e1, expr *e2);

        bool has_length(expr *e) const { return m_has_length.contains(e); }
        void add_length(expr *e);
        void enforce_length(expr *n);

    private:
        bool is_of_this_theory(expr *e) const;
        bool is_string_sort(expr *e) const;
        bool is_regex_sort(expr *e) const;
        bool is_const_fun(expr *e) const;
        expr_ref mk_sub(expr *a, expr *b);
        zstring print_word_term(expr *a) const;
        zstring print_vars(expr *a) const;
        std::vector<expr *> get_vars(expr *e) const;
        // expr* get_vars(expr * e);
        expr *get_vars(expr *e, ptr_vector<expr> lst) const;

        literal mk_literal(expr *e);
        bool_var mk_bool_var(expr *e);
        void add_axiom(std::initializer_list<literal> ls);
        void handle_char_at(expr *e);
        void handle_substr(expr *e);
        void handle_index_of(expr *e);
        void handle_replace(expr *e);
        void handle_prefix(expr *e);
        void handle_suffix(expr *e);
        void handle_not_prefix(expr *e);
        void handle_not_suffix(expr *e);
        void handle_contains(expr *e);
        void handle_in_re(expr *e, bool is_true);
        void set_conflict(const literal_vector &ls);
        void block_curr_assignment();
        void dump_assignments() const;
        void string_theory_propagation(expr *ex);
        void propagate_concat_axiom(enode *cat);
        void propagate_basic_string_axioms(enode *str);
        void tightest_prefix(expr *, expr *);
        void print_ast(expr *e);
        void print_ctx(context &ctx);
    };
}

#endif /* _THEORY_trau_H_ */