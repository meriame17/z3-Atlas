#ifndef _THEORY_ATLAS_H_
#define _THEORY_ATLAS_H_

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
//#include "smt/theory_atlas/pf_automaton.h"
//#include "smt/theory_str/pf_automaton_def.h"

#define PRINT_CHAR_MIN 65
#define PRINT_CHAR_MAX 122

namespace smt
{

    class theory_atlas : public theory
    {

        int m_scope_level = 0;
        static bool is_over_approximation;
        static bool is_under_approximation;
        static bool str_solver_checked;
        static bool assignement_dumped;
        static bool is_undeapp_over;
        

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
        unsigned p_bound = unsigned(3);
        unsigned q_bound = unsigned(1);
        unsigned cut_size = unsigned(1);
        unsigned scope;
        unsigned p_r;
        unsigned p_l;
       
        sort *int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);



        std::set<std::pair<int, int>> axiomatized_eq_vars;
        using expr_pair = std::pair<expr_ref, expr_ref>;
        using tvar_pair = std::pair<theory_var, theory_var>;

        //PFA for variables ;
        //typedef automaton<expr, ast_manager> pautomaton;
       // typedef pf_automaton<expr, ast_manager> pf_automaton_t;
       // scoped_ptr<pf_automaton_t> m_pfa;

        scoped_vector<tvar_pair> m_word_eq_var_todo;
       //scoped_vector<expr*> vars;
        scoped_vector<app*> m_int_eq_todo;

        scoped_vector<tvar_pair> m_word_diseq_var_todo;
        scoped_vector<expr_ref> int_vars;
        scoped_vector<expr_ref> pp_vars;

        scoped_vector<expr_pair> m_word_eq_todo;
        scoped_vector<expr_pair> m_word_eq_todo2;
        std::vector<expr_ref> cst_vars;

        scoped_vector<expr_pair> m_word_diseq_todo;
        scoped_vector<expr_pair> m_not_contains_todo;
        scoped_vector<expr_pair> m_membership_todo;
        //scoped_vector<expr*> formula; 
        expr_ref_vector axioms;
        unsigned flag=0;
        
        unsigned flag1=0;
        obj_map<expr, zstring> candidate_model;
        obj_map<expr, std::vector<std::pair<expr_ref, expr_ref>>> vars_map;
         std::vector <expr_ref> pk_vars;

       obj_map<expr,std::vector<std::pair<std::string, std::string>>> states_map;
       void   find_states(
        expr_ref elt, std::vector<std::pair<std::string, std::string>> *states);
       void find_vars( expr_ref elt, 
        std::vector<std::pair<expr_ref, expr_ref>> *vars);
       std::map <std::string, expr_ref> st_map;
       std::vector<std::pair<expr_ref, expr_ref>> phi_sharp;
        obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> fresh_int_vars;
        obj_map<expr,std::string> model;
       // std::vector<std::pair<expr*,std::string >> model;
        unsigned vars_count;

    public:
    

        theory_atlas(context& c, ast_manager & m, theory_str_params const & params);
        ~theory_atlas() override;
        typedef automaton<expr, ast_manager> pautomaton;

        char const *get_name() const override { return "atlas"; }
        void display(std::ostream &os) const override;
        theory *mk_fresh(context *c) override { return alloc(theory_atlas, *c, c->get_manager(), m_params); }
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
        void handle_word_eq(expr* lhs, expr* rhs);
        void handle_word_diseq(expr_ref lhs, expr_ref rhs);
        ptr_vector<expr> get_int_vars_from_aut(pautomaton *aut, unsigned s);
        app* construct_basic_str_ctr( ast_manager& m,std::vector<std::pair<expr_ref, expr_ref>> vars, 
        unsigned l_bound,
         unsigned s_bound,
         std::vector<std::pair<std::string, std::string>> states);
       // app* construct_basic_str_ctr( ast_manager& m,std::vector<std::pair<expr_ref, expr_ref>> vars, unsigned l_bound, unsigned s_bound);
        std::vector<std::pair<expr_ref,expr_ref>>  init_int_vars(unsigned p, std::string s,
        std::vector<std::pair<std::string, std::string>> *states);
        std::vector<std::pair<expr_ref,expr_ref>>  init_int_vars2(expr_ref e, unsigned p, std::string s,
        std::vector<std::pair<std::string, std::string>> *states);
        std::vector<std::pair<expr_ref,expr_ref>>  mk_fresh_vars(expr_ref str_v, std::string s);
        void print_model(context &local_ctx) ;
        std::vector<int> get_segment_vector();
        app *mk_fresh_const(std::string name, sort *s, unsigned k, unsigned l);
        app *mk_fresh_const(std::string name, sort *s, unsigned k);
        app *mk_fresh_const(std::string name, sort *s);
        void mk_product(
        std::vector<std::pair<expr_ref, expr_ref>> lhs, 
        std::vector<std::pair<expr_ref, expr_ref>> rhs ,
        std::vector<std::pair<std::string, std::string>> states_l,
        std::vector<std::pair<std::string, std::string>> states_r);
        expr_ref get_in_state_index(expr_ref elt,
            std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>>  prod_vars,
           std::vector< std::pair<std::string, std::string>>  p_states);
        expr_ref get_state_index(std::string elt);
       
        void parikh_img(ast_manager& m, 
                std::vector< std::pair<std::string, std::string>> states,
                std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>> prod_vars,
                 std::vector<std::string> reachable2, 
                std::string final_s );
        app * mk_value_helper(app * n) ;
        expr * mk_string(zstring const& str);
        expr * get_eqc_value(expr * n, bool & hasEqcValue);
        expr * z3str2_get_eqc_value(expr * n , bool & hasEqcValue) ;
        theory_var get_var(expr * n) const;
        void  word_eq_over_approx(expr* lhs,expr* rhs);
        expr*query_theory_arith_core(expr* n, model_generator& mg);
         void add_int_axiom(expr *const e);
        app * mk_strlen(expr * e);
        bool get_arith_value(expr* e, rational& val) const;
        app*  construct_string_from_int_array(std::vector<std::pair<expr_ref, expr_ref>> int_varr,model_generator &mg);
        void print_assignement();
        std::vector<std::pair<expr_ref, expr_ref>> mk_newvar(zstring s,std::vector<std::pair<std::string, std::string>> *states);
        std::vector<std::pair<expr_ref, expr_ref>> mk_newvar2(expr_ref elt,zstring s,std::vector<std::pair<std::string, std::string>> *states);

        final_check_status final_check_eh() override;
        model_value_proc *mk_value(enode *n, model_generator &mg) override;
        void init_model(model_generator &m) override;
        void finalize_model(model_generator &mg) override;
        lbool validate_unsat_core(expr_ref_vector &unsat_core) override;

        void add_length_axiom(expr *n);
        void find(obj_map<expr_ref,std::vector<std::pair<std::string, std::string>>> states_map,
                expr_ref elt,
                  std::vector<std::pair<std::string, std::string>> states);
         bool  find(obj_map <std::string, expr_ref> st_ma,
                        std::string s,
                        expr_ref e);
        bool contains_elt(app* elt, obj_map <expr_ref, expr_ref> vec);
        void print_terms(const expr_ref_vector& terms);
        std::string expr2str(expr* node);
        bool contains(std::string elt, std::vector<std::string> vec) ;
        int contains_elt(expr_ref elt, std::vector<std::pair<expr_ref, expr_ref>>vec);
        bool contains_elt(app *elt, scoped_vector<app *> vec);
        bool contains_elt(expr_ref elt, scoped_vector<expr_ref> vec);
        bool contains_elt(expr_pair elt, scoped_vector<expr_pair> vec);
        bool contains_elt(expr* elt, scoped_vector<expr*> vec) ;
        bool contains_elt(app* elt, std::vector<app*> vec) ;
        bool contains_elt(expr_ref elt, std::vector<expr_ref> vec) ;
        bool contains_elt(std::string elt,
            obj_map <std::string, expr_ref> st_map);
        bool contains_elt(std::string elt, std::vector<std::string> vec) ;
        bool contains_elt(expr_ref elt, obj_map <expr_ref, expr_ref> vec) ;
        bool contains_elt(expr* elt, obj_map<expr*, 
        std::vector<std::pair<expr_ref, expr_ref>>> vec);
        bool contains_elt(app* elt, obj_map<expr_ref, std::vector<std::pair<expr_ref, expr_ref>>> vec);

        bool contains_elt(expr* elt,
          obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> vec,
          std::vector<std::pair<expr_ref, expr_ref>> *vars);
        bool contains_elt(std::pair<std::string, std::string>pr,
         std::vector<std::pair<std::string, std::string>> vec) ;

        void word_eq_under_approx(expr* lhs, expr* rhs, expr_ref_vector &items);
        void get_nodes_in_concat(expr *node, ptr_vector<expr> &nodeList);
        /**
          * 
          * 
          * */
        //void handle_word_eq(expr * lhs, expr * rhs);

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
        void add_axiom_arith(expr *const e);
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
        std::vector<expr* > get_vars(expr* e) const;
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

#endif /* _THEORY_ATLAS_H_ */