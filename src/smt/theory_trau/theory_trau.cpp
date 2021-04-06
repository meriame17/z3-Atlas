#include <algorithm>
#include <sstream>
#include "ast/ast_pp.h"
#include "smt/theory_trau/theory_trau.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt {
    bool theory_trau::is_over_approximation = false;

    namespace {
        bool IN_CHECK_FINAL = false;
    }

    theory_trau::theory_trau(context& ctx,ast_manager &m, const theory_str_params &params):
     theory(ctx, m.mk_family_id("seq")), 
     m_params{params}, 
     m_rewrite{m}, 
     m_util_a{m},
     m_util_s{m}, 
     m{m}, 
     m_length(m),
     m_fresh_id(0) {}
  theory_trau::~theory_trau(){

            }
    void theory_trau::display(std::ostream &os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_trau::init() {
        std::cout<< "INIT" <<"\n";
        theory::init();
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init\n";);
    }

    enode *theory_trau::ensure_enode(expr *e) {
        context &ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode *n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    theory_var theory_trau::mk_var(enode *const n) {
        if (!m_util_s.is_seq(n->get_owner()) &&
            !m_util_s.is_re(n->get_owner())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }


    bool theory_trau::internalize_atom(app *const atom, const bool gate_ctx) {

        (void) gate_ctx;
        std::cout<< "i am inside internalize atom" <<std::endl;
        STRACE("str", tout << "internalize_atom: gate_ctx is " << gate_ctx << ", "
                           << mk_pp(atom, get_manager()) << '\n';);
        context &ctx = get_context();
        if (ctx.b_internalized(atom)) {
            STRACE("str", tout << "done before\n";);
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_trau::internalize_term(app *const term) {
        context &ctx = get_context();
    

        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        for (auto arg : *term) {
            mk_var(ensure_enode(arg));
        }
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            ctx.mark_as_relevant(bv);
        }

        enode *e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        mk_var(e);
        if (!ctx.relevancy()) {
            relevant_eh(term);
        }
        return true;
    }

    void theory_trau::apply_sort_cnstr(enode *n, sort *s) {
        mk_var(n);
    }

    void theory_trau::print_ctx(context &ctx) {  // test_hlin
        std::cout << "~~~~~ print ctx start ~~~~~~~\n";
//        context& ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        expr_ref_vector Literals(get_manager()), Assigns(get_manager());
        ctx.get_guessed_literals(Literals);
        ctx.get_assignments(Assigns);
        std::cout << "~~~~~~ from get_asserted_formulas ~~~~~~\n";
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            std::cout << mk_pp(ex, get_manager()) << " relevant? " << ctx.is_relevant(ex) << std::endl;
        }
        std::cout << "~~~~~~ from get_guessed_literals ~~~~~~\n";
        for (auto &e : Literals) {
            std::cout << mk_pp(e, get_manager()) << " relevant? " << ctx.is_relevant(e) << std::endl;
        }
        std::cout << "~~~~~~ from get_assignments ~~~~~~\n";
        for (auto &e : Assigns) {
//            print_ast(e);
            std::cout << mk_pp(e, get_manager()) << " relevant? " << ctx.is_relevant(e) << std::endl;
        }
        std::cout << "~~~~~ print ctx end ~~~~~~~~~\n";
    }

    void theory_trau::print_ast(expr *e) {  // test_hlin
        ast_manager m = get_manager();
        unsigned int id = e->get_id();
        ast_kind ast = e->get_kind();
        sort *e_sort = e->get_sort();
        sort *bool_sort = m.mk_bool_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();
        std::cout << "#e.id = " << id << std::endl;
        std::cout << "#e.kind = " << get_ast_kind_name(ast) << std::endl;
        std::cout << std::boolalpha << "#is bool sort? " << (e_sort == bool_sort) << std::endl;
        std::cout << std::boolalpha << "#is string sort? " << (e_sort == str_sort) << std::endl;
        std::cout << std::boolalpha << "#is string term? " << m_util_s.str.is_string(e) << std::endl;
        std::cout << std::boolalpha << "#is_numeral? " << m_util_a.is_numeral(e) << std::endl;
        std::cout << std::boolalpha << "#is_to_int? " << m_util_a.is_to_int(e) << std::endl;
        std::cout << std::boolalpha << "#is_int_expr? " << m_util_a.is_int_expr(e) << std::endl;
        std::cout << std::boolalpha << "#is_le? " << m_util_a.is_le(e) << std::endl;
        std::cout << std::boolalpha << "#is_ge? " << m_util_a.is_ge(e) << std::endl;
    }


    void theory_trau::init_search_eh() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            string_theory_propagation(ex);
            
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_trau::string_theory_propagation(expr *expr) {

        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        ast_manager &m = get_manager();
        context &ctx = get_context();

        if (!ctx.e_internalized(expr)) {
            ctx.internalize(expr, false);
        }
        enode *n = ctx.get_enode(expr);
        ctx.mark_as_relevant(n);

        sort *expr_sort = expr->get_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();
      
        if (expr_sort == str_sort) {
        

            enode *n = ctx.get_enode(expr);
            propagate_basic_string_axioms(n);
            if (is_app(expr) && m_util_s.str.is_concat(to_app(expr))) {
                propagate_concat_axiom(n);
            }
        }
        // if expr is an application, recursively inspect all arguments
        if (is_app(expr) && !m_util_s.str.is_length(expr)) {
            app *term = to_app(expr);
            unsigned num_args = term->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                string_theory_propagation(term->get_arg(i));
            }
        }
            
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_trau::handle_word_eq(expr_ref lhs, expr_ref rhs){


        ast_manager & m = get_manager();
        context & ctx = get_context();
        sort * lhs_sort = lhs->get_sort();
        sort * rhs_sort = rhs->get_sort();
        sort * str_sort = m_util_s.str.mk_string_sort();

        if (lhs_sort != str_sort || rhs_sort != str_sort) {
            TRACE("str", tout << "skip equality: not String sort" << std::endl;);
            return;
        }
        if(is_over_approximation){
            //OVER APPROX
            expr_ref len_lhs(m);
            len_lhs = m_util_s.str.mk_length(lhs);
            expr_ref len_rhs(m);
            //len_rhs = m_util_a.mk_numeral(rational(0), true);
            len_rhs=m_util_s.str.mk_length(lhs);
            app* lhs_eq_rhs = m_util_a.mk_eq(len_lhs, len_rhs);
            SASSERT(lhs_eq_rhs);
            add_axiom(lhs_eq_rhs);
            if (! contains_elt(lhs_eq_rhs,m_int_eq_todo))
                {m_int_eq_todo.push_back(lhs_eq_rhs);}

        }else{
             std:: cout << "over app over"<<"\n";
            expr_ref_vector new_int_const(m);
            word_eq_under_approx(lhs,rhs, new_int_const);
        }


    }
     void theory_trau::word_eq_under_approx(expr* lhs, expr* rhs, expr_ref_vector & items){

        /*TODO: 
                -get string vars
                -convert to sets of integer vars:
                    ->-> define p and q create flat automata 
                    -> concatenate lhs(resp. rhs) nodes automata
                    ->
                    
                -convert equalities
       */
      /*
      TEMPORARELY DISABLED: word equations with string constants

        ptr_vector<expr> lhs_nodes, rhs_nodes;
        zstring s;
        expr_ref_vector str_vars(m);
        get_nodes_in_concat(lhs,lhs_nodes);
        get_nodes_in_concat(rhs,rhs_nodes);

        for (const auto& v : lhs_nodes){
            if (is_app(v)) {
                app *ap = to_app(v);
                if (!m_util_s.str.is_concat(ap)) {
                    if (!str_vars.contains(v))
                        str_vars.push_back(v);
                }
                
            }
            
        }
        for (const auto& v : rhs_nodes){
            if (is_app(v)) {
                app *ap = to_app(v);
                if (!m_util_s.str.is_concat(ap)) {
                    if (!str_vars.contains(v))
                        str_vars.push_back(v);
                }
                
            }
            
        }

        */

        ast_manager &m = get_manager();
         
        context & ctx = get_context();
                 

        std::vector<expr*> lhs_vars=get_vars(lhs);
                 

        std::vector<expr*> rhs_vars=get_vars(rhs);
                 

       // pautomaton* pfa_left = m_pfa->create_flat(m,0,0);
        unsigned num_vars= p_bound*(q_bound+1)-1;
        sort *int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);
       
              


        obj_map<expr,std::pair<std::vector<expr_ref>,std::vector<expr_ref>>> fresh_int_vars_l;
        obj_map<expr,std::pair<std::vector<expr_ref>,std::vector<expr_ref>>> fresh_int_vars_r;

        std::vector<std::pair<expr_ref, expr_ref>> all_vars_r;
        std::vector<std::pair<expr_ref, expr_ref>> all_vars_l;

        std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>> product_vars;
        expr_ref eps(m);
        expr_ref eps_p(m);
        char const phi_i='i';
        char const phi_f='f';
        char const ph_p='p';

        expr_ref phi_pa_init (mk_fresh_const(&phi_i, int_sort), m); 
        expr_ref phi_pa_final (mk_fresh_const(&phi_f, int_sort), m); 
        expr_ref one(m_util_a.mk_int(0), m);


        app*  phi_left;
        for(auto const& ex: lhs_vars){
                     

            std::vector<std::pair<expr_ref, expr_ref>> fresh_vars_int=init_int_vars(num_vars,p_bound,"a");///mk_pp(ex, m));

            phi_left= construct_basic_str_ctr(m,fresh_vars_int, p_bound,q_bound);

            all_vars_l.insert(all_vars_l.end(),fresh_vars_int.begin(), fresh_vars_int.end() );


            p_l+=p_bound;

            
        }
         app*   phi_right;
         for(auto const& ex: rhs_vars){

            std::vector<std::pair<expr_ref, expr_ref>> fresh_vars_int=init_int_vars(num_vars,p_bound,"a");///mk_pp(ex, m));
            phi_right= construct_basic_str_ctr(m,fresh_vars_int, p_bound,q_bound);
            all_vars_r.insert(all_vars_r.end(),fresh_vars_int.begin(), fresh_vars_int.end());
            p_r+= p_bound;
            
        }


       // pautomaton* pfa_right = m_pfa->create_flat(m,0,0);



            // (p,v,q )in T_l, (p',v', q') in t_r ==> ((p,p'), (v, v'), (q,q')) T_p

            for(unsigned k=0; k<all_vars_r.size(); k++){
                for(unsigned j=0; j<all_vars_l.size(); j++){

                    
                    std::pair<expr_ref, expr_ref> i_var=std::make_pair(all_vars_r[k].first, all_vars_l[j].first);
                    expr_ref p_pro(mk_fresh_const(&ph_p+k+j, int_sort), m);

                    std::pair<std::pair<expr_ref, expr_ref>,  expr_ref> pair= std::make_pair(i_var, p_pro);
                    product_vars.push_back(pair);

                    // Parikh formula constr uction
                    if( 
                         (k==0 && j==0)  ||
                         (k==0 && j== q_bound) || 
                         (k == q_bound && j==0) || 
                         (k==q_bound && j ==q_bound)
                        )
                           phi_pa_init= m_util_a.mk_add(p_pro, phi_pa_init);


                    if(
                        (k == all_vars_r.size()-1 && j == all_vars_l.size()-1) ||
                        (k == all_vars_r.size()-1 && j == q_bound*(p_l - 1)-1) ||
                        (k == q_bound*(p_r - 1) -1 && j == all_vars_l.size()-1)||
                        (k == q_bound*(p_r - 1) -1 && j == q_bound*(p_l - 1)-1)

                       )
                            phi_pa_final= m_util_a.mk_add(p_pro, phi_pa_final);

                    

                }
            }


            for(unsigned k=0; k<all_vars_l.size(); k++){
                 std::pair<expr_ref, expr_ref> i_var=std::make_pair(eps, all_vars_l[k].first);
                    expr_ref p_pro(mk_fresh_const(&ph_p+k, int_sort), m);

                std::pair<std::pair<expr_ref, expr_ref>,expr_ref> pair=std::make_pair(i_var,p_pro);
                product_vars.push_back(pair);

            }

             for(unsigned k=0; k<all_vars_r.size(); k++){
                 std::pair<expr_ref, expr_ref> i_var=std::make_pair(all_vars_r[k].first, eps);
                std::pair<expr_ref, expr_ref> p_var=std::make_pair(all_vars_r[k].second, eps_p);
                expr_ref p_pro(mk_fresh_const(&ph_p+k, int_sort), m);
                std::pair<std::pair<expr_ref, expr_ref>,expr_ref> pair=std::make_pair(i_var,p_pro);
                product_vars.push_back(pair);

            }

        //Product formula
    
        //phi_#
            app* phi_p=m.mk_true();

            for(auto const& r_var: all_vars_r ){
                  expr_ref sum(mk_fresh_const(&ph_p+'s', int_sort), m);
              
                for(auto const& elt: product_vars){
                        if( r_var.first == elt.first.first) sum= m_util_a.mk_add(sum,elt.second );
                }
            phi_p=m.mk_and(m_util_a.mk_eq(sum,r_var.second), phi_p);
            }
            for(auto const& l_var: all_vars_l ){
                  expr_ref sum(mk_fresh_const(&ph_p+'s', int_sort), m);
              
                for(auto const& elt: product_vars){

                        if( l_var.first == elt.first.second) sum= m_util_a.mk_add(sum,elt.second );

                }
            phi_p=m.mk_and(m_util_a.mk_eq(sum,l_var.second), phi_p);
            }
        // phi_=
                        std::cout << product_vars.size()<< "\n";
                        int kk=0;
                for(auto const& elt: product_vars){
                    if(kk <400){ 
                    expr_ref ge(mk_fresh_const(&ph_p+'g', int_sort), m);

                    expr_ref zero(m_util_a.mk_int(0), m);

                    ge= m_util_a.mk_ge(elt.second, zero); 

                    phi_p= m.mk_and(phi_p, m.mk_implies(ge, m_util_a.mk_eq(elt.first.first, elt.first.second)));
                    std::cout<< __LINE__ << kk++<< "\n";
                }

                }
                std::cout<< __LINE__ << "\n";

        //Parikh image formula   
                        std::cout<< __LINE__ << "\n";
        expr_ref sse(m);
        sse= m.mk_and(sse, phi_pa_init);


        phi_pa_init = m_util_a.mk_eq(phi_pa_init, one);
        phi_pa_final = m_util_a.mk_eq(phi_pa_final, one);


        /*
        collect constraints

        */

        phi_p= m.mk_and(m.mk_and(m.mk_and(phi_left, phi_right), m.mk_and(phi_pa_init,phi_pa_final )), phi_p);
std::cout<< __LINE__ << "\n";
        add_axiom(phi_p);



    }
    



    app* theory_trau::construct_basic_str_ctr(
        ast_manager& m,
        std::vector<std::pair<expr_ref, expr_ref>> vars,
        unsigned l_bound,
        unsigned s_bound){
        

        context& ctx=get_context();
        
        //expr_ref res(m);
        app * res     = m.mk_true();
        //mk_bool_var(t);
        //bool_var bv = ctx.mk_bool_var(res);


        expr_ref print_char_min(m);
        expr_ref print_char_max(m);
        expr_ref one(m);
        one = m_util_a.mk_numeral(rational(1), true);
        print_char_min = m_util_a.mk_numeral(rational(PRINT_CHAR_MIN), true);
        print_char_max = m_util_a.mk_numeral(rational(PRINT_CHAR_MAX), true);

        // PRINTABLE CHAR INTERVAL

        for(auto& v: vars){

        app* gt_min = m_util_a.mk_ge(v.first,print_char_min);


        app* le_max = m_util_a.mk_le(v.first,print_char_max);

        



        res = m.mk_and(res,le_max);
        }
        // vars in the same loop have same parikh image


        for(unsigned j=0; j<vars.size(); j=j+1+s_bound){  

            app * ex     = m.mk_true();

            for(unsigned k=1; k<s_bound; k++){

                app* eq=m_util_a.mk_eq(vars[j].second,vars[j+k].second);
                ex=m.mk_and(ex, eq);
            }
            res=m.mk_and(res, ex);
            app* eq1= m_util_a.mk_eq(vars[j+s_bound-1].second, one);

            res=m.mk_and(ex, eq1);        

        }
        

        return res;
    }
    std::vector<std::pair<expr_ref,expr_ref>>  theory_trau::init_int_vars(unsigned p,unsigned q, std::string s){
        std::vector<std::pair<expr_ref, expr_ref>> res;
        ast_manager &m = get_manager();
        unsigned k=0;
        for(unsigned j=0;j<p;j++){
         context &ctx = get_context();

        sort *int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);
        if(j< p_bound) k++;
        else k=0;
         expr_ref ex (mk_fresh_const(s.c_str()+j+k, int_sort), m);
         expr_ref ex_p( mk_fresh_const(s.c_str()+j+k, int_sort), m);

        ctx.internalize(ex, false);
        ctx.internalize(ex_p, false);

        SASSERT(ctx.get_enode(ex) != NULL);
        SASSERT(ctx.get_enode(ex_p) != NULL);

        SASSERT(ctx.e_internalized(ex));
        SASSERT(ctx.e_internalized(ex_p));

        ctx.mark_as_relevant(to_app(ex));
        ctx.mark_as_relevant(to_app(ex_p));


            res.push_back(std::make_pair(ex,ex_p));

        }
        return res;
    }


    app *theory_trau::mk_fresh_const(char const *name, sort *s)
    {
        string_buffer<64> buffer;
        buffer << name;
        buffer << "!tmp";
        buffer << m_fresh_id;
        m_fresh_id++;
        return m_util_s.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }
    ptr_vector<expr> theory_trau::get_int_vars_from_aut(pautomaton* aut, unsigned s){

        ptr_vector<expr> result;

        for(unsigned j=0; j< s; j++)
        {

            aut->get_moves_from(j);

        }
        //return nullptr;
    }
    
    void theory_trau::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
        app * a_node = to_app(node);
        expr * leftArg = nullptr, * rightArg = nullptr;
        if (!m_util_s.str.is_concat(a_node, leftArg, rightArg)) {
            nodeList.push_back(node);
            return;
        } else {
            get_nodes_in_concat(leftArg, nodeList);
            get_nodes_in_concat(rightArg, nodeList);
        }
    }
    void theory_trau::handle_word_diseq(expr_ref lhs, expr_ref rhs){


         ast_manager & m = get_manager();
        context & ctx = get_context();
        sort * lhs_sort = lhs->get_sort();
        sort * rhs_sort = rhs->get_sort();
        sort * str_sort = m_util_s.str.mk_string_sort();

        if (lhs_sort != str_sort || rhs_sort != str_sort) {
            TRACE("str", tout << "skip equality: not String sort" << std::endl;);
            return;
        }

    //OVER APPROX
    expr_ref len_lhs(m);
    len_lhs = m_util_s.str.mk_length(lhs);
    expr_ref len_rhs(m);
    //len_rhs = m_util_a.mk_numeral(rational(0), true);
    len_rhs=m_util_s.str.mk_length(lhs);
    app* sub= m_util_a.mk_sub(len_lhs, len_rhs);
    app* lhs_lt_rhs = m_util_a.mk_lt(sub, 0);
    app* lhs_gt_rhs = m_util_a.mk_gt(sub,0);

    /* ptr_vector<app> orForm(2);
    orForm.push_back(lhs_gt_rhs);
    orForm.push_back(lhs_lt_rhs);*/
    app * lhs_diff_rhs =m.mk_or(lhs_lt_rhs,lhs_gt_rhs) ;

    //app_ref tst= lhs_lt_rhs | lhs_gt_rhs;
    

   SASSERT(lhs_lt_rhs);
   SASSERT(lhs_gt_rhs);
    add_axiom(lhs_diff_rhs);
   // add_axiom(lhs_gt_rhs);

    //std::cout<<"ADDED NEW CONSTRAINT"<< lhs_neq_rhs<< std::endl;

    }


    void theory_trau::propagate_concat_axiom(enode *cat) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen = false;


        app *a_cat = cat->get_owner();
        SASSERT(m_util_s.str.is_concat(a_cat));
        ast_manager &m = get_manager();

        // build LHS
        expr_ref len_xy(m);
        len_xy = m_util_s.str.mk_length(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app *a_x = to_app(a_cat->get_arg(0));
        app *a_y = to_app(a_cat->get_arg(1));
        expr_ref len_x(m);
        len_x = m_util_s.str.mk_length(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = m_util_s.str.mk_length(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_util_a.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        if (on_screen)
            std::cout << "[Concat Axiom] " << mk_pp(len_xy, m) << " = " << mk_pp(len_x, m) << " + " << mk_pp(len_y, m)
                      << std::endl;

        // finally assert equality between the two subexpressions
        app *eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        add_axiom(eq);
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_trau::propagate_basic_string_axioms(enode *str) {
        bool on_screen = false;

        context &ctx = get_context();
        ast_manager &m = get_manager();

        {
            sort *a_sort = str->get_owner()->get_sort();
            sort *str_sort = m_util_s.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str",
                       tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_owner(), m)
                            << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            STRACE("str", tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app *a_str = str->get_owner();

        if (m_util_s.str.is_string(a_str)) {
            if (on_screen) std::cout << "[ConstStr Axiom] " << mk_pp(a_str, m) << std::endl;

            expr_ref len_str(m);
            len_str = m_util_s.str.mk_length(a_str);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_owner(), strconst);
            unsigned int l = strconst.length();
            expr_ref len(m_util_a.mk_numeral(rational(l), true), m);

            literal lit(mk_eq(len_str, len, false));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        } else {
            // build axiom 1: Length(a_str) >= 0
            {
                if (on_screen) std::cout << "[Non-Zero Axiom] " << mk_pp(a_str, m) << std::endl;

                // build LHS
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app *lhs_ge_rhs = m_util_a.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                STRACE("str", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
                add_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                if (on_screen) std::cout << "[Zero iff Empty Axiom] " << mk_pp(a_str, m) << std::endl;

                // build LHS of iff
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = ctx.mk_eq_atom(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = m_util_s.str.mk_string(symbol(""));
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = ctx.mk_eq_atom(a_str, empty_str);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                literal l(mk_eq(lhs, rhs, true));
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }

        }
    }

    void theory_trau::add_length_axiom(expr *n) {
        add_axiom(m_util_a.mk_ge(n, m_util_a.mk_int(0)));

    }

    void theory_trau::relevant_eh(app *const n) {
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << '\n';);

        if (m_util_s.str.is_length(n)) {
            add_length_axiom(n);
        }
        if (m_util_s.str.is_extract(n)) {
            handle_substr(n);
        } else if (m_util_s.str.is_itos(n)) {
            //handle_itos(n);
        } else if (m_util_s.str.is_stoi(n)) {
            //handle_stoi(n);
        } else if (m_util_s.str.is_at(n)) {
            handle_char_at(n);
        } else if (m_util_s.str.is_replace(n)) {
            handle_replace(n);
        } else if (m_util_s.str.is_index(n)) {
            handle_index_of(n);
        }

        expr *arg;
        if (m_util_s.str.is_length(n, arg) && !has_length(arg) && get_context().e_internalized(arg)) {
            enforce_length(arg);
        }

    }

    /*
    ensure that all elements in equivalence class occur under an application of 'length'
    */
    void theory_trau::enforce_length(expr *e) {
        enode *n = ensure_enode(e);
        enode *n1 = n;
        do {
            expr *o = n->get_owner();
            if (!has_length(o)) {
                expr_ref len = mk_len(o);
                add_length_axiom(len);
            }
            n = n->get_next();
        } while (n1 != n);
    }

    void theory_trau::assign_eh(bool_var v, const bool is_true) {
        ast_manager &m = get_manager();
        STRACE("strg", tout << "assign: bool_var #" << v << " is " << is_true << ", "
                            << mk_pp(get_context().bool_var2expr(v), m) << "@ scope level:" << m_scope_level << '\n';);
        context &ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        expr *e1 = nullptr, *e2 = nullptr;
        if (m_util_s.str.is_prefix(e, e1, e2)) {
            if (is_true) {
                handle_prefix(e);
            } else {
                handle_not_prefix(e);
            }
        } else if (m_util_s.str.is_suffix(e, e1, e2)) {
            if (is_true) {
                handle_suffix(e);
            } else {
                handle_not_suffix(e);
            }
        } else if (m_util_s.str.is_contains(e, e1, e2)) {
            if (is_true) {
                handle_contains(e);
            } else {
                m_not_contains_todo.push_back({{e1, m},
                                               {e2, m}});
            }
        } else if (m_util_s.str.is_in_re(e)) {
            handle_in_re(e, is_true);
        } else {
            TRACE("str", tout << "unhandled literal " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
        }
    }

    void theory_trau::new_eq_eh(theory_var x, theory_var y) {


    
        m_word_eq_var_todo.push_back({x, y});

        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};

        if (axiomatized_eq_vars.count(std::make_pair(x, y)) == 0) {
            axiomatized_eq_vars.insert(std::make_pair(x, y));


            literal l_eq_r = mk_eq(l, r, false);
            literal len_l_eq_len_r = mk_eq(m_util_s.str.mk_length(l), m_util_s.str.mk_length(r), false);
            add_axiom({~l_eq_r, len_l_eq_len_r});
        }
        m_word_eq_todo.push_back({l, r});
          


        STRACE("str", tout << "new_eq: " << l << " = " << r << '\n';);
    }

    template<class T>
    static T *get_th_arith(context &ctx, theory_id afid, expr *e) {
        theory *th = ctx.get_theory(afid);
        if (th && ctx.e_internalized(e)) {
            return dynamic_cast<T *>(th);
        } else {
            return nullptr;
        }
    }

    void theory_trau::new_diseq_eh(theory_var x, theory_var y) {
        m_word_diseq_var_todo.push_back({x, y});

        ast_manager &m = get_manager();
        const expr_ref l{get_enode(x)->get_owner(), m};
        const expr_ref r{get_enode(y)->get_owner(), m};

        m_word_diseq_todo.push_back({l, r});
        STRACE("str", tout << "new_diseq: " << l << " != " << r << '\n';);

        
               
        //handle_word_diseq(l, r);
       // m_word_diseq_todo.pop_back();


    }

    bool theory_trau::can_propagate() {
        return false;
    }

    void theory_trau::propagate() {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "propagate" << '\n';);
            /*
           for (auto const& we  : m_word_eq_todo) {
                const expr_ref  lhs = we.first;
                const expr_ref  rhs = we.second;
                

                handle_word_eq(lhs, rhs);

            
            }
            */
    }




    void theory_trau::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_word_eq_var_todo.push_scope();
        m_word_diseq_var_todo.push_scope();
        m_membership_todo.push_scope();
        m_not_contains_todo.push_scope();
        m_int_eq_todo.push_scope();

        STRACE("str", if (!IN_CHECK_FINAL) tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_trau::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_word_eq_var_todo.pop_scope(num_scopes);
        m_word_diseq_var_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_not_contains_todo.pop_scope(num_scopes);
        m_int_eq_todo.pop_scope(num_scopes);
        m_rewrite.reset();
        STRACE("str", if (!IN_CHECK_FINAL)
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);
    }

    void theory_trau::reset_eh() {
        STRACE("str", tout << "reset" << '\n';);
    }



    zstring theory_trau::print_word_term(expr * e) const{
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return s;
        }
        if (m_util_s.str.is_concat(e)) {
            //e is a concat of some elements
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                s = s+ print_word_term(to_app(e)->get_arg(i));
            }
            return s;
        }
        if (m_util_s.str.is_stoi(e)){
            return zstring("stoi");
        }
        if (m_util_s.str.is_itos(e)){
            return zstring("itos");
        }

        // e is a string variable
        std::stringstream ss;
        ss << "V("<<mk_pp(e, get_manager())<<")";
        s = zstring(ss.str().data());
        return s;

    }

        std::vector<expr*> theory_trau::get_vars(expr * e) const{

             zstring s;
             std::vector<expr*> lst1;
                if (m_util_s.str.is_string(e, s)) {
                    return lst1;                   
                }
                if (m_util_s.str.is_concat(e)) {
                    //e is a concat of some elements
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                        std::vector<expr*> aux;
                        aux=get_vars(to_app(e)->get_arg(i));
                        lst1.insert( lst1.end(), std::make_move_iterator(aux.begin()), std::make_move_iterator(aux.end()));


                        
                    }
                    return lst1;
                }
                if (m_util_s.str.is_stoi(e)){
                    return lst1;
                }
                if (m_util_s.str.is_itos(e)){
                    return lst1;
                }

                // e is a string variable
                std::stringstream ss;
                ss << "V("<<mk_pp(e, get_manager())<<")";
                s = zstring(ss.str().data());
                lst1.push_back(e);
                return lst1;


        }


        zstring theory_trau::print_vars(expr * e) const{

                zstring s;
                if (m_util_s.str.is_string(e, s)) {
                    return "";                   
                }
                if (m_util_s.str.is_concat(e)) {
                    //e is a concat of some elements
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                        s = s+ print_vars(to_app(e)->get_arg(i));
                    }
                    return s;
                }
                if (m_util_s.str.is_stoi(e)){
                    return "";
                }
                if (m_util_s.str.is_itos(e)){
                    return "";
                }

                // e is a string variable
                std::stringstream ss;
                ss << "V("<<mk_pp(e, get_manager())<<")";
                s = zstring(ss.str().data());
                return s;

            }

    expr* theory_trau::get_vars(expr * e, ptr_vector<expr> lst) const{
               // ptr_vector<expr> ex;
               zstring s;
                if (m_util_s.str.is_string(e, s)) {
                    return nullptr;               
                }
                if (m_util_s.str.is_concat(e)) {
                    //e is a concat of some elements
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                        std::cout<<"*******"<<i<<"\n";
                        lst.push_back(get_vars(to_app(e)->get_arg(i), lst));
                         std::cout<<"showing elt:" << mk_pp(e, get_manager())<<std::endl;

                       /* if( != nullptr){
                                 lst.push_back(to_app(e)->get_arg(i));
                        }*/
                    }
                    return to_app(e)->get_arg(0);
                }
                if (m_util_s.str.is_stoi(e)){
                    return nullptr;
                }
                if (m_util_s.str.is_itos(e)){
                    return nullptr;
                }

                // e is a string variable
                /*std::stringstream ss;
                ss << "V("<<mk_pp(e, get_manager())<<")";
                s = zstring(ss.str().data());*/
                return e;

            }


    final_check_status theory_trau::final_check_eh() {
        std::cout << "final_check starts\n"<<std::endl;


        if (m_word_eq_todo.empty() && m_word_diseq_todo.empty()) {
            return FC_DONE;
        }
        
        else{

             if(m_int_eq_todo.empty())// check for new integer constaint; ==> if the overapprox is over or not== > underapprox
            {
                is_over_approximation=false;
                 //Handle word eq, underAproxx
                 for (const auto& we : m_word_eq_todo) {
                                
                        //handle word eq, Over Approxx
                        handle_word_eq(we.first, we.second);

                    }              
                 
            }
            else{
            /// handle the rest of the constraints ,Over Approxx
                    for (const auto& we : m_word_eq_todo) {
                                
                        handle_word_eq(we.first, we.second);

                    }

                return FC_CONTINUE;
            }
        }


        block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
        IN_CHECK_FINAL = false;
        return FC_CONTINUE;
    }

    model_value_proc *theory_trau::mk_value(enode *const n, model_generator &mg) {
        app *const tgt = n->get_owner();
        (void) m;
        STRACE("str", tout << "mk_value: sort is " << mk_pp(tgt->get_sort(), m) << ", "
                           << mk_pp(tgt, m) << '\n';);
        return alloc(expr_wrapper_proc, tgt);
    }

    void theory_trau::init_model(model_generator &mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init_model\n";);
    }

    void theory_trau::finalize_model(model_generator &mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "finalize_model\n";);
    }

    lbool theory_trau::validate_unsat_core(expr_ref_vector &unsat_core) {
        return l_undef;
    }

    bool theory_trau::is_of_this_theory(expr *const e) const {
        return is_app(e) && to_app(e)->get_family_id() == get_family_id();
    }

    bool theory_trau::is_string_sort(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_trau::is_regex_sort(expr *const e) const {
        return m_util_s.is_re(e);
    }

    bool theory_trau::is_const_fun(expr *const e) const {
        return is_app(e) && to_app(e)->get_decl()->get_arity() == 0;
    }

    expr_ref theory_trau::mk_sub(expr *a, expr *b) {
        ast_manager &m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }
    // check if scoped vector contains elt 
    bool theory_trau::contains_elt(app* elt, scoped_vector<app*> vec) {
        ast_manager& m = get_manager();

        for (app* app_elt :  vec){
            if(m.are_equal(app_elt, elt) ) return true;
        }
    return false;
    }


    expr_ref
    theory_trau::mk_skolem(symbol const &name, expr *e1, expr *e2, expr *e3, expr *e4, sort *sort) {
        ast_manager &m = get_manager();
        expr *es[4] = {e1, e2, e3, e4};
        unsigned len = e4 ? 4 : (e3 ? 3 : (e2 ? 2 : 1));

        if (!sort) {
            sort = e1->get_sort();
        }
        app *a = m_util_s.mk_skolem(name, len, es, sort);

//        ctx.internalize(a, false);
//        mk_var(ctx.get_enode(a));
//        propagate_basic_string_axioms(ctx.get_enode(a));
//
//        enode* n = ctx.get_enode(a);
//
//        if (!is_attached_to_var(n)) {
//            const theory_var v = theory::mk_var(n);
//            ctx.attach_th_var(n, this, v);
//            ctx.mark_as_relevant(n);
//            STRACE("str", tout << "new theory_var #" << v << '\n';);
//        }

        expr_ref ret(a, m);
        string_theory_propagation(ret);

        return expr_ref(a, m);

    }

    literal theory_trau::mk_literal(expr *const e) {
        ast_manager &m = get_manager();
        context &ctx = get_context();
        expr_ref ex{e, m};
        m_rewrite(ex);
        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *const n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
    }

    bool_var theory_trau::mk_bool_var(expr *const e) {
        ast_manager &m = get_manager();
        STRACE("str", tout << "mk_bool_var: " << mk_pp(e, m) << '\n';);
        if (!m.is_bool(e)) {
            return null_bool_var;
        }
        context &ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        const bool_var &bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
        return bv;
    }



    void theory_trau::add_axiom(expr *const e) {
        bool on_screen = true;
        STRACE("str_axiom", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

        if (on_screen) STRACE("str_axiom",
                              std::cout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);


        if (!axiomatized_terms.contains(e) || false) {
            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
//        string_theory_propagation(e);
            context &ctx = get_context();
//        SASSERT(!ctx.b_internalized(e));
            if (!ctx.b_internalized(e)) {
                ctx.internalize(e, false);
            }
            ctx.internalize(e, false);
           /// std::cout<< "ADDING AXIOM " <<std::endl;
            literal l{ctx.get_literal(e)};
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }
    }

    void theory_trau::add_axiom(std::initializer_list<literal> ls) {
        bool on_screen = true;

        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        literal_vector lv;
        for (const auto &l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        ctx.mk_th_axiom(get_id(), lv.size(), lv.c_ptr());
        if (on_screen) STRACE("str_axiom", std::cout << __LINE__ << " " << __FUNCTION__;);
        if (on_screen) STRACE("str_axiom", ctx.display_literals_verbose(std::cout, lv) << std::endl;);
        STRACE("str_axiom", ctx.display_literals_verbose(tout << "[Assert_c]\n", lv) << '\n';);
        STRACE("str_axiom", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      Let e = at(s, i)
        0 <= i < len(s)  ->  s = xey /\ len(x) = i /\ len(e) = 1
        i < 0 \/ i >= len(s)  ->  e = empty
    */
    void theory_trau::handle_char_at(expr *e) {

        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));
        expr_ref len_e(m_util_s.str.mk_length(e), m);
        expr_ref len_s(m_util_s.str.mk_length(s), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref x = mk_skolem(symbol("m_char_at_left"), s, i);
        expr_ref y = mk_skolem(symbol("m_char_at_right"), s, i);
        expr_ref xey(m_util_s.str.mk_concat(x, m_util_s.str.mk_concat(e, y)), m);
        string_theory_propagation(xey);

        expr_ref len_x(m_util_s.str.mk_length(x), m);
        expr_ref emp(m_util_s.str.mk_empty(e->get_sort()), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero));

        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(s, xey, false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});

        add_axiom({i_ge_0, mk_eq(e, emp, false)});
        add_axiom({~i_ge_len_s, mk_eq(e, emp, false)});
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      TBD: check semantics of extract, a.k.a, substr(s, i ,l)

      let e = extract(s, i, l)

      i is start index, l is length of substring starting at index.

      i < 0 => e = ""
      i >= |s| => e = ""
      l <= 0 => e = ""
      0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)

    this translates to:

      0 <= i <= |s| -> s = xey
      0 <= i <= |s| -> len(x) = i
      0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
      0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
      i >= |s| => |e| = 0
      i < 0 => |e| = 0
      l <= 0 => |e| = 0

      It follows that:
      |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|
    */
    void theory_trau::handle_substr(expr *e) {
        if (!axiomatized_terms.contains(e) || false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *s = nullptr, *i = nullptr, *l = nullptr;
            VERIFY(m_util_s.str.is_extract(e, s, i, l));

            expr_ref x(mk_skolem(symbol("m_substr_left"), s, i), m);
            expr_ref ls(m_util_s.str.mk_length(s), m);
            expr_ref lx(m_util_s.str.mk_length(x), m);
            expr_ref le(m_util_s.str.mk_length(e), m);
            expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
            expr_ref y(mk_skolem(symbol("m_substr_right"), s, ls_minus_i_l), m);
            expr_ref xe(m_util_s.str.mk_concat(x, e), m);
            expr_ref xey(m_util_s.str.mk_concat(x, e, y), m);

            string_theory_propagation(xe);
            string_theory_propagation(xey);

            expr_ref zero(m_util_a.mk_int(0), m);

            literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
            literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
            literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
            literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
            literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(lx, i, false)});
            add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
            add_axiom({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
            add_axiom({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false)});
            add_axiom({i_ge_0, mk_eq(le, zero, false)});
            add_axiom({ls_le_i, mk_eq(le, zero, false)});
            add_axiom({~ls_le_0, mk_eq(le, zero, false)});
        }
    }
    void theory_trau::handle_replace(expr *r) {
        context& ctx = get_context();
        expr* a = nullptr, *s = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace(r, a, s, t));
        expr_ref x  = mk_skolem(symbol("m_contains_left"), a, s);
        expr_ref y  = mk_skolem(symbol("m_contains_right"), a, s);
        expr_ref xty = mk_concat(x, mk_concat(t, y));
        expr_ref xsy = mk_concat(x, mk_concat(s, y));
        literal a_emp = mk_eq_empty(a, true);
        literal s_emp = mk_eq_empty(s, true);
        literal cnt = mk_literal(m_util_s.str.mk_contains(a, s));
        add_axiom({~a_emp, s_emp, mk_eq(r, a,false)});
        add_axiom({cnt,  mk_eq(r, a,false)});
        add_axiom({~s_emp, mk_eq(r, mk_concat(t, a),false)});
        add_axiom({~cnt, a_emp, s_emp, mk_eq(a, xsy,false)});
        add_axiom({~cnt, a_emp, s_emp, mk_eq(r, xty,false)});
        ctx.force_phase(cnt);
        tightest_prefix(s, x);

    }
    void theory_trau::handle_index_of(expr *i) {
        if(!axiomatized_terms.contains(i)||false) {
            axiomatized_terms.insert(i);
            ast_manager &m = get_manager();
            expr *s = nullptr, *t = nullptr, *offset = nullptr;
            rational r;
            VERIFY(m_util_s.str.is_index(i, t, s) || m_util_s.str.is_index(i, t, s, offset));

            expr_ref minus_one(m_util_a.mk_int(-1), m);
            expr_ref zero(m_util_a.mk_int(0), m);

            expr_ref emp(m_util_s.str.mk_empty(t->get_sort()), m);

            literal cnt = mk_literal(m_util_s.str.mk_contains(t, s));


            literal i_eq_m1 = mk_eq(i, minus_one, false);
            literal i_eq_0 = mk_eq(i, zero, false);
            literal s_eq_empty = mk_eq(s, emp, false);
            literal t_eq_empty = mk_eq(t, emp, false);

            add_axiom({cnt, i_eq_m1});
            add_axiom({~t_eq_empty, s_eq_empty, i_eq_m1});

            if (!offset || (m_util_a.is_numeral(offset, r) && r.is_zero())) {
                expr_ref x = mk_skolem(symbol("m_contains_left"), t, s);
                expr_ref y = mk_skolem(symbol("m_contains_right"), t, s);
                expr_ref xsy(m_util_s.str.mk_concat(x, s, y), m);
                string_theory_propagation(xsy);

                // |s| = 0 => indexof(t,s,0) = 0
                // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
                expr_ref lenx(m_util_s.str.mk_length(x), m);
                add_axiom({~s_eq_empty, i_eq_0});
                add_axiom({~cnt, s_eq_empty, mk_eq(t, xsy, false)});
                add_axiom({~cnt, s_eq_empty, mk_eq(i, lenx, false)});
                add_axiom({~cnt, mk_literal(m_util_a.mk_ge(i, zero))});

                tightest_prefix(s, x);
            } else {
                expr_ref len_t(m_util_s.str.mk_length(t), m);
                literal offset_ge_len = mk_literal(m_util_a.mk_ge(mk_sub(offset, len_t), zero));
                literal offset_le_len = mk_literal(m_util_a.mk_le(mk_sub(offset, len_t), zero));
                literal i_eq_offset = mk_eq(i, offset, false);
                add_axiom({~offset_ge_len, s_eq_empty, i_eq_m1});
                add_axiom({offset_le_len, i_eq_m1});
                add_axiom({~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset});

                expr_ref x = mk_skolem(symbol("m_contains_left"), t, s, offset);
                expr_ref y = mk_skolem(symbol("m_contains_right"), t, s, offset);
                expr_ref xy(m_util_s.str.mk_concat(x, y), m);
                string_theory_propagation(xy);

                expr_ref indexof0(m_util_s.str.mk_index(y, s, zero), m);
                expr_ref offset_p_indexof0(m_util_a.mk_add(offset, indexof0), m);
                literal offset_ge_0 = mk_literal(m_util_a.mk_ge(offset, zero));
                add_axiom(
                        {~offset_ge_0, offset_ge_len, mk_eq(t, xy, false)});
                add_axiom(
                        {~offset_ge_0, offset_ge_len, mk_eq(m_util_s.str.mk_length(x), offset, false)});
                add_axiom({~offset_ge_0, offset_ge_len, ~mk_eq(indexof0, minus_one, false), i_eq_m1});
                add_axiom({~offset_ge_0, offset_ge_len, ~mk_literal(m_util_a.mk_ge(indexof0, zero)),
                            mk_eq(offset_p_indexof0, i, false)});

                // offset < 0 => -1 = i
                add_axiom({offset_ge_0, i_eq_m1});
            }
        }
    }

    void theory_trau::tightest_prefix(expr* s, expr* x) {
        expr_ref s1 = mk_first(s);
        expr_ref c  = mk_last(s);
        expr_ref s1c = mk_concat(s1, m_util_s.str.mk_unit(c));
        literal s_eq_emp = mk_eq_empty(s);
        add_axiom({s_eq_emp, mk_eq(s, s1c,true)});
        add_axiom({s_eq_emp, ~mk_literal(m_util_s.str.mk_contains(mk_concat(x, s1), s))});
    }

    expr_ref theory_trau::mk_first(expr* s) {
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_string(str.extract(0, str.length()-1)), m);
        }
        return mk_skolem(symbol("seq_first"), s);
    }

    expr_ref theory_trau::mk_last(expr* s) {
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_char(str, str.length()-1), m);
        }
        sort* char_sort = nullptr;
        VERIFY(m_util_s.is_seq(s->get_sort(), char_sort));
        return mk_skolem(symbol("seq_last"), s, nullptr, nullptr, nullptr, char_sort);
    }

    expr_ref theory_trau::mk_concat(expr* e1, expr* e2) {
        return expr_ref(m_util_s.str.mk_concat(e1, e2), m);
    }

    literal theory_trau::mk_eq_empty(expr* _e, bool phase) {
        context& ctx = get_context();
        expr_ref e(_e, m);
        SASSERT(m_util_s.is_seq(e));
        expr_ref emp(m);
        zstring s;
        if (m_util_s.str.is_empty(e)) {
            return true_literal;
        }
        expr_ref_vector concats(m);
        m_util_s.str.get_concat(e, concats);
        for (auto c : concats) {
            if (m_util_s.str.is_unit(c)) {
                return false_literal;
            }
            if (m_util_s.str.is_string(c, s) && s.length() > 0) {
                return false_literal;
            }
        }
        emp = m_util_s.str.mk_empty(e->get_sort());

        literal lit = mk_eq(e, emp, false);
        ctx.force_phase(phase?lit:~lit);
        ctx.mark_as_relevant(lit);
        return lit;
    }


    // e = prefix(x, y), check if x is a prefix of y
    void theory_trau::handle_prefix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref s = mk_skolem(symbol("m_prefix_right"), x, y);
            expr_ref xs(m_util_s.str.mk_concat(x, s), m);
            string_theory_propagation(xs);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(y, xs, false)});
        }
    }

// e = prefix(x, y), check if x is not a prefix of y
    void theory_trau::handle_not_prefix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref p= mk_skolem(symbol("m_not_prefix_left"), x, y);
            expr_ref mx= mk_skolem(symbol("m_not_prefix_midx"), x, y);
            expr_ref my= mk_skolem(symbol("m_not_prefix_midy"), x, y);
            expr_ref qx= mk_skolem(symbol("m_not_prefix_rightx"), x, y);
            expr_ref qy= mk_skolem(symbol("m_not_prefix_righty"), x, y);

            expr_ref len_x_gt_len_y{m_util_a.mk_gt(m_util_a.mk_sub(m_util_s.str.mk_length(x),m_util_s.str.mk_length(y)), m_util_a.mk_int(0)),m};

            literal len_y_gt_len_x = mk_literal(len_x_gt_len_y);

            expr_ref pmx(m_util_s.str.mk_concat(p, mx), m);
            string_theory_propagation(pmx);
            expr_ref pmxqx(m_util_s.str.mk_concat(pmx, qx), m);
            string_theory_propagation(pmxqx);

            expr_ref pmy(m_util_s.str.mk_concat(p, my), m);
            string_theory_propagation(pmy);
            expr_ref pmyqy(m_util_s.str.mk_concat(pmy, qy), m);
            string_theory_propagation(pmyqy);

            literal x_eq_pmq = mk_eq(x,pmxqx,false);
            literal y_eq_pmq = mk_eq(y,pmyqy,false);

            literal len_mx_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(mx),false);
            literal len_my_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(my),false);
            literal eq_mx_my = mk_eq(mx, my,false);

            literal lit_e = mk_literal(e);
            add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, len_mx_is_one});
            add_axiom({lit_e, len_y_gt_len_x, len_my_is_one});
            add_axiom({lit_e, len_y_gt_len_x, ~eq_mx_my});
        }
    }


    // e = suffix(x, y), check if x is a suffix of y
    void theory_trau::handle_suffix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_suffix(e, x, y));

            expr_ref p = mk_skolem(symbol("m_suffix_left"), x, y);
            expr_ref px(m_util_s.str.mk_concat(p, x), m);
            string_theory_propagation(px);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(y, px, false)});
        }
    }

    // e = suffix(x, y), check if x is not a suffix of y
    void theory_trau::handle_not_suffix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref q= mk_skolem(symbol("m_not_suffix_right"), x, y);
            expr_ref mx= mk_skolem(symbol("m_not_suffix_midx"), x, y);
            expr_ref my= mk_skolem(symbol("m_not_suffix_midy"), x, y);
            expr_ref px= mk_skolem(symbol("m_not_suffix_leftx"), x, y);
            expr_ref py= mk_skolem(symbol("m_not_suffix_lefty"), x, y);



            expr_ref len_x_gt_len_y{m_util_a.mk_gt(m_util_a.mk_sub(m_util_s.str.mk_length(x),m_util_s.str.mk_length(y)), m_util_a.mk_int(0)),m};

            literal len_y_gt_len_x = mk_literal(len_x_gt_len_y);

            expr_ref pxmx(m_util_s.str.mk_concat(px, mx), m);
            string_theory_propagation(pxmx);
            expr_ref pxmxq(m_util_s.str.mk_concat(pxmx, q), m);
            string_theory_propagation(pxmxq);

            expr_ref pymy(m_util_s.str.mk_concat(py, my), m);
            string_theory_propagation(pymy);
            expr_ref pymyq(m_util_s.str.mk_concat(pymy, q), m);
            string_theory_propagation(pymyq);

            literal x_eq_pmq = mk_eq(x,pxmxq,false);
            literal y_eq_pmq = mk_eq(y,pymyq,false);

            literal len_mx_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(mx),false);
            literal len_my_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(my),false);
            literal eq_mx_my = mk_eq(mx, my,false);

            literal lit_e = mk_literal(e);
            add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, len_mx_is_one});
            add_axiom({lit_e, len_y_gt_len_x, len_my_is_one});
            add_axiom({lit_e, len_y_gt_len_x, ~eq_mx_my});
        }
    }

    // e = contains(x, y)
    void theory_trau::handle_contains(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_contains(e, x, y));
            expr_ref p = mk_skolem(symbol("m_contains_left"), x, y);
            expr_ref s = mk_skolem(symbol("m_contains_right"), x, y);
            expr_ref pys(m_util_s.str.mk_concat(m_util_s.str.mk_concat(p, y), s), m);

            string_theory_propagation(pys);
//            expr_ref not_e(m.mk_not(e),m);
//            add_axiom(m.mk_or(not_e, m.mk_eq(y, pys)));
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(x, pys, false)});
        }

    }

    void theory_trau::handle_in_re(expr *const e, const bool is_true) {
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));
        ast_manager& m = get_manager();

//        expr_ref tmp{e, m};
//        m_rewrite(tmp);
//        if ((m.is_false(tmp) && is_true) || (m.is_true(tmp) && !is_true)) {
//            literal_vector lv;
//            lv.push_back(is_true ? mk_literal(e) : ~mk_literal(e));
//            set_conflict(lv);
//            return;
//        }
        expr_ref r{re, m};
        context& ctx = get_context();
        literal l = ctx.get_literal(e);
        if (!is_true) {
            r = m_util_s.re.mk_complement(re);
            l.neg();
        }
        m_membership_todo.push_back({{s, m}, r});
    }

    void theory_trau::set_conflict(const literal_vector& lv) {
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx.get_region(), lv.size(), lv.c_ptr(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE("str", ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_trau::block_curr_assignment() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen=false;

        if(on_screen) std::cout<<"[block] ";
        for (const auto& we : m_word_eq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"="<<we.second<<")";
        }
        for (const auto& we : m_word_diseq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"!="<<we.second<<")";
        }
        if(on_screen) std::cout<<std::endl;

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE("str", tout << "[Refinement]\nformulas:\n";);
        for (const auto& we : m_word_eq_todo) {
            expr *const e = m.mk_not(m.mk_eq(we.first, we.second));
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << we.first << " = " << we.second << '\n';);
        }
        for (const auto& wi : m_word_diseq_todo) {
//            expr *const e = mk_eq_atom(wi.first, wi.second);
            expr *const e = m.mk_eq(wi.first, wi.second);
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << wi.first << " != " << wi.second << '\n';);
        }
        if (refinement != nullptr) {
            add_axiom(refinement);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_trau::dump_assignments() const {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                std::cout << "dump all assignments:\n";
                expr_ref_vector assignments{m};


                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                   // ctx.mark_as_relevant(e);
                    std::cout <<"**"<< mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
    }
}
