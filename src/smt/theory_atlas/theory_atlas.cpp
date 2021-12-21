#include <algorithm>
#include <sstream>
#include <math.h>    
#include "ast/ast_pp.h"
#include "smt/theory_atlas/theory_atlas.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt {
    class int_expr_solver:expr_solver {
    bool initialized;
    ast_manager& m;
    kernel m_kernel;
    expr_ref_vector erv;

public:
    int_expr_solver(ast_manager& m, smt_params fp):
        initialized(false), m(m), m_kernel(m, fp), erv(m) {
        fp.m_string_solver = symbol("none");
    }

    void assert_expr(expr *e) {
        erv.push_back(e);
        // m_kernel.assert_expr(e);
    }

    void assert_expr(const expr_ref_vector &v) {
        erv.append(v);
        // m_kernel.assert_expr(v);
    }

    void initialize(context &ctx) {
        bool on_screen = false;

        if (!initialized) {
            initialized = true;
            expr_ref_vector Assigns(m), Literals(m);
            ctx.get_guessed_literals(Literals);
            ctx.get_assignments(Assigns);
            for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                if (on_screen) std::cout << "check_sat context from asserted:" << mk_pp(ctx.get_asserted_formula(i), m) << std::endl;
                assert_expr(ctx.get_asserted_formula(i));
            }
            for (auto &e:Assigns) {
                if (ctx.is_relevant(e)) {
                    if (on_screen) std::cout << "check_sat context from assign:" << mk_pp(e, m) << std::endl;
                    assert_expr(e);
                }
                if (on_screen) std::cout << "is relevant: " << ctx.is_relevant(e) << " get_assignment: " << ctx.get_assignment(e) << std::endl;
            }
            
        }
    }
    lbool check_sat(expr *v) {
        SASSERT(false);
        lbool r = m_kernel.check(1, &v);
        return r;
    }
    lbool check_sat(const expr_ref_vector &v) {
        erv.append(v);
        lbool r = m_kernel.check(erv);
        return r;
    }
    context& get_context() {
        return m_kernel.get_context();
    }
};
    bool theory_atlas::is_over_approximation = true;
    bool theory_atlas::str_solver_checked= false;
    bool theory_atlas::assignement_dumped= false;

    bool theory_atlas::is_undeapp_over= false;

    namespace {
        bool IN_CHECK_FINAL = false;
    }

    theory_atlas::theory_atlas(context& ctx,ast_manager &m, const theory_str_params &params):
     theory(ctx, m.mk_family_id("seq")), 
      m_params{params}, 
     m_rewrite{m}, 
     m_util_a{m},
     m_util_s{m}, 
     m{m}, 
     m_length(m),
     m_fresh_id(0),
     axioms{m}  {
     }
     
  theory_atlas::~theory_atlas(){
            }
    void theory_atlas::display(std::ostream &os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_atlas::init() {
         
        theory::init();

        STRACE("str", if (!IN_CHECK_FINAL) tout << "init\n";);
    }

    enode *theory_atlas::ensure_enode(expr *e) {
                 

        context &ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode *n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    theory_var theory_atlas::mk_var(enode *const n) {
                // 

        if (!m_util_s.is_seq(n->get_expr()) &&
            !m_util_s.is_re(n->get_expr())) {
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


    bool theory_atlas::internalize_atom(app *const atom, const bool gate_ctx) {
    //     

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

    bool theory_atlas::internalize_term(app *const term) {
             //    

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

    void theory_atlas::apply_sort_cnstr(enode *n, sort *s) {
                 

        mk_var(n);
    }

    void theory_atlas::print_ctx(context &ctx) {  // test_hlin
        std::cout << "~~~~~ print ctx start ~~~~~~~\n";
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

    void theory_atlas::print_ast(expr *e) {  // test_hlin
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


    void theory_atlas::init_search_eh() {
         
        
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            string_theory_propagation(ex);
            
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_atlas::string_theory_propagation(expr *expr) {
         
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

    void theory_atlas::handle_word_eq(expr* lhs, expr* rhs){
        
         

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
        TRACE("str", tout << "equality over-approximation starts" << std::endl;);
        word_eq_over_approx(lhs, rhs);

        }else{
            if(!is_undeapp_over){
            TRACE("str", tout << "equality under approximations starts" << std::endl;);
            expr_ref_vector new_int_const(m);
            word_eq_under_approx(lhs,rhs, new_int_const);
            is_undeapp_over=true;
            }
        
        }
    }

    void theory_atlas:: word_eq_over_approx(expr* lhs, expr* rhs){
         

            expr_ref len_lhs(m);
            expr_ref zero(m);
            zero= m_util_a.mk_numeral(rational(0), true);
            len_lhs = m_util_s.str.mk_length(lhs);
            expr_ref len_rhs(m);
            len_rhs=m_util_s.str.mk_length(lhs);
            app* lhs_eq_rhs = m_util_a.mk_eq(m_util_a.mk_sub(len_rhs, len_lhs), zero);
            SASSERT(lhs_eq_rhs);
            add_axiom(lhs_eq_rhs); // constraint dealt with, it should be removed ??! 
            
            if (!contains_elt(lhs_eq_rhs,m_int_eq_todo))
                {m_int_eq_todo.push_back(lhs_eq_rhs);}

    }
     void theory_atlas::word_eq_under_approx(expr* lhs, expr* rhs, expr_ref_vector & items){

        /*TODO: 
                -get string vars
                -convert to sets of integer vars:
                    ->-> define p and q create flat automata 
                    -> concatenate lhs(resp. rhs) nodes automata
                    ->
                    
                -convert equalities
       */
      /*
      TEMPORARELY DISABLED: word equations with string constants*/
        expr_ref_vector len_l(m), len_r(m);
        ptr_vector<expr> lhs_nodes, rhs_nodes;
        zstring s;
        expr_ref_vector str_vars(m);
        get_nodes_in_concat(lhs,lhs_nodes);
        get_nodes_in_concat(rhs,rhs_nodes);
       
   
  /*
            zstring s;
            if (is_app(lhs_nodes[k])) {
                app *ap = to_app(lhs_nodes[k]);
                if (!m_util_s.str.is_concat(ap)) {
                   if(m_util_s.str.is_string(lhs_nodes[k], s)){
                        //flag lhs_nodes[k];
                        expr_ref n(m);
                         mk_newvar(s,&states);
                        


                    }
                    if (!str_vars.contains(lhs_nodes[k]))
                        str_vars.push_back(lhs_nodes[k]);
                        len_l.push_back(m_util_s.str.mk_length(lhs_nodes[k]));
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
                len_r.push_back(m_util_s.str.mk_length(v));
            }
            

        }*/
       // add_axiom(m_util_a.mk_eq(m_util_a.mk_add(len_l), m_util_a.mk_add(len_r)));
       
       
                        

        ast_manager &m = get_manager();
        context & ctx = get_context();   
        std::vector<expr*> lhs_vars=get_vars(lhs);
        std::vector<expr*> rhs_vars=get_vars(rhs);

        
       // pautomaton* pfa_left = m_pfa->create_flat(m,0,0);
        unsigned num_vars= p_bound*(q_bound+1)-1;
      
                               



        std::vector<std::pair<std::string, std::string>> states_l;
        std::vector<std::pair<std::string, std::string>> states_r;

        std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>> product_vars;
        std::vector<std::pair<expr_ref, expr_ref>> all_vars_l;
        std::vector<std::pair<expr_ref, expr_ref>> all_vars_r;
        expr_ref_vector lhs_len(m), rhs_len(m);
        expr_ref ep(mk_fresh_const("ep", int_sort), m);
        expr_ref eps_p(m);
        unsigned count=0;
         
         if ( rhs_vars.size()> lhs_vars.size()){
             expr_ref aux_v(mk_fresh_const("aux_v", int_sort), m);
            // lhs_nodes.push_back(aux_v);
         }
         else if (rhs_vars.size()<lhs_vars.size())
         {
            elif  :
             expr_ref aux_v(mk_fresh_const("aux_v", int_sort), m);
           //  rhs_nodes.push_back(aux_v);
         }
        for( auto elt: lhs_nodes){                           
            std::string s;
            zstring zs;
            std::stringstream ss;
            
            std::vector<std::pair<std::string, std::string>> states;
            std::vector<std::pair<expr_ref, expr_ref>> vars;
            app *ap = to_app(elt);
           
            
           if(!m_util_s.str.is_concat(ap)){
                if (!fresh_int_vars.contains(elt) ) {
                     if(m_util_s.str.is_string(elt, zs)){
                        expr_ref n(m);
                        n=expr_ref(to_app(elt), m);
                        vars= mk_newvar2(n, zs,&states);
                        ss <<zs;
                        s = ss.str().data();

                        }
                    else{
            
                        ss <<mk_pp(elt, get_manager());
                        s = ss.str().data();
                        expr_ref n(m);
                        n=expr_ref(to_app(elt), m);
                        vars =init_int_vars2(n, num_vars,s, &states); 
                        
                        fresh_int_vars.insert(elt, vars);
                        model.insert(elt,"");
                        }
                }  else{
                     expr_ref n(m); 
                     n=expr_ref(to_app(elt), m); 
                    expr_ref ax(m);
                    ax=expr_ref(ap,m);
                   
                    find_vars(n, &vars);
                    //vars_map.find() //find(elt,);
                     
                   // states_map.find(elt,states);
                   
                   
                    find_states( n,&states);  
                  
                }
         
            if(count>0 && count < lhs_nodes.size()) {
                std::string newv= expr2str(all_vars_l[all_vars_l.size()-1].first) ;
                std::string newv2;
                if(m_util_s.str.is_string(elt, zs)) newv2= expr2str(elt).substr(1, expr2str(elt).size()-2);
                else newv2=expr2str(elt);
              // :: .substr(0, expr2str(elt).find("\""));

                newv= newv.substr(0, newv.find("!tmp") ); /// .split("!tmp";
                
                expr_ref n_ex(mk_fresh_const(newv+newv2+"!tmp", int_sort), m);

                expr_ref n_exp(mk_fresh_const('p'+newv+newv2+"!tmp"+std::to_string(count), int_sort), m);
             
                int_vars.push_back(n_ex);
                int_vars.push_back(n_exp);

                  axioms.push_back(m_util_a.mk_eq(n_ex, m_util_a.mk_numeral(rational(32), true)));
                axioms.push_back(m_util_a.mk_eq(n_exp, m_util_a.mk_numeral(rational(1), true)));

                   

                all_vars_l.push_back(std::make_pair(n_ex, n_exp));
                                        states_l.push_back(std::make_pair(states_l[states_l.size()-1].second, states[0].first));

                
            }
        
                     
            all_vars_l.insert(all_vars_l.end(),vars.begin(), vars.end() );
            count ++;
            states_l.insert(states_l.end(),states.begin(), states.end() );
             
            
        }
        
       }
        count=0;
      
        for(auto  elt: rhs_nodes){
                          //   std:: cout << " !!!!!" << mk_pp(elt,m) <<"\n";


            std::string s;
            std::stringstream ss;
            std::vector<std::pair<std::string, std::string>> states;
            std::vector<std::pair<expr_ref, expr_ref>> vars;
            app *ap = to_app(elt);
            zstring zs;
            expr_ref e(m);
            e=expr_ref(ap,m);
            if(!m_util_s.str.is_concat(ap)){
            if (!fresh_int_vars.contains(elt)){        

            if(m_util_s.str.is_string(elt, zs)){
                        //flag lhs_nodes[k];
                        expr_ref n(m);
                        n=expr_ref(to_app(elt), m);
                        vars= mk_newvar2(n, zs,&states);
                         ss<< zs;
                         s = ss.str().data();

                    } else{
            ss <<mk_pp(elt, get_manager());
            s = ss.str().data();
             expr_ref n(m);
            n=expr_ref(to_app(elt), m);
            vars =init_int_vars2(n,num_vars,s, &states); 
            fresh_int_vars.insert(elt, vars);
            model.insert(elt,"");
            }
            }
            else{
                expr_ref ee(m); 
                expr_ref n(m);
            n=expr_ref(to_app(elt), m);
                ee= expr_ref(ap,m); 
                                    find_vars(n, &vars); 
                states_map.find(elt,states); 
            }
             
            if(count>0 && count < rhs_nodes.size()) {
                std::string newv= expr2str(all_vars_r[all_vars_r.size()-1].first) ;
                std::string newv2; 
                if(m_util_s.str.is_string(elt, zs)) newv2= expr2str(elt).substr(1, expr2str(elt).size()-2);
                // 
                else newv2=expr2str(elt);
                newv= newv.substr(0, newv.find("!tmp") ); 
                expr_ref n_ex(mk_fresh_const(newv+newv2+"!tmp", int_sort), m);
 
                expr_ref n_exp(mk_fresh_const('p'+newv+newv2+"!tmp"+std::to_string(count), int_sort), m);
                int_vars.push_back(n_ex);
                int_vars.push_back(n_exp); 
                 axioms.push_back(m_util_a.mk_eq(n_ex, m_util_a.mk_numeral(rational(32), true)));
                 axioms.push_back(m_util_a.mk_eq(n_exp, m_util_a.mk_numeral(rational(1), true)));
         
                all_vars_r.push_back(std::make_pair(n_ex, n_exp));
                 states_r.push_back(std::make_pair(states_r[states_r.size()-1].second, states[0].first));
                            
            }
            all_vars_r.insert(all_vars_r.end(),vars.begin(), vars.end() );  
            count+=1;
            states_r.insert(states_r.end(),states.begin(), states.end() );
           

         }

         

        }
   
        app* phi_right= construct_basic_str_ctr(m,all_vars_r, p_bound*rhs_vars.size(),q_bound,states_r); 
                                            
              
        app* phi_left= construct_basic_str_ctr(m,all_vars_l, p_bound*lhs_vars.size(),q_bound,states_l);  

       
    for(auto ex:int_vars){
            
                   ctx.internalize(ex, false); 
                    SASSERT(ctx.get_enode(ex) != NULL); 
                    SASSERT(ctx.e_internalized(ex)); 
                    enode* nex = ctx.get_enode(ex);

                    ctx.mark_as_relevant(nex);
            

            }
                mk_product( all_vars_l,   all_vars_r , states_l, states_r);


    }


        void theory_atlas::mk_product(
        std::vector<std::pair<expr_ref, expr_ref>> all_vars_l, 
        std::vector<std::pair<expr_ref, expr_ref>> all_vars_r ,
        std::vector<std::pair<std::string, std::string>> states_l,
        std::vector<std::pair<std::string, std::string>> states_r){



        std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>> product_vars;
        std::vector<std::pair<std::string,std::string>> p;
      
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        std::vector<std::string> reachable2;
        std::vector<std::pair<std::string, std::string>> reachable;
      
        std::string initial_s= states_l[0].first+states_r[0].first;
        std::string final_s= states_l[states_l.size()- q_bound].first+states_r[states_r.size()- q_bound].first;
        reachable.push_back(std::make_pair(states_l[0].first,states_r[0].first));
        reachable2.push_back(initial_s);


        std::vector<std::pair<std::string, std::string>> p_states;
        unsigned  c=0, k=0;
       
             // (p,v,q )in T_l, (p',v', q') in t_r ==> ((p,p'), (v, v'), (q,q')) T_p

            while( k<states_l.size()){
                c+=1;
                for(unsigned j=0; j<states_r.size(); j++){
                    

                      for(unsigned  i =0; i<reachable.size(); i++){
                        if (states_l[k].first == reachable[i].first
                         && states_r[j].first == reachable[i].second 
                         && !contains_elt({states_l[k].second,states_r[j].second}, reachable)
                        )
                        {
                             reachable.push_back(std::make_pair(states_l[k].second,states_r[j].second));
                             std::string ss= states_l[k].second+ states_r[j].second;
                             reachable2.push_back(ss);
                      
                            
                            
                        }
                      }
                }
                if (c == states_l.size()-1 )k=0;
                else k=k+1;
        
                if (c== states_l.size())  k=states_l.size();
            }
                    



    for(unsigned k=0; k<all_vars_l.size(); k++){
         expr_ref sum=zero;
        for(unsigned j=0; j<all_vars_r.size(); j++){ 
            
                if (contains_elt(states_l[k].first+states_r[j].first, reachable2)){
                    std::pair<expr_ref, expr_ref> i_var=std::make_pair(all_vars_l[k].first, all_vars_r[j].first);

                    expr_ref p_pro(mk_fresh_const("pk", int_sort, k, j), m);
                    ensure_enode(p_pro);
                    pk_vars.push_back(p_pro);
                    if(!contains_elt( p_pro,pp_vars)) pp_vars.push_back(p_pro);

                    axioms.push_back(m_util_a.mk_ge(p_pro, zero));

                    product_vars.push_back(std::make_pair(i_var,p_pro));
                    p_states.push_back(std::make_pair(states_l[k].first+states_r[j].first, states_l[k].second+states_r[j].second));
                    /*
                                phi_=
                    */
                    
                if(expr2str(i_var.first) != "ep" || expr2str(i_var.second) != "ep"){
                     axioms.push_back(m.mk_or(m.mk_not(m_util_a.mk_ge(p_pro, one)), m_util_a.mk_eq(i_var.first, i_var.second)));
              
                }
                   
                   if ( expr2str(all_vars_l[k].first)  != "ep")
                   {   
                       sum= m_util_a.mk_add(sum, p_pro);

                  }
                  if  (expr2str(all_vars_r[j].first)  != "ep"){

                      expr_ref e(m);
                      
                      int i= contains_elt(all_vars_r[j].second, phi_sharp );
                       if (i==-1)
                                {        
                               phi_sharp.push_back({all_vars_r[j].second,p_pro});
                                }
                        
                       
                        else{
                            expr_ref e(m);
                            expr_ref aux(m);
                             phi_sharp[i].second=m_util_a.mk_add(phi_sharp[i].second,p_pro) ;
                            
                        } 
                  }
    
 
                          

          } 
                }
                if  ( expr2str(all_vars_l[k].first)  != "ep"){
                               axioms.push_back(m_util_a.mk_eq(all_vars_l[k].second,sum));
            }


         
        }


                 

       for (auto elt: phi_sharp){
                axioms.push_back(m_util_a.mk_eq(elt.first, elt.second));
       }
        
       

       



      
      unsigned idx=0;
     /* for(auto elt: reachable2){

          expr_ref var_b(mk_fresh_const('u'+std::to_string(idx), int_sort), m);
                           
        axioms.push_back(m_util_a.mk_eq(var_b,m_util_a.mk_numeral(rational(idx), true)));
        st_map.insert({elt, var_b});
                         
        idx+=1;
      }*/

   

        parikh_img(m, p_states, product_vars, reachable2, final_s);

        for (auto elt: axioms){
            add_axiom(elt);
        }

       /*int_expr_solver ies(m, get_fparams());
        ies.initialize(ctx);
        lbool result = ies.check_sat(axioms);     

        if (result == l_true){

          print_model(ies.get_context());
  
        }*/
          

        }



    void theory_atlas::parikh_img(ast_manager& m, 
                std::vector<std::pair<std::string, std::string>> p_states,
                std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>> prod_vars,
                std::vector<std::string> st, 
                std::string final_s)
{
        
        expr_ref zero(m);
        expr_ref one(m);
        expr_ref mone(m);
                  
        zero = m_util_a.mk_numeral(rational(0), true);
        SASSERT(zero);
        one = m_util_a.mk_numeral(rational(1), true);
        mone = m_util_a.mk_numeral(rational(-1), true);
        expr_ref lpp(m);
        std::vector<app*> p_form;
        std::vector<std::string> stt;
    
        
        
        for( unsigned k=0; k<st.size(); k++ ){
          
           // ptr_vector<expr>  conn;
           expr_ref in_t=zero; 
           expr_ref  out_t=zero;
            unsigned j=0;
            bool lp_b=false;
                while( j < p_states.size()){
                    if(st[k] == p_states[j].first )///outgoing
                        { 
                            out_t = m_util_a.mk_add(out_t,prod_vars[j].second);
                    }else if(st[k] == p_states[j].second){///incoming
                            in_t = m_util_a.mk_add(in_t,prod_vars[j].second);
                            /************ CONNECTEDNESS  *************/
                            expr_ref aux2(m);
                        
                        /* if( st_map.find(st[k]) != st_map.end())
                       {
                            aux2=st_map.at(st[k]);  
                            conn.push_back( m.mk_or(m_util_a.mk_eq(prod_vars[j].second, zero),
                            m_util_a.mk_ge(get_in_state_index(prod_vars[j].second, prod_vars, p_states), 
                                            aux2)));
                           }*/
                           

                        
                        
                    }   
                   /* if(st[k] == p_states[j].first && st[k] == p_states[j].second ){//loops
                    lpp= prod_vars[j].second;

                        lp_b= true;
                         }*/
                    j=j+1;
                   
                }
          /* if(conn.size() != 0){
               app* ee= m_util_a.mk_eq(in_t, zero) ;
           app* er=m.mk_not(m.mk_and(conn));
            axioms.push_back(m.mk_or(ee,er));
        
          
           }*/
          

        /******* FLOW CONSISTENCY   ***************/

        if (k ==0){
                axioms.push_back( m_util_a.mk_eq(
                   m_util_a.mk_add(
                       out_t, m_util_a.mk_uminus(in_t)), one))  ;
              
        }
        else if (st[k]== final_s )
            {

                 axioms.push_back(m_util_a.mk_eq(m_util_a.mk_add(out_t, m_util_a.mk_uminus(in_t)), mone))  ;

            }             
        else  
                   {  axioms.push_back(m_util_a.mk_eq(out_t ,in_t));

                   }

      
 }
                                    


        SASSERT(one);
      
        

           
              
}
 
    
  app* theory_atlas::construct_basic_str_ctr(
        ast_manager& m,
        std::vector<std::pair<expr_ref, expr_ref>> vars,
        unsigned l_bound,
        unsigned s_bound,
        std::vector<std::pair<std::string, std::string>> states){

        context& ctx=get_context();
        app * res     = m.mk_true();
        app * p_res     = m.mk_true();

        expr_ref print_char_min(m);
        expr_ref print_char_max(m);
        expr_ref parikh_val_bound(m);
        expr_ref one(m);
         expr_ref empty_char(m);
        one = m_util_a.mk_numeral(rational(1), true);
        parikh_val_bound= m_util_a.mk_numeral(rational(2), true);
        empty_char= m_util_a.mk_numeral(rational(32), true);
        unsigned min=0, max=0, new_s=q_bound/cut_size;
        for(unsigned k=0; k<cut_size;k++) min=PRINT_CHAR_MIN*pow(10, 2*k)+min;
        for(unsigned k=0; k<cut_size;k++) max=PRINT_CHAR_MAX*pow(10, 3*k)+max;
        print_char_min = m_util_a.mk_numeral(rational(min), true);
        print_char_max = m_util_a.mk_numeral(rational(max), true);
               
        // PRINTABLE CHAR INTERVAL
                

        for(auto& v: vars){
        if(!contains_elt(v.first,cst_vars)){   

        app* gt_min = m_util_a.mk_ge(v.first,print_char_min);  

        app* le_max = m_util_a.mk_le(v.first,print_char_max);  
        app* empty_s= m_util_a.mk_eq(v.first, empty_char);
     //    axioms.push_back(m.mk_or(m.mk_and(gt_min, le_max), empty_s));
       //  axioms.push_back(m_util_a.mk_le(v.second, parikh_val_bound));
       //   axioms.push_back(le_max );
         // axioms.push_back(gt_min );
         if (expr2str(v.first) == "ep"){
              axioms.push_back(m_util_a.mk_eq(v.first, empty_char));

         }else{
         axioms.push_back(m.mk_or(gt_min,empty_s ) );

         axioms.push_back(m.mk_or(le_max,empty_s ) );

         }
       // res = m.mk_and(res,le_max);       
        }
        }
        
        // vars in the same loop have same parikh image
          
       // for(unsigned j=0;  j= (j== 0)? j+new_s: j+1+new_s){ 
                   

            unsigned j=0;
              if(new_s>1){
            while(j<vars.size()){
                                            

            app * ex     = m.mk_true(); 
            

            if(stoi(states[j].first.substr(states[j].first.find("q")+1, states[j].first.size()-1))%q_bound == 0 
            && stoi(states[j].second.substr(states[j].second.find("q")+1, states[j].second.size()-1))%q_bound == 0
            ){                            


            app* eq1= m_util_a.mk_eq(vars[j].second, one);
             axioms.push_back(eq1); 
            j++;


            }
            else{               
              

                for(unsigned k=1; k<new_s; k++){
               if(j+k < vars.size()){
                app* eq=m_util_a.mk_eq(vars[j].second,vars[j+k].second);
                 axioms.push_back(eq);


               } 
            }             
                    j=j+new_s;
            }
               
                            


            //p_res=m.mk_and(p_res, ex);
         /*   if(j+new_s-1 <vars.size()){
                app* eq1= m_util_a.mk_eq(vars[j+new_s-1].second, one);
               

             res=m.mk_and(ex, eq1);        

            }  */
            
        }}
                      
                            


        return res;
    }

    /*  app* theory_atlas::construct_basic_str_ctr(
        ast_manager& m,
        std::vector<std::pair<expr_ref, expr_ref>> vars,
        unsigned l_bound,
        unsigned s_bound){
        context& ctx=get_context();
        app * res     = m.mk_true();
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
*/
    std::vector<std::pair<expr_ref,expr_ref>>  theory_atlas:: mk_fresh_vars(expr_ref str_v, std::string s){
         

        SASSERT(cut_size % q_bound !=0);
        /* cut variables according to cut_sizeize , if =1 ==> original algo */
        std::vector<std::pair<expr_ref, expr_ref>> res;
        ast_manager &m = get_manager();
        context &ctx = get_context();


        unsigned k=0;
        unsigned new_s=q_bound/cut_size;
        for(unsigned j=0;j<p_bound;j++){

            while(k<new_s){
                    expr_ref ex (mk_fresh_const(s, int_sort, j,k), m);
                    expr_ref ex_p(mk_fresh_const(s, int_sort, k, j), m);
                    ctx.internalize(ex, false);
                    SASSERT(ctx.get_enode(ex) != NULL);
                    SASSERT(ctx.e_internalized(ex));
                    ctx.internalize(ex_p, false);
                    SASSERT(ctx.get_enode(ex_p) != NULL);
                    SASSERT(ctx.e_internalized(ex_p));

                    res.push_back(std::make_pair(ex,ex_p));

            }


                    expr_ref ex (mk_fresh_const(s, int_sort, j), m);
                    expr_ref ex_p(mk_fresh_const(s, int_sort,j), m);
                    ctx.internalize(ex, false);
                    SASSERT(ctx.get_enode(ex) != NULL);
                    SASSERT(ctx.e_internalized(ex));
                    ctx.internalize(ex_p, false);
                    SASSERT(ctx.get_enode(ex_p) != NULL);
                    SASSERT(ctx.e_internalized(ex_p));
                    res.push_back(std::make_pair(ex,ex_p));
         
        

        }

        return res;

         


    }
    
    std::vector<std::pair<expr_ref,expr_ref>>  theory_atlas::init_int_vars(
        unsigned p,
        std::string s,
        std::vector<std::pair<std::string, std::string>> *states){
        std::vector<std::pair<expr_ref, expr_ref>> res;

     //  if(find_var_by_label(int_vars, s))

        ast_manager &m = get_manager();
        SASSERT(q_bound%cut_size == 0);
        unsigned new_q_bound=q_bound/cut_size ;
        unsigned num_states = (new_q_bound+1)*p_bound-1,sr,d, lp=0, a=0;
        unsigned  st=0;
        for(unsigned k=0; k< p_bound; k++){
        unsigned s0=k*new_q_bound;
        unsigned j=0;
           while( j<new_q_bound-1){

            (*states).push_back(std::make_pair(s+"q"+std::to_string(s0+j),s+"q"+std::to_string(s0+j+1)));
           // s0++;
            j++;
           }
           (*states).push_back(std::make_pair(s+"q"+std::to_string(j+st),s+"q"+std::to_string(s0)));
           st+=new_q_bound;
         if(k<p_bound-1) {
                      (*states).push_back(std::make_pair(s+"q"+std::to_string(k*new_q_bound),s+"q"+std::to_string(k*new_q_bound+new_q_bound)));

         } 

        }


        for(int k=0; k< num_states; k++){

        std::string ss=s+ (*states)[k].first.substr((*states)[k].first.find("q")+1, (*states)[k].first.size()-1)+(*states)[k].second.substr((*states)[k].first.find("q")+1, (*states)[k].first.size()-1);        
        expr_ref ex (mk_fresh_const(ss, int_sort), m);
        std::string s_p= ss+"p";     
        expr_ref ex_p(mk_fresh_const(s_p, int_sort), m);
      
        res.push_back(std::make_pair(ex,ex_p));
         
        int_vars.push_back(ex);
        int_vars.push_back(ex_p);
        
        }
  

        return res;
    }


    app *theory_atlas::mk_fresh_const(std::string name, sort *s, unsigned k, unsigned l)
    {
        string_buffer<64> buffer;

        for(int j=0; j<name.size();j++){
            buffer << name[j];
        }  
        buffer << "!tmp";
        buffer << k;
        buffer << l;

        m_fresh_id++;
        
        return m_util_s.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }
    
        app *theory_atlas::mk_fresh_const(std::string name, sort *s, unsigned k)
    {

        string_buffer<64> buffer;

        for(int j=0; j<name.size();j++)  buffer << name[j];
        buffer << "!te";
        buffer << k;


       // buffer << "!tmp";
       // buffer << m_fresh_id;
        m_fresh_id++;
        return m_util_s.mk_skolem(symbol(buffer.c_str()), 0, nullptr, s);
    }

     app *theory_atlas::mk_fresh_const(std::string var_name, sort *s)
    {
       symbol(name);

       m_fresh_id++;
        return m_util_s.mk_skolem(symbol(var_name), 0, nullptr, s);
    }
    ptr_vector<expr> theory_atlas::get_int_vars_from_aut(pautomaton* aut, unsigned s){

        ptr_vector<expr> result;

        for(unsigned j=0; j< s; j++)
        {

            aut->get_moves_from(j);

        }
        //return nullptr;
    }
    
    void theory_atlas::get_nodes_in_concat(expr * node, ptr_vector<expr> & nodeList) {
                 

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
    void theory_atlas::handle_word_diseq(expr_ref lhs, expr_ref rhs){

         

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


    }


    void theory_atlas::propagate_concat_axiom(enode *cat) {
                 

        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen = false;


        app *a_cat = cat->get_expr();
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

    void theory_atlas::propagate_basic_string_axioms(enode *str) {
 
        bool on_screen = false;

        context &ctx = get_context();
        ast_manager &m = get_manager();

        {
            sort *a_sort = str->get_expr()->get_sort();
            sort *str_sort = m_util_s.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str",
                       tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_expr(), m)
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
        app *a_str = str->get_expr();

        if (m_util_s.str.is_string(a_str)) {
            if (on_screen) std::cout << "[ConstStr Axiom] " << mk_pp(a_str, m) << std::endl;

            expr_ref len_str(m);
            len_str = m_util_s.str.mk_length(a_str);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_expr(), strconst);
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
                empty_str = m_util_s.str.mk_string("");
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

    void theory_atlas::add_length_axiom(expr *n) {
        
        add_axiom(m_util_a.mk_ge(n, m_util_a.mk_int(0)));

    }

    void theory_atlas::relevant_eh(app *const n) {

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
    void theory_atlas::enforce_length(expr *e) {
         
        enode *n = ensure_enode(e);
        enode *n1 = n;
        do {
            expr *o = n->get_expr();
            if (!has_length(o)) {
                expr_ref len = mk_len(o);
                add_length_axiom(len);
            }
            n = n->get_next();
        } while (n1 != n);
    }

    void theory_atlas::assign_eh(bool_var v, const bool is_true) {
         
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

    void theory_atlas::new_eq_eh(theory_var x, theory_var y) {
         
    
        m_word_eq_var_todo.push_back({x, y});

        const expr_ref l{get_enode(x)->get_expr(), m};
        const expr_ref r{get_enode(y)->get_expr(), m};

        if (axiomatized_eq_vars.count(std::make_pair(x, y)) == 0) {
            axiomatized_eq_vars.insert(std::make_pair(x, y));
            literal l_eq_r = mk_eq(l, r, false);
            literal len_l_eq_len_r = mk_eq(m_util_s.str.mk_length(l), m_util_s.str.mk_length(r), false);
            app* exprr= m_util_a.mk_eq(m_util_s.str.mk_length(l), m_util_s.str.mk_length(r));

            add_axiom({~l_eq_r, len_l_eq_len_r});
           // m_int_eq_todo.push_back(exprr);

                    

        }
        /*add len constraint

        */
                
        if(!contains_elt({l, r}, m_word_eq_todo)) m_word_eq_todo.push_back({l, r});
        m_word_eq_todo2.push_back({l, r});
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

    void theory_atlas::new_diseq_eh(theory_var x, theory_var y) {
         
        m_word_diseq_var_todo.push_back({x, y});
        
        ast_manager &m = get_manager();
        const expr_ref l{get_enode(x)->get_expr(), m};
        const expr_ref r{get_enode(y)->get_expr(), m};

        m_word_diseq_todo.push_back({l, r});
        STRACE("str", tout << "new_diseq: " << l << " != " << r << '\n';);

        
               
        //handle_word_diseq(l, r);
       // m_word_diseq_todo.pop_back();


    }

    bool theory_atlas::can_propagate() {
         
        return false;
    }

    void theory_atlas::propagate() {
         
        STRACE("str", if (!IN_CHECK_FINAL) tout << "propagate" << '\n';);
            /*
           for (auto const& we  : m_word_eq_todo) {
                const expr_ref  lhs = we.first;
                const expr_ref  rhs = we.second;
                

               // handle _word_e q(lhs, rhs);

            
            }
            */
    }




    void theory_atlas::push_scope_eh() {
         
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

    void theory_atlas::pop_scope_eh(const unsigned num_scopes) {

            
       // std::cout<<"current scope"<< num_scopes <<"\n";
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

    void theory_atlas::reset_eh() {
         
        STRACE("str", tout << "reset" << '\n';);
    }



    zstring theory_atlas::print_word_term(expr * e) const{
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

        std::vector<expr*> theory_atlas::get_vars(expr * e) const{

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
                //if(!contains_elt(e, vars)) vars.push_back(e);
                lst1.push_back(e);

                return lst1;


        }


        zstring theory_atlas::print_vars(expr * e) const{

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

    expr* theory_atlas::get_vars(expr * e, ptr_vector<expr> lst) const{
               // ptr_vector<expr> ex;
               zstring s;
                if (m_util_s.str.is_string(e, s)) {
                    return nullptr;               
                }
                if (m_util_s.str.is_concat(e)) {
                    //e is a concat of some elements
                    for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                        lst.push_back(get_vars(to_app(e)->get_arg(i), lst));


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


    final_check_status theory_atlas::final_check_eh() {

       
        if (m_word_eq_todo.empty() ) {
            

            str_solver_checked = true;
            ctx.push_trail(value_trail<bool>(str_solver_checked));

            if(is_undeapp_over){
            arith_value v(get_manager());
            v.init(&ctx);
            final_check_status arith_fc_status = v.final_check();
            //v.get_fixed 
            //v.get_value

            if (arith_fc_status == FC_DONE  ) {
                std::cout<<"Arithmetic solver Done \n";
                if(ctx.inconsistent()){
                    std::cout<<" && Context is inconsistent \n";
                  
                            return FC_CONTINUE;
                }
                else{
                   std::cout<<"&&  context is consistent()\n";
                   context&  arith_ctx= ctx.get_theory(m_util_a.get_family_id())->get_context(); 
                  // arith_ctx.display_assignment(std::cout);
                  // arith_ctx.display(std::cout);
                   return FC_DONE;
                }

            }else{
                    std::cout << FC_GIVEUP <<"\n";

    
                        TRACE("str", tout << "arithmetic solver not done yet, continuing search" << std::endl);

                //done doesnt mean sat: it means sat/or unsat
               // case : sat : done 
               //case:unsat : block_curr_assigneemnt
                
                return FC_GIVEUP;
            }

        }

        
        }
        
        else{


             if(m_int_eq_todo.empty())// check for new integer constaint; ==> if the overapprox is over or not== > underapprox
            {


                is_over_approximation=false;
                 //Handle word eq, underAproxx
                 for (const auto& we : m_word_eq_todo) {
                        handle_word_eq(we.first, we.second);
                       m_word_eq_todo.pop_back();

                    }  
              /*  expr_ref one(m_util_a.mk_int(34), m);
                expr_ref ex (mk_fresh_const("test", int_sort), m);
                ctx.internalize(ex, false); 
                SASSERT(ctx.get_enode(ex) != NULL); 
                SASSERT(ctx.e_internalized(ex)); 
                enode* nex = ctx.get_enode(ex);
                ctx.mark_as_relevant(nex);
                expr_ref ex1 (mk_fresh_const("test1", int_sort), m);
                ctx.internalize(ex1, false); 
                SASSERT(ctx.get_enode(ex1) != NULL); 
                SASSERT(ctx.e_internalized(ex1)); 
                enode* nex1 = ctx.get_enode(ex1);
                ctx.mark_as_relevant(nex1);
                expr_ref ex2 (mk_fresh_const("test2", int_sort), m);
                ctx.internalize(ex2, false); 
                SASSERT(ctx.get_enode(ex2) != NULL); 
                SASSERT(ctx.e_internalized(ex2)); 
                enode* nex2 = ctx.get_enode(ex);
                ctx.mark_as_relevant(nex2);
                app* eq1= m_util_a.mk_eq(ex, ex2);
                app* eq2= m_util_a.mk_eq(m_util_a.mk_add(ex, ex2), ex1);
                app* eq3= m_util_a.mk_eq(ex1, one);
                 axioms.push_back(eq1);
                 axioms.push_back(eq2);
                  axioms.push_back(eq3);
                int_vars.push_back(ex);
                                int_vars.push_back(ex1);
                int_vars.push_back(ex2);
             arith_value v(get_manager());

            v.init(&ctx);
        
            final_check_status arith_fc_status = v.final_check();
            if (arith_fc_status != FC_DONE) {

                 
                TRACE("str", tout << "arithmetic solver not done yet, continuing search" << std::endl;);

                return FC_CONTINUE;
            }else{

                
                return FC_DONE;
            }*/
            }
          /*  else{
            /// handle the rest of the constraints ,Over Approxx
                    for (const auto& we : m_word_eq_todo2) {         
                        handle_word_eq(we.first, we.second);
                    }
                return FC_CONTINUE;
            }*/
           
            
        }
    
       // block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
        IN_CHECK_FINAL = false;
        return FC_CONTINUE;
    }

    model_value_proc *theory_atlas::mk_value(enode *const n, model_generator &mg) {


          /*    
             app* tgta=nullptr;
             app *const tgt = n->get_expr();
               for(obj_map<expr,std::string> ::iterator it2 = model.begin(); it2 != model.end(); ++it2){
          if(m.are_equal(tgt, &((*it2).get_key()))) {
              zstring st((*it2).get_value().data()); 
                 tgta=  to_app(mk_string(st));

          }
               }
     /*   for (auto elt: model){


             if( m.are_equal(n->get_expr(), elt.first)){
                 
                 zstring st(elt.second.data()); 
                 tgta=  to_app(mk_string(st));
                     


             }
            // else  return alloc(expr_wrapper_proc, tgt);
          }


        if(tgta !=nullptr ) return alloc(expr_wrapper_proc, tgta);
        else  return alloc(expr_wrapper_proc, tgt);
*/
              

        family_id afid = m_util_a.get_family_id(); 
        app* tgta=nullptr;
        expr_ref_vector assignments{m};
        expr_ref_vector reslt{m};
        ctx.get_assignments(assignments);
        arith_value v(m);
        v.init(&ctx);
        context&  arith_ctx= ctx.get_theory(m_util_a.get_family_id())->get_context();
        app* value = nullptr;
        
       /* for(auto elt: pp_vars){
            rational val; 
            rational val2;
            
             //m_util_a.is_numeral(root_e->get_expr(), val)  ;            
             

            

             // theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, elt);

              //model_value_proc* tmp = tha->mk_value(arith_ctx.get_enode(elt), mg);
              // value = tmp->mk_value(mg, assignments);
              
              
                                  /* if(get_arith_value(elt,val))  std::cout<<"\n";
                     else{                 

                          app* value = nullptr;             


                            value=ctx.get_theory(m_util_a.get_family_id())->mk_value(ctx.get_enode(elt),mg)->mk_value(mg, assignments);
                            m_util_a.is_numeral(value, val);// && val.is_int())                 

                       }
       }*/
                 
            for(obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> ::iterator it = fresh_int_vars.begin(); it != fresh_int_vars.end(); ++it){
               expr_ref e(m);
               if(m.are_equal(n->get_expr(),&((*it).get_key()))){                
                     tgta= construct_string_from_int_array((*it).get_value(), mg);
                   }

            }
   
       

        theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, n->get_expr());
   
        
        app *const tgt = n->get_expr();
        
        (void) m;
        STRACE("str", tout << "mk_value: sort is " << mk_pp(tgt->get_sort(), m) << ", "
                           << mk_pp(tgt, m) << '\n';);

     rational val;
  
   

       /* for(unsigned k=0; k<int_vars.size(); k++){

          if( int_vars[k]->get_sort() == int_sort){
           SASSERT(ctx.get_enode(int_vars[k])!= NULL );
            rational val;
               
            else{
                app* value = nullptr;

                 value=ctx.get_theory(m_util_a.get_family_id())->mk_value(ctx.get_enode(int_vars[k]),mg)->mk_value(mg, assignments);
                 if(m_util_a.is_numeral(value, val) && val.is_int())
            }

            }
                    
           }*/
        if(tgta !=nullptr ) return alloc(expr_wrapper_proc, tgta);
        else  return alloc(expr_wrapper_proc, tgt);
        
    }

    void theory_atlas::init_model(model_generator &mg) {
         
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init_model\n";);
    }

    void theory_atlas::finalize_model(model_generator &mg) {
         
        STRACE("str", if (!IN_CHECK_FINAL) tout << "finalize_model\n";);
    }

    lbool theory_atlas::validate_unsat_core(expr_ref_vector &unsat_core) {
         
        return l_undef;
    }

    bool theory_atlas::is_of_this_theory(expr *const e) const {
         
        return is_app(e) && to_app(e)->get_family_id() == get_family_id();
    }

    bool theory_atlas::is_string_sort(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_atlas::is_regex_sort(expr *const e) const {
        return m_util_s.is_re(e);
    }

    bool theory_atlas::is_const_fun(expr *const e) const {
        return is_app(e) && to_app(e)->get_decl()->get_arity() == 0;
    }

    expr_ref theory_atlas::mk_sub(expr *a, expr *b) {
        ast_manager &m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }
    // check if scoped vector contains elt 
    int theory_atlas::contains_elt(expr_ref elt, std::vector<std::pair<expr_ref, expr_ref>>vec)
    {
        ast_manager& m = get_manager();

        for (unsigned j=0; j< vec.size(); j++){
            if(m.are_equal(vec[j].first, elt) ) {
               // *i=j;
                return j;
            }
        }
    return -1;

    }
    bool theory_atlas::contains_elt(app* elt, scoped_vector<app*> vec) {
        ast_manager& m = get_manager();

        for (app* app_elt :  vec){
            if(m.are_equal(app_elt, elt) ) return true;
        }
    return false;
    }
    bool theory_atlas::contains_elt(app* elt, obj_map <expr_ref, expr_ref> vec){
        
    for(obj_map<expr_ref,expr_ref> ::iterator it = vec.begin(); it != vec.end(); ++it){

         
            if( m.are_equal((*it).get_key(), elt))
            {
            return true;
            }
        }
        
        return false;
    }
    bool theory_atlas::contains_elt(expr_ref elt, obj_map <expr_ref, expr_ref> vec){
        
    for(obj_map<expr_ref,expr_ref> ::iterator it = vec.begin(); it != vec.end(); ++it){

         
            if( m.are_equal((*it).get_key(), elt))
            {
            return true;
            }
        }
        
        return false;
    }
    bool contains_elt(std::string elt,
            obj_map <std::string, expr_ref> vec){


          for(obj_map<std::string,expr_ref> ::iterator it = vec.begin(); it != vec.end(); ++it){

         
            if( (*it).get_key()== elt)
            {
            return true;
            }
        }
        
        return false;

            }
     bool theory_atlas::contains_elt(std::pair<std::string, std::string>pr, std::vector<std::pair<std::string, std::string>> vec) {
        ast_manager& m = get_manager();

        for (auto elt :  vec){
            if(pr.first == elt.first and pr.second == elt.second ){
                return true;
            } 
        }
    return false;
    }
     bool theory_atlas::contains_elt(std::string elt, std::vector<std::string> vec) {

        for (std::string v_elt :  vec){
            if(v_elt == elt ) return true;
        }
    return false;
    }
    bool theory_atlas::contains_elt(app* elt, obj_map<expr_ref, 
    std::vector<std::pair<expr_ref, expr_ref>>> vec) {

         for( obj_map<expr_ref, std::vector<std::pair<expr_ref, expr_ref>>> ::iterator it = vec.begin(); it != vec.end(); ++it){

         
            if( (*it).get_key()== elt)
            {
            return true;
            }
         }
    return false;
    }
    
    bool theory_atlas::contains_elt(app* elt, std::vector<app*> vec){
        ast_manager& m = get_manager();

        for (app* app_elt :  vec){
            if(m.are_equal(app_elt, elt) ) return true;
        }
    return false;
    }
      bool theory_atlas::contains_elt(expr_ref elt, std::vector<expr_ref> vec){
        ast_manager& m = get_manager();

        for (auto app_elt :  vec){
            if(m.are_equal(app_elt, elt) ) return true;
        }
    return false;
    }

    bool theory_atlas::contains_elt(expr_pair elt, scoped_vector<expr_pair> vec){
        ast_manager& m = get_manager();

        for (auto p_elt :  vec){
            if(m.are_equal(elt.first, p_elt.first) &&m.are_equal(elt.second, p_elt.second) ) return true;
        }
    return false;
    }
     bool theory_atlas::contains_elt(expr_ref elt, scoped_vector<expr_ref> vec) {
        ast_manager& m = get_manager();

        for (expr_ref app_elt :  vec){
            if(m.are_equal(app_elt, elt) ) return true;
        }
    return false;
    }
       bool theory_atlas::contains_elt(expr* elt, scoped_vector<expr*> vec) {
        ast_manager& m = get_manager();

        for (expr* expr_elt :  vec){
            if(m.are_equal(expr_elt, elt) ) return true;
        }
    return false;
    }
    bool theory_atlas::contains_elt(expr* elt,
     obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> vec,
     std::vector<std::pair<expr_ref, expr_ref>> *vars) {
        ast_manager& m = get_manager();

        for (auto expr_elt :  vec){
            if( m.are_equal( &(expr_elt.get_key()), elt))
            {
                (*vars).insert((*vars).end(), expr_elt.get_value().begin(), expr_elt.get_value().begin());
            return true;
            }
        }
    return false;
    }


    expr_ref theory_atlas::mk_skolem(symbol const &name, expr *e1, expr *e2, expr *e3, expr *e4, sort *sort) {
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

    literal theory_atlas::mk_literal(expr *const e) {
         
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

    bool_var theory_atlas::mk_bool_var(expr *const e) {
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



    void theory_atlas::add_axiom(expr *const e) {
         
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
           
            literal l{ctx.get_literal(e)};

            ctx.mark_as_relevant(l);

            ctx.mk_th_axiom(get_id(), 1, &l);
            
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }

    }
    void theory_atlas::add_axiom_arith(expr *const e) {
        bool on_screen = true;
        STRACE("str_axiom", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

        if (on_screen) STRACE("str_axiom",
                              std::cout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

        if (!axiomatized_terms.contains(e) || false) {

            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
            context &ctx = get_context();

//        SASSERT(!ctx.b_internalized(e));
            if (!ctx.b_internalized(e)) {

                ctx.internalize(e, false);
            }


            ctx.internalize(e, false);

           
            literal l{ctx.get_literal(e)};

            ctx.mark_as_relevant(l);

            ctx.mk_th_axiom(m_util_a.get_family_id(), 1, &l);
            
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }

    }

    void theory_atlas::add_axiom(std::initializer_list<literal> ls) {
         
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
        ctx.mk_th_axiom(get_id(), lv.size(), lv.data());
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
    void theory_atlas::handle_char_at(expr *e) {
        

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
    void theory_atlas::handle_substr(expr *e) {
        
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
    void theory_atlas::handle_replace(expr *r) {
        
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
    void theory_atlas::handle_index_of(expr *i) {
        
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

    void theory_atlas::tightest_prefix(expr* s, expr* x) {
        
        expr_ref s1 = mk_first(s);
        expr_ref c  = mk_last(s);
        expr_ref s1c = mk_concat(s1, m_util_s.str.mk_unit(c));
        literal s_eq_emp = mk_eq_empty(s);
        add_axiom({s_eq_emp, mk_eq(s, s1c,true)});
        add_axiom({s_eq_emp, ~mk_literal(m_util_s.str.mk_contains(mk_concat(x, s1), s))});
    }

    expr_ref theory_atlas::mk_first(expr* s) {
         
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_string(str.extract(0, str.length()-1)), m);
        }
        return mk_skolem(symbol("seq_first"), s);
    }

    expr_ref theory_atlas::mk_last(expr* s) {
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_char(str, str.length()-1), m);
        }
        sort* char_sort = nullptr;
        VERIFY(m_util_s.is_seq(s->get_sort(), char_sort));
        return mk_skolem(symbol("seq_last"), s, nullptr, nullptr, nullptr, char_sort);
    }

    expr_ref theory_atlas::mk_concat(expr* e1, expr* e2) {
         
        return expr_ref(m_util_s.str.mk_concat(e1, e2), m);
    }

    literal theory_atlas::mk_eq_empty(expr* _e, bool phase) {
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
    void theory_atlas::handle_prefix(expr *e) {
        
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
    void theory_atlas::handle_not_prefix(expr *e) {

        
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
    void theory_atlas::handle_suffix(expr *e) {
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
    void theory_atlas::handle_not_suffix(expr *e) {
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
    void theory_atlas::handle_contains(expr *e) {
        
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

    void theory_atlas::handle_in_re(expr *const e, const bool is_true) {
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

    void theory_atlas::set_conflict(const literal_vector& lv) {
         
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx.get_region(), lv.size(), lv.data(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE("str", ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_atlas::block_curr_assignment() {
         
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
            std::cout << we.first << " = " << we.second << '\n';
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
   
    void theory_atlas::dump_assignments() const {
         
        ast_manager& m = get_manager();
        context& ctx = get_context();
        expr_ref_vector assignments{m};
        ctx.get_assignments(assignments);
        STRACE("str", \
                
                std::cout << "dump all assignments:\n";
                expr_ref_vector assignments{m};


                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                   // ctx.mark_as_relevant(e);
                    std::cout <<"**"<< mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
                
                for (expr *const e : assignments) {
                    if( e->get_sort()==int_sort){
                        expr_ref not_e(m.mk_not(e),m);
                        ctx.mark_as_relevant(m.mk_not(e));
                    }
                    else{

                        expr_ref not_e(m.mk_not(e),m);

                        ctx.mark_as_relevant(m.mk_not(e));
                    }
                }
    }


      /* model_value_proc * theory_atlas::mk_value(enode * n, model_generator & mg) {


        TRACE("str", tout << "mk_value for: " << mk_ismt2_pp(n->get_expr(), get_manager()) <<
              " (sort " << mk_ismt2_pp(n->get_expr()->get_sort(), get_manager()) << ")" << std::endl;);
        ast_manager & m = get_manager();
        app_ref owner(m);

        owner = n->get_expr();


        // If the owner is not internalized, it doesn't have an enode associated.
        SASSERT(ctx.e_internalized(owner));    
        app * val = mk_value_helper(owner);

        if (val != nullptr) {
            return alloc(expr_wrapper_proc, val);         

        } else {
            TRACE("str", tout << "WARNING: failed to find a concrete value, falling back" << std::endl;);
            std::ostringstream unused;
            //unused << "**UNUSED**" << (m_unused_id++);
            return alloc(expr_wrapper_proc, to_app(mk_string(unused.str())));
        }

    }*/
    app * theory_atlas::mk_value_helper(app * n) {
         
        if (m_util_s.str.is_string(n)) {
            return n;
        } else if (m_util_s.str.is_concat(n)) {
            // recursively call this function on each argument
            SASSERT(n->get_num_args() == 2);
            expr * a0 = n->get_arg(0);
            expr * a1 = n->get_arg(1);

            app * a0_conststr = mk_value_helper(to_app(a0));
            app * a1_conststr = mk_value_helper(to_app(a1));

            if (a0_conststr != nullptr && a1_conststr != nullptr) {
                zstring a0_s, a1_s;
                m_util_s.str.is_string(a0_conststr, a0_s);
                m_util_s.str.is_string(a1_conststr, a1_s);
                zstring result = a0_s + a1_s;
                return to_app(mk_string(result));
            }
        }


        zstring assignedValue;
        if (candidate_model.find(n, assignedValue)) {
            return to_app(mk_string(assignedValue));
        }

        // fallback path
        // try to find some constant string, anything, in the equivalence class of n
        if (!candidate_model.empty()) {
            zstring val;
            if (candidate_model.find(n, val)) {
                return to_app(mk_string(val));
            }
        }
       
    }

    expr * theory_atlas::mk_string(zstring const& str) {
      
            return m_util_s.str.mk_string(str);
        
    }



     /*
     * Look through the equivalence class of n to find a string constant.
     * Return that constant if it is found, and set hasEqcValue to true.
     * Otherwise, return n, and set hasEqcValue to false.
     */

    expr * theory_atlas::get_eqc_value(expr * n, bool & hasEqcValue) {
        return z3str2_get_eqc_value(n, hasEqcValue);
    }

        // copied from z3 str3
    // Simulate the behaviour of get_eqc_value() from Z3str2.
    // We only check m_find for a string constant.

    expr * theory_atlas::z3str2_get_eqc_value(expr * n , bool & hasEqcValue) {
     
        return n;
    }
    theory_var theory_atlas::get_var(expr * n) const {
        if (!is_app(n)) {
            return null_theory_var;
        }
        if (ctx.e_internalized(to_app(n))) {
            enode * e = ctx.get_enode(to_app(n));
            return e->get_th_var(get_id());
        }
        return null_theory_var;
    }


    /*
            borrowed from trau with some modifications
    */

       expr* theory_atlas::query_theory_arith_core(expr* n, model_generator& mg){
            
        context& ctx = get_context();
        family_id afid = m_util_a.get_family_id();

        expr_ref_vector values(m);
        app* value = nullptr;
        do {


            theory_mi_arith* tha = get_th_arith<theory_mi_arith>(ctx, afid, n);
            if (tha) {        

                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }

            theory_i_arith* thi = get_th_arith<theory_i_arith>(ctx, afid, n);
            if (thi) {         
                
      

                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);
                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);
                value = tmp->mk_value(mg, values);
                break;
            }
            theory_lra* thr = get_th_arith<theory_lra>(ctx, afid, n);
            if (thr) {      

                
                STRACE("str", tout << __LINE__ << " " << __FUNCTION__ << " " << mk_pp(n, m) << std::endl;);   

                model_value_proc* tmp = tha->mk_value(ctx.get_enode(n), mg);  

                

                value = tmp->mk_value(mg, values);           
 
                

                break;
    

            }
            break;
        }

        while (false);
        

        return value;
    }

     app * theory_atlas::mk_strlen(expr * e) {
        app* tmp = m_util_s.str.mk_length(e);
        ensure_enode(tmp);
        return tmp;
    }

    bool theory_atlas::get_arith_value(expr* e, rational& val) const {
     
        context& ctx = get_context();
        if (!ctx.e_internalized(e)) {
            return false;
        }
        // check root of the eqc for an integer constant
        // if an integer constant exists in the eqc, it should be the root
        enode * en_e = ctx.get_enode(e);

        enode * root_e = en_e->get_root();
        if (m_util_a.is_numeral(root_e->get_expr(), val) && val.is_int()) {
            return true;
        } else {
            return false;
        }

    }

    app*  theory_atlas::construct_string_from_int_array(
        std::vector<std::pair<expr_ref, expr_ref>> int_varr,
         model_generator &mg){


            
            arith_value v(m);
            v.init(&ctx); 
            arith_value local_arith_value(m);
            local_arith_value.init(&ctx);

                std::stringstream ss;
             
                unsigned new_q_bound= q_bound/cut_size;
                unsigned k=1,j=0;
                expr_ref_vector assignments{m};
           for(auto elt:int_varr ){
               rational val; 
               get_arith_value(elt.second, val);
           }

            while(k<int_varr.size()){
                std::string res="";
                while(j<q_bound){   
                              

                     rational val;
                     if(get_arith_value(int_varr[j+k].first,val))  std::cout<<" \n";
                     else{   

                          v.get_value(int_varr[j+k].first,val);              
                          app* value = nullptr;  
                          expr_ref vall(m);           
                   //     local_arith_value.get_value(int_varr[j+k].first, val);

                                
                             // ctx.get_value(ctx.get_enode(int_varr[k].first),vall );
                         // value=ctx.get_theory(m_util_a.get_family_id())->mk_value(ctx.get_enode(int_varr[k].first),mg)->mk_value(mg, assignments) ;
                         // m_util_a.is_numeral(to_app(vall), val);// && val.is_int())  


                       }

                     char s= char(val.get_int64());  

                    if(s !=' ') res= res+s;
                    j++;  

                }
                rational val2 ;                  

                if(get_arith_value(int_varr[k].second,val2))    std::cout<<"\n";              

                     
                     else{
                          app* value = nullptr;                 
                        v.get_value(int_varr[k].second, val2);


                            //value=ctx.get_theory(m_util_a.get_family_id())->mk_value(ctx.get_enode(int_varr[k].second),mg)->mk_value(mg, assignments);
                         //   m_util_a.is_numeral(value, val2) ;//&& val2.is_int())
                       }

            for(unsigned i=0; i<val2; i++) ss << res;                 

           if(k<int_varr.size()-1){ 
               rational val3 ;                  

               
                if(get_arith_value(int_varr[k+1].first,val3))    std::cout<<"\n";

                     else{
                          app* value = nullptr;
                             v.get_value(int_varr[k+1].first, val3);

                           // value=ctx.get_theory(m_util_a.get_family_id())->mk_value(ctx.get_enode(int_varr[k+1].first),mg)->mk_value(mg, assignments);
                           // m_util_a.is_numeral(value, val3) ;//&& val3.is_int())
                       }
            char s= char(val3.get_int64());  
            if(s !=' ') ss <<s;

            }
            k=k+3;
            j=0;

            }
                

        zstring st(ss.str().data());  
        return to_app(mk_string(st));
       

    }
    void theory_atlas::print_assignement(){


            

    }
    std::vector<std::pair<expr_ref, expr_ref>>  theory_atlas::mk_newvar(zstring s,
    std::vector<std::pair<std::string, std::string>> *states){
         std::vector<std::pair<expr_ref, expr_ref>> res;
         unsigned new_q_bound= q_bound/cut_size, new_p=s.length() == 1 ? 1 : s.length()/new_q_bound;
         expr_ref one(m);
         one = m_util_a.mk_numeral(rational(1), true);
         std::string st;
            std::stringstream ss;
            ss <<s;
            st = ss.str().data();
         
         unsigned  stt=0;
            for(unsigned k=0; k<new_p; k++){
                    unsigned s0=k*new_q_bound;
                    unsigned j=0;
                while( j<new_q_bound-1){

                        (*states).push_back(std::make_pair(st+"q"+std::to_string(s0+j),st+"q"+std::to_string(s0+j+1)));
                    // s0++;
                        j++;
                }
                
                    (*states).push_back(std::make_pair(st+"q"+std::to_string(j+stt),st+"q"+std::to_string(s0)));
            

                    stt+=new_q_bound;
                    if(k<new_p-1) {

                    (*states).push_back(std::make_pair(st+"q"+std::to_string(k*new_q_bound),st+"q"+std::to_string(k*new_q_bound+new_q_bound)));
                    }
                     
        }
        
        
         unsigned len=s.length();


        for( unsigned k=0; k< (*states).size(); k++){
        std::string name=st.at(0)+ (*states)[k].first.substr((*states)[k].first.find("q")+1, (*states)[k].first.size()-1)+(*states)[k].second.substr((*states)[k].first.find("q")+1, (*states)[k].first.size()-1);        
        expr_ref ex (mk_fresh_const(name, int_sort), m);
        std::string s_p= name+"p";     
        expr_ref ex_p(mk_fresh_const(s_p, int_sort), m);
        res.push_back(std::make_pair(ex,ex_p));
        int_vars.push_back(ex);
        int_vars.push_back(ex_p);
        cst_vars.push_back(ex);
        
     

      //   axioms.push_back(m_util_a.mk_eq(ex_p, one));
        if(k<len){
              if(k!=0 && (k+1)% (new_q_bound+1)==0){
                      axioms.push_back(m_util_a.mk_eq(ex, m_util_a.mk_numeral(rational(int(32)), true)));
                   // len++;

             }else{

                         axioms.push_back(m_util_a.mk_eq(ex, m_util_a.mk_numeral(rational(int(st[k+s.length()-len])), true)));
             }
        }else{

             axioms.push_back(m_util_a.mk_eq(ex, m_util_a.mk_numeral(rational(int(32)), true)));

        }

         axioms.push_back(m_util_a.mk_eq(ex_p, m_util_a.mk_numeral(rational(1), true)));
        }
        
return res;

     }























std::vector<std::pair<expr_ref, expr_ref>>  theory_atlas::mk_newvar2(
        expr_ref elt, zstring s,
        std::vector<std::pair<std::string, std::string>> *states){


             

         ast_manager &m = get_manager();
         expr_ref ep(mk_fresh_const("ep", int_sort), m);
         std::vector<std::pair<expr_ref, expr_ref>> res;
         expr_ref one(m);
         one = m_util_a.mk_numeral(rational(1), true);
         std::string st;
            std::stringstream ss;
            ss <<s;
            st = ss.str().data();
         
        unsigned  stt=0;
        unsigned s0=q_bound;
        unsigned j=0;
    while( j<st.size()){
            (*states).push_back(std::make_pair("q"+st+std::to_string(s0+j),"q"+st+std::to_string(s0+j)));
            // EPS LOOP
            expr_ref pep(mk_fresh_const("peps", int_sort), m);
            
            res.push_back(std::make_pair(ep, pep));
             int_vars.push_back(ep);
        int_vars.push_back(pep);
            // normal transition
            (*states).push_back(std::make_pair("q"+st+std::to_string(s0+j),"q"+st+std::to_string(s0+j+1)));
            std::string strn= st;
            std::string stp= 'p'+strn;

            expr_ref vr(mk_fresh_const(strn, int_sort,s0+j, s0+j+1), m);
            expr_ref p_vr(mk_fresh_const(stp, int_sort,s0+j,s0+j+1), m);
             int_vars.push_back(vr);
        int_vars.push_back(p_vr);
            res.push_back(std::make_pair(vr, p_vr));
             axioms.push_back(m_util_a.mk_eq(vr, m_util_a.mk_numeral(rational(int(st[j])), true)));
            j++;
    }

     (*states).push_back(std::make_pair("q"+st+std::to_string(s0+j),"q"+st+std::to_string(s0+j)));
     expr_ref pep(mk_fresh_const("peps", int_sort), m);
     res.push_back(std::make_pair(ep, pep));
      int_vars.push_back(ep);
        int_vars.push_back(pep);
     states_map.insert(elt, *states);
     
       
    return res;

     }












 void   theory_atlas::find_states( expr_ref elt, 
        std::vector<std::pair<std::string, std::string>> *states){

            for(obj_map<expr,std::vector<std::pair<std::string, std::string>>> ::iterator it = states_map.begin(); it != states_map.end(); ++it){

                  if(m.are_equal(elt,&((*it).get_key()))
                      ){

                    (* states)= (*it).get_value();

            }

        }
 }
    void   theory_atlas::find_vars( expr_ref elt, 
        std::vector<std::pair<expr_ref, expr_ref>> *vars){
 for(obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> ::iterator it = fresh_int_vars.begin(); it != fresh_int_vars.end(); ++it){
                  if(m.are_equal(elt,&((*it).get_key()))
                      ){
                            

                    (* vars)= (*it).get_value();

            }

        }

        }


    std::vector<std::pair<expr_ref,expr_ref>>  theory_atlas::init_int_vars2(
        expr_ref elt, 
        unsigned p,
        std::string s,
        std::vector<std::pair<std::string, std::string>> *states){
        std::vector<std::pair<expr_ref, expr_ref>> res;

     //  if(find_var_by_label(int_vars, s))

        ast_manager &m = get_manager();
        expr_ref ep(mk_fresh_const("ep", int_sort), m);
        SASSERT(q_bound%cut_size == 0);
        unsigned new_q_bound=q_bound/cut_size ;
        unsigned num_states = (new_q_bound+1)*p_bound-1,sr,d, lp=0, a=0;
        unsigned  st=0;
        for(unsigned k=0; k< p_bound; k++){
        unsigned s0=k*new_q_bound;
        unsigned j=0;
        
        (*states).push_back(std::make_pair("q"+s+std::to_string(st),"q"+s+std::to_string(s0)));
        expr_ref pep(mk_fresh_const("peps", int_sort), m);
        res.push_back(std::make_pair(ep, pep));
        int_vars.push_back(ep);
        int_vars.push_back(pep);

   
        (*states).push_back(std::make_pair("q"+s+std::to_string(st),"q"+s+std::to_string(st)));
        std::string stt= s+"!tmp"+std::to_string(st)+std::to_string(s0);
        expr_ref xep(mk_fresh_const(stt, int_sort), m);
        expr_ref pep2(mk_fresh_const('p'+stt, int_sort), m);
         int_vars.push_back(xep);
        int_vars.push_back(pep2);
        res.push_back(std::make_pair(xep, pep2));

        st+=new_q_bound;
         if(k<p_bound-1) {
 
            std::string stt= s+"!tmp"+std::to_string(k*q_bound)+std::to_string((k+1)*q_bound); 
            (*states).push_back(std::make_pair("q"+s+std::to_string(k*q_bound),"q"+s+std::to_string((k+1)*q_bound)));
            stt= s+"!tmp"+std::to_string(k*q_bound)+std::to_string((k+1)*q_bound);
            expr_ref xep(mk_fresh_const(stt, int_sort), m);
            expr_ref pep(mk_fresh_const('p'+stt, int_sort), m);
             int_vars.push_back(xep);
             int_vars.push_back(pep);
            res.push_back(std::make_pair(xep, pep));

         } 

        }


  
        states_map.insert(elt, *states);
        return res;
    }





expr_ref theory_atlas::get_in_state_index(expr_ref elt,
            std::vector<std::pair<std::pair<expr_ref, expr_ref>,expr_ref>>  prod_vars,
           std::vector< std::pair<std::string, std::string>>  p_states){
    
        auto it = std::find(pk_vars.begin(), pk_vars.end(),elt );
        if( it!= pk_vars.end()){
             int i= it - pk_vars.begin();
             return get_state_index(p_states[i].first);
        }
    /*  for(unsigned i=0; i< prod_vars.size(); i++){
          
        if (expr2str(elt) == expr2str(prod_vars[i].second)){
            return get_state_index(p_states[i].first);
        }
            
             }*/
    }

expr_ref  theory_atlas::get_state_index(std::string elt
            ){
                 
                // expr_ref e(m);
                if (st_map.count(elt) > 0){
                    
                    std::map <std::string, expr_ref> ::iterator it =st_map.find(elt);
                        return it->second;
                }
                       
           // return e;

            }
   


void theory_atlas::find(obj_map<expr_ref,std::vector<std::pair<std::string, std::string>>> states_map,
                expr_ref elt,
                  std::vector<std::pair<std::string, std::string>> states){

      for(obj_map<expr_ref,std::vector<std::pair<std::string, std::string>>> ::iterator it = states_map.begin(); it != states_map.end(); ++it){

                 if(m.are_equal(elt,(*it).get_key())){
                   
                     states= (*it).get_value();
                     
                 

                   }
                  }
        
                  }


bool theory_atlas:: find(obj_map <std::string, expr_ref> st_ma,
                        std::string s,
                        expr_ref e){
            for(obj_map <std::string, expr_ref> ::iterator it = st_ma.begin(); it != st_ma.end(); ++it){

                 if(s== (*it).get_key())
                   
                     {e= (*it).get_value();
                     return true;
                     }
                
                 

                   
                  }
                  return false;
         
                        }
    std::string theory_atlas::expr2str(expr* node){
        std::stringstream ss;
        
        ss << mk_pp(node, m);
        return ss.str();
    }




void theory_atlas::print_model(context &local_ctx) {
    arith_value local_arith_value(m);
    local_arith_value.init(&local_ctx);
    //rational val;
   for(obj_map<expr,std::vector<std::pair<expr_ref, expr_ref>>> ::iterator it = fresh_int_vars.begin(); it != fresh_int_vars.end(); ++it){
                 
                 //expr_ref e(m);
                 std::stringstream ss;
                 unsigned k=1,j=0;
                 while(k<(*it).get_value().size()){                
                std::string res="";
                while(j<q_bound){                 

                     rational val;
                     
                     local_arith_value.get_value_equiv((*it).get_value()[j+k].first, val);
                      
               
                       
                    
                     char s= char(val.get_int64());  
                    if(s !=' ') res= res+s;
                    j++;                 
                                         

                }
                rational val2 ;                  
                local_arith_value.get_value_equiv((*it).get_value()[k].second, val2);            

                
            for(unsigned i=0; i<val2; i++)  ss << res;    

           if(k<(*it).get_value().size()-1){ 
               rational val3 ;                  

               
                local_arith_value.get_value_equiv((*it).get_value()[k+1].first, val3); 
            char s= char(val3.get_int64());   
            if(s !=' ') ss <<s;
            }
            k=k+3;
            j=0;

            }
                
    

        zstring st(ss.str().data()); 
        for(obj_map<expr,std::string> ::iterator it2 = model.begin(); it2 != model.end(); ++it2){
          if(m.are_equal(&((*it).get_key()), &((*it2).get_key()))) {
                            model.insert(&((*it).get_key()), ss.str());
             // (*it2).get_value() = ss.str();
          }

      }

        //model.push_back(std::make_pair(&ee,ss.str()));

                /* for(auto elt:(*it).get_value() ){
                                          expr exx= *(elt.first);
                    local_arith_value.get_value_equiv(elt.first, val);
                 }*/
              
   }

      

    //&& val.is_int();
  //  print_term(local_arith_value, term, size);
}

std::vector<int> theory_atlas::get_segment_vector() {
    std::vector<int> segment_vector;
    int segment = stoi(gparams::get_value("segment"));
    if (segment <= 0)
        segment_vector.insert(segment_vector.end(), {1, 2, 4, 8});
    else
        segment_vector.push_back(segment);
    return segment_vector;
}

void theory_atlas::print_terms(const expr_ref_vector& terms){
    bool first =true;
    
}
}
