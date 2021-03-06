%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  VERSION 4.9.5

%release 4.9.5-18 
% - aggiunto trattamento size(S,N) % N > k o N neq 0.
%   es. size(S,N) & N>=3. size(S,N) & N neq 0. size(S,N) & N>=M+1 (--> ***WARNING***)
% - rifatta implementazione di nodup_split; nuovo predicato split_cs
%.1 
% - spostato clausole di global_check2 per mettere vicine quelle per lo stesso vincolo
%.2 
% - aggregato clausole di global_check2 per lo stesso vincolo
%.3 
% - corretto bug nella sat_nin caso cp;
%   controes.: X nin cp(A,B) solo la sol. X = [_N2,_N1] (invece che tre sol.)
% - spostato clausole definizione di nonopen_intv(S) e open_intv(_S). 
% - definito closed_intv e usato al posto di is_c_int
% - anticipato test var(Warning) in varie clausole di filter_and_check1
% - aggiunto cut nella penultima clausola di filter_and_check1
% - definito nuova clausola per filter_and_check1 caso open interval 
% - definito predicato contains_open_int(C) e chiamato in filter_and_check1 
%   controes.:  subset(int(A,10),{1}) & A > 2. --> true, senza nessun warning
%.4
% - rifatta implementazione di labeling_FD: definito labeling_FD/2, modificato
%   labeling_FD/1 in modo che prenda una lista,
% - modificato uso di labeling_FD in labeling/1, in finalize_int_constr/1
%.5
% - aggiunto fd_labeling_strategy(Str) e usato in labeling_FD/1
% - modificato commento a dynamic int_solver/1.
% - aggiunto dynamic fd_labeling_strategy e nuova clausola per fd_labeling_strategy
%   in apply_params 

%release 4.9.5-19 
% - sistemato bug in uso delay per sat_dres, sat_rres, sat_dares, sat_rares 
% - aggiunta gestione intervalli chiusi (compreso vuoti) nella sat_id
% - sostituito S={} con is_empty(S) is sat_inv   
%   (modifiche indicate con %NNNNNNNNNNNNNNNNN)
%a
% - aggiunto sort constraint a sat_id e sat_inv
%b
% - aggiunto caso trattamento id(X,X)  ---> X={} in sat_id
%c
% - modificata implementazione della sat_inv caso speciale sat_inv_same_tail
%   aggiunto caso inv(R,{.../R}) (era presente solo  inv({.../R},R))
%d
% - sistemato bug per casi id(R,{.../R}) e id({.../R},R)

%release 4.9.5-20 
% - modificata sat_inv_same_tail per caso inv({.../R},{.../R}).
%   controesempio: inv({[a,b]/R},{[a,b]/R})  & R = {[b,a]}. ---> no 
%b
% - corretto problema con goal inv({[a,a]/R},{[b,b]/R}). ---> infinite soluzioni
%   (riattivato [Y1,X1] nin N3 in sat_inv_same_tail)
%c
% - modificato implementazione di sat_nran
% - modificato implementazione di sat_nid
% - modificato gen_type_constrs(id(T1,T2)...) (pfun(T1) --> rel(T1)) : NO, ripristinato
%d
% - modificato gen_type_constrs di id: pfun(T2) ---> rel(T2)  

%release 4.9.5-21 
% - spostato 'cut' in penultima clausola di sat_un in modo da tagliare anche la sunify
%   controesempio un({1/A},{1,C},{2,{[X,X]/M1}}).
% - aggiunta nuova clausola a sat_id per trattare caso id({.../R},{.../R}), var R
%a
% - usato sunify invece di unificazione sintattica in dompf, caso dom(S,{...}) var(S)
%   controesempio:  dompf(S,{S}) (richiede occr-check)
% - usato sunify invece di unificazione sintattica in inv, caso inv(R,{...}), var R [rule inv_6]
%   controesempio:  inv(R,{[a,R]}) o  inv(R,{[R,1]}) (richiede occr-check)
%b
% - modificata regola di sat_eq_cp per trattamento caso cp(A,B) = cp(C,D)
%   controesempio:  cp(W,X) = cp(Y,Z) & X={} & Z={} & W={1} & Y={2}.  --> no
%   X={} & Z={} & W={1} & Y={2} & cp(W,X) = cp(Y,Z) --> X = {},  Z = {},  W = {1}, Y = {2}
%c
% - eliminata sunify da condizioni della penultima clausola sat_un (inutile se inclusa nel cut)
%   ed eliminati vincoli T1 nin N nelle tre alternative
%   cosi' funziona sia con il goal un({1/A},{3},{{2/B}}) che con il goal
%   comp({[1,a],[2,b],P1},{[a,x],P2},{[1,x],P3}) & call(P3 = [1,x]) & call(P2 = [a,x]) & call(P1 = [1,a]).
%   Funziona correttamente anche il goal
%        A neq B & subset({[X,A],[X,B]/Z},cp(U3,U1))
%   che prima ritornava "no"
%   ma non riesce a terminare il goal (con la release elease 4.9.5-20 termina in ca. 15 sec.)
%   un(A,B,M1) & un(M1,M2,U) & disj(M1,M2) & un(M2,C,M3) & un(M3,M4,U) & disj(M3,M4) & un(C,D,M5) & 
%   un(M5,M6,U) & disj(M5,M6) & un(C,M7,U) & disj(C,M7) & un(M7,M6,M8) & un(M8,M13,U) & disj(M8,M13) & 
%   un(A,M13,M9) & un(M9,M10,U) & disj(M9,M10) & un(M4,M10,M11) & un(M11,M12,U) & disj(M11,M12) & M12 neq C.
%d
% - aggiunto commenti nella sat_un
% - modificato ordine clausole di predicati usati nella sat_un
% - sostituito predicati samevar_cp/2 e samevar_cp/3 con cp_component(X,CP)/2 e cp_component(X,CP)/3
% - commentata la %member_all/4 perche' non utilizzata
% - aggiunto predicato tail_cp
% - aggiunto predicato sat_un_special_cp/6
% - commentate clausole di sat_un per trattamento casi speciali su CP
% - aggiunto nuova clausola di sat_un per trattamento casi speciali su CP
% - clausole per predicati sat_un_cp_special e sat_un_special_tail non piu' in uso
%   (da eliminare)
%e
% - eliminati 'cut' da casi speciali di sat_un, sat_eq_cp e sat_id
% - aggiunto definizione di predicato same_tail/3
%f
% - rimessi 'cut' nei casi speciali di sat_un, sat_eq_cp e sat_id (come in release d)
% - modificata clausola di sat_un per trattamento casi speciali su CP (solo soluzione TZ={})

%release 4.9.5-22
% - ripristinati clausola di sat_un per trattamento casi speciali su CP e sat_un_special_cp/6
%   come in release 21d
% - aggiunta implementazione vincolo id ssu CP in sat_id;
%   definito nuovo predicato sat_id_cp
% - aggiunto trattamento casi speciali in sat_id_cp;
%   es.: id(cp(A,B),{X/A}), id(cp(A,B),cp({X/A},{Y/B})).
%a
% - modificato ordine clausole in sat_dom_cp; es.  dom(A,cp(A,B)) --> irriducibile
% - anticipata chiamata della sat_dom_cp in sat_dom
% - modificata implementazione caso speciale di sat_dom_cp;
%   controesempi: dom({X/A},cp(A,{Y/B})), dom({X/A},cp({X/A},{Y/A})), ... (ciclo)
% - modificata implementazione caso speciale di sat_id_cp;
%   controesempio: id(cp({Y/B},{Z/A}),{X/A}) (ha soluzioni)
% - usato same_tail(A,B,TS) in sat_dom_cp caso speciale
% - elimnato caso fail da sat_eq_cp casi speciali
% - anticipata clausole per trattamento CP in sat_inv;
%   controesempio: inv({X/A},cp(A,{Y/B})). (ciclo)
% - rinominata sat_un_special_cp in special_cp3
% - aggiunta clausola a sat_comp_cp per trattamento casi speciali
%   controesempio: comp(cp({Y/B},{X/A}),C,{X/A}),  comp(cp({Y/B},{Z/A}),C,{X/A})
%   (soluz. sempre piu' grosse)            


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                          
%%                The {log} interpreter and solver                  
%%                                                           
%%                           VERSION 4.9.5   
%%                                             
%%                      original development by                                                          
%%                Agostino Dovier     Eugenio Omodeo          
%%                Enrico Pontelli     Gianfranco Rossi  
%%
%%                    subsequent enhancements by
%%                         Gianfranco Rossi
%%
%%                    with the contribution of 
%%       B.Bazzan  S.Manzoli  S.Monica  C.Piazza  L.Gelsomino
%%
%%                        Last revision by 
%%               Gianfranco Rossi and Maximiliano Cristia'
%%                         (August 2018)           
%%                                                              
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(setlog,[
             op(980,xfx,:),
             op(970,xfy,or),
             op(950,xfy,&),
             op(900,fy,[neg,naf]),
             op(800,xf,!),
             op(700,xfx,[in,neq,nin]), 
             op(670,xfx,\),                    
             op(650,yfx,[with,mwith]), 
             op(150,fx,*),
             setlog/0,           % for interactive use
             setlog/1,           % to call setlog from Prolog
             setlog/2,
             setlog/3,
             setlog/4,
             setlog/5,
             setlog_InOut/3,
             setlog_InOut_partial/3,
             setlog_InOut_SC/3,
             setlog_consult/1,
             consult_lib/0,
             setlog_clause/1,
             setlog_config/1, 
             setlog_clear/0,   
             setlog_rw_rules/0,  
             setlog_help/0,           
             h/1 
   ]).

:- use_module(library(dialect/sicstus/timeout)).         

:- dynamic isetlog/2.                                  
:- dynamic newpred_counter/1. 
:- dynamic context/1. 
:- dynamic final/0.         %default: no final
:- dynamic nowarning/0.     %default: warning
:- dynamic filter_on/0.     %default: no filter_on

:- dynamic nolabel/0.       %default: label
:- dynamic noneq_elim/0.    %default: neq_elim
:- dynamic noran_elim/0.    %default: ran_elim
:- dynamic nocomp_elim/0.   %default: comp_elim
:- dynamic noirules/0.      %default: irules
:- dynamic subset_elim/0.   %default: no subset_elim                                
:- dynamic trace/1.         %default: no trace
:- dynamic int_solver/1.    %default: as specified by default_int_solver/1

:- dynamic strategy/1.      %modifiable configuration params  
:- dynamic path/1. 
:- dynamic rw_rules/1. 
:- dynamic fd_labeling_strategy/1.   
     
:- multifile replace_rule/6.     
:- multifile inference_rule/7.
:- multifile fail_rule/6.
:- multifile equiv_rule/3.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%                                    %%%%%%%%%%%%%%           
%%%%%%%%%%%   {log} interactive environment    %%%%%%%%%%%%%%               
%%%%%%%%%%%                                    %%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates implement the {log} 
% interactive programming environment. This environment 
% offers a Prolog-like user interface, enriched with facilities
% for manipulating sets and multi-sets. The most notable
% syntactic differences w.r.t. std Prolog are: the use of '&' in 
% place of ',' to represent goal conjunction; the  use of 'or' 
% in place of ';' to represent goal disjunction; the use of 
% 'neg' or 'naf' in place of '\+' to represent negation (resp., 
% simplified Constructive Negation and Negation as Failure).  
% To enter the {log} interactive environment call the goal
% 'setlog.'. To exit, call the goal 'halt.'.
% N.B. {log}, in the current version, provides only a small 
% subset of Prolog built-ins and no support for program
% debugging at {log} program level.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog :-
       set_default,
       top_level.

set_default :-
       cond_retract(nowarning),      %restore default value: warning
       set_default_control,       
       cond_retract(nolabel),        %restore default value: label
       retract_trace,                %restore default value: no trace
       default_int_solver(IS),
       ssolve(int_solver(IS),[],[]). %restore default value: clpfd
set_default_control :-
       cond_retract(noirules),       %restore default value: irules
       cond_retract(noneq_elim),     %restore default value: neq_elim
       cond_retract(noran_elim),     %restore default value: ran_elim 
       cond_retract(nocomp_elim),    %restore default value: comp_elim 
       cond_retract(final),          %restore default value: no final
       cond_retract(subset_elim).    %restore default value: no subset_elim

top_level :-
       nl, write('{log}=> '),
       setlog_read_term(Goal,[variable_names(VarNames)]),            %e.g. VarNames=[X=_1,S=_2,Y=_3,R=_4]
       solve(Goal,Constr),
       skip_return, 
       add_intv(Constr,ConstrAll,_),     
       filter_and_check_w(ConstrAll,RConstrAll,_),
       chvar([],_,v(VarNames,RConstrAll),_,_,v(VarNames1,Constr1)),  %e.g. VarNames1=[X=_20,S=_21,Y=_22,R=23],[set(_23)]))
       mk_subs_ext(VarNames1,VarNames_ext1),  %e.g. VarNames1=[X=X,S=R with X,Y=X,R=R] VarNames_ext1=[S={X/R},Y=X,true,true]
       extract_vars(VarNames_ext1,Vars),      %e.g. VarNames_ext1=[S={Y/_7},R={X/_7},true,true] Vars=[_7]
       extract_vars(Constr1,ConstrVars),
       rename_fresh_vars(Vars,1,N),
       rename_fresh_vars(ConstrVars,N,_),
       nl, write_subs_constr(VarNames_ext1,Constr1,Vars),
       top_level.
top_level :-
       nl,write(no),nl,
       skip_return,  
       top_level.

welcome_message :-                                     
       nl, nl,
       write('              WELCOME TO {log} - version 4.9           '),
       nl, nl.

%%%%%%%%%%%%%%%%

setlog_read_term(Goal,Vars) :- 
       on_exception(Msg,read_term(Goal,Vars),syntax_error_msg(Msg)).  

syntax_error_msg(Text) :-
       write('Syntax error:'), nl,   
       write(Text), nl, 
       fail.

skip_return :-    
      read_pending_input(user_input,_C,[]).

%%%%%%%%%%%%%%%%

mk_subs_ext(VarSubs,VarSubsMin) :-      
       postproc(VarSubs,VarSubsExt),
       mk_subs_vv(VarSubsExt,VarSubsMin).

mk_subs_vv([],[]).                  
mk_subs_vv([N1=V1|Subs],R) :-
       var(V1),!,
       V1 = N1,
       mk_subs_vv(Subs,SubsMin),
       append(SubsMin,[true],R).  
mk_subs_vv([N1=V1|Subs],[N1=V1|R]) :-
       mk_subs_vv(Subs,R).  

%%%%%%%%%%%%%%%% write substitutions and constraints

write_subs_constr([],[],_) :- !,    
       write(yes), nl.                       
write_subs_constr(Subs,Constr,Vars) :-  
      (Subs = [],!, true
       ; 
       Subs = [true|_],!,write('true'),Prn=y
       ;
       write_subs_all(Subs,Prn)
      ), 
       write_constr(Constr,Vars,Prn), 
       ask_the_user(Prn).

ask_the_user(Prn):-
       var(Prn),!.
ask_the_user(_):-
       nl,  
       nl, write('Another solution?  (y/n)'),
%       get(C), skip(10),
       get_single_char(C), 
       (C \== 121,! 
        ; 
        cond_retract(nowarning), fail
       ).

write_subs_all([],_).
write_subs_all([N1=V1|R],Prn) :-
        write(N1), write(' = '), write(V1), Prn=y,  
       (R = [],!,true ; 
        R = [true|_],!,true ;
        write(',  '), nl, write_subs_all(R,Prn) ).  

write_constr(Constr,Vars,Prn) :-             
       postproc(Constr,Constr_ext),
       write_eqconstr_first(Constr_ext,Constr_ext_noeq),    
       write_constr_first(Constr_ext_noeq,Vars,Prn).

write_eqconstr_first([],[]) :- !.                
write_eqconstr_first([T1 = T2|R],NewR) :- 
       var(T1),!,             
       write(',  '), nl, 
       write(T1), write(' = '), write(T2),
       write_eqconstr_first(R,NewR).  
write_eqconstr_first([T1 = T2|R],NewR) :- 
       var(T2),!,             
       write(',  '), nl, 
       write(T2), write(' = '), write(T1),
       write_eqconstr_first(R,NewR).  
write_eqconstr_first([C|R],[C|NewR]) :-             
       write_eqconstr_first(R,NewR).

write_constr_first([],_,_) :- !.                
write_constr_first([C|Constr],Vars,Prn) :-             
       nl, write('Constraint: '), 
       write_atomic_constr(C), Prn=y,
       write_constr_all(Constr,Vars).

write_constr_all([],_) :- !.                
write_constr_all([C|Constr],Vars) :-             
       write(', '), write_atomic_constr(C),
       write_constr_all(Constr,Vars).
         
write_atomic_constr(solved(C,_,_,_)) :- !,
       write(C).
write_atomic_constr(delay(irreducible(C)&true,_)) :- !, 
       write(irreducible(C)).
write_atomic_constr(C) :- !,
       write(C).

rename_fresh_vars([],Num,Num) :- !.
rename_fresh_vars([X|R],Num,NumF) :-
       var(X),!,
       name(Num,NumCodeList),
%       append([78,95],NumCodeList,CodeList),   %N_
%       append([78],NumCodeList,CodeList),
       append([95,78],NumCodeList,CodeList),   %_N
       name(XNew,CodeList),
       X=XNew,
       Num1 is Num + 1,
       rename_fresh_vars(R,Num1,NumF).
rename_fresh_vars([_X|R],Num,NumF) :-
       rename_fresh_vars(R,Num,NumF).

filter_and_check_w(Constr,ConstrAll,Warning) :-     
       filter_and_check(Constr,ConstrAll,Warning), 
       mk_warning(Warning).    

filter_and_check(C,NewC,W) :-
       split_cs(C,RedCS),                         %split the CS into <neq-constraints,other-constraints>
       filter_and_check1(C,RedCS,NewC,W). 
filter_and_check1([],_GC,[],_) :- !.         
filter_and_check1([C|R],GC,ReducedC,Warning) :-   %remove sort constraint not to be shown
       type_constr(C),   
       type_constraints_to_be_shown(LConstr), \+member(C,LConstr),!,   
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([comp(X,Y,Z)|R],GC,[comp(X,Y,Z)|ReducedC],Warning) :-
       nocomp_elim,
       var(Warning),
       tail(X,TX),tail(Y,TY),tail(Z,TZ),      
       samevar3(TX,TY,TZ),!,  
       Warning = unsafe,        
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
       noran_elim,
       var(Warning),
       is_ran_l(C,_,X,Y),var(X),nonvar(Y),!,  
       Warning = unsafe,        
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
       noneq_elim,
       var(Warning),
       is_neq(C,1,W,T),var(W),var(T),
       find_setconstraint(W,T,GC,_X,_Y),!,  
       Warning = unsafe,        
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
       noneq_elim,
       var(Warning),
       is_neq(C,1,W,T),var(W),nonvar(T),is_set(T),
       find_setconstraint(W,GC),!,  
       Warning = unsafe,        
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([X in int(inf,B)|R],GC,[X =< B|ReducedC],Warning) :- !,   %replace open domain declarations
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([X in int(A,sup)|R],GC,[X >= A|ReducedC],Warning) :- !,   %replace open domain declarations
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([glb_state(Rel)|R],GC,ReducedC,Warning) :-   %remove constraints glb_state/1  
       Rel =.. [_OP,E1,E2],                                    %e.g. glb_state(X>3) & X in int(10,sup)                               
       (ground(E2), get_domain(E1,(E1 in _)),!
        ;
        ground(E1), get_domain(E2,(E2 in _))
       ),!,
       filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([glb_state(Rel)|R],GC,[Rel|ReducedC],Warning) :- !, %extract C from glb_state(C)  
       (var(Warning),                                                 %and generate warning if C is:
        int_solver(clpfd),                                            %e.g  X>Y, X>X-1
        Rel =.. [_OP,E1,E2],                                          %e.g. X+Y>2
            (\+ground(E1),\+ground(E2),!                       
             ;
             term_variables(Rel,VarsList), VarsList=[_,_|_]    
            ),!,
        Warning = 'not_finite_domain'
        ; 
        true),!,    %NEW       
        filter_and_check1(R,GC,ReducedC,Warning). 

filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
       (var(Warning),
        contains_open_int(C),!,
        Warning = 'not_finite_domain'
        ; 
        true),!,            
        filter_and_check1(R,GC,ReducedC,Warning).
filter_and_check1([C|R],GC,[C|ReducedC],Warning) :-
       filter_and_check1(R,GC,ReducedC,Warning).

mk_warning(R) :- 
       var(R),!.
mk_warning('not_finite_domain') :- !,
       write('\n***WARNING***: non-finite domain'),nl.     
mk_warning(unsafe) :- !,
       write('\n***WARNING***: possible unreliable answer'),nl.

contains_open_int(C) :-
       C=..[OP,X,Y],!,
       (OP == subset,! ; OP == dom),     % NOT-SOLVED irreducible constraints which may
       (open_intv(X),! ; open_intv(Y)).  % contain open intervals
%contains_open_int(C) :-
%       C=..[_,X,Y,Z],
%       (open_intv(X),! ; open_intv(Y),! ; open_intv(Z)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%   Prolog to {log} interface  %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following predicates allow a Prolog program to use the 
% {log} facilities for set/bag definition and manipulation
% (without leaving the Prolog execution environment).
% In particular, they provide a (Prolog) predicate for calling 
% any {log} goal G, possibly involving {log} set constraints.
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% setlog(+Goal) 
%
setlog(Goal) :-
       setlog(Goal,_,_).

%%%% setlog(+Goal,-OutConstraintList) 
%
setlog(Goal,OutConstrLst) :-
       setlog(Goal,OutConstrLst,_).

%%%% setlog(+Goal,-OutConstraintList,-Res) (Res = success | maybe) 
%
setlog(Goal,OutConstrLst,Res) :-
       set_default,
       setlog1(Goal,OutConstrLst,Res).
setlog1(Goal,OutConstrLst,Res) :-
       nonvar(Goal), 
       copy_term(Goal,NewGoal),
       setlog2(NewGoal,Constr,Res),
       postproc(Constr,OutConstrLst),         %from 'with' to {...} notation  
       postproc(NewGoal,NewGoal_ext),
       postproc(Goal,Goal_ext),
       Goal_ext = NewGoal_ext.                %apply sustitutions to the original variables
setlog2(NewGoal,Constr,Res) :-
       solve(NewGoal,C),    
       remove_solved(C,C1),                   %remove info about "solved" constraints    
       add_intv(C1,Constr1,Warning),          %add the possibly remaining interval constr's
       filter_and_check(Constr1,Constr,Warning),
       map_warning(Warning,Res). 

%%%% setlog with timeout and other optional strategies (setlog/5)
%%%% setlog(+Goal,+TimeOut,-OutConstraintList,-Res,+Options) (Res = success | time_out | maybe)
%
setlog(Goal,TimeOut,OutConstrLst,Res,Options) :-
       set_default,
       setlog1(Goal,TimeOut,OutConstrLst,Res,Options).

setlog1(Goal,TimeOut,OutConstrLst,Res,[]) :- !,
       time_out(setlog1(Goal,OutConstrLst,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlog1(Goal,TimeOut,OutConstrLst,Res,[Opt1|ROpt]) :-
       set_default_control,
       copy_term(Goal,NewGoal),
       setlogTimeOut_opt(Opt1,NewGoal,TimeOut,Constr,Res1), 
       setlogTimeOut_cont(ROpt,Goal,NewGoal,TimeOut,Constr,OutConstrLst,Res1,Res).

setlogTimeOut_cont([],Goal,NewGoal,_TimeOut,Constr,OutConstrLst,Return,Return) :- !,
       postproc(Constr,OutConstrLst),          
       postproc(NewGoal,NewGoal_ext),
       postproc(Goal,Goal_ext),
       Goal_ext = NewGoal_ext.                
setlogTimeOut_cont(_,Goal,NewGoal,_TimeOut,Constr,OutConstrLst,success,success) :- !,
       postproc(Constr,OutConstrLst),          
       postproc(NewGoal,NewGoal_ext),
       postproc(Goal,Goal_ext),
       Goal_ext = NewGoal_ext.                  
setlogTimeOut_cont(ROpt,Goal,_NewGoal,TimeOut,_,OutConstrLst,_,Res) :-
       setlog1(Goal,TimeOut,OutConstrLst,Res,ROpt).

setlogTimeOut_opt(clpq,Goal,TimeOut,Constr,Res) :- !,
       int_solver(Current), 
       ssolve(int_solver(clpq),[],[]),
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res),
       ssolve(int_solver(Current),[],[]).
setlogTimeOut_opt(clpfd,Goal,TimeOut,Constr,Res) :- !,
       int_solver(Current), 
       ssolve(int_solver(clpfd),[],[]),
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res),
       ssolve(int_solver(Current),[],[]).
setlogTimeOut_opt(final,Goal,TimeOut,Constr,Res) :- !,
       set_final,      
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlogTimeOut_opt(noirules,Goal,TimeOut,Constr,Res) :- !,
       ssolve(noirules,[],[]),    
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlogTimeOut_opt(subset_elim,Goal,TimeOut,Constr,Res) :- !,
       ssolve(subset_elim,[],[]),  
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlogTimeOut_opt(noneq_elim,Goal,TimeOut,Constr,Res) :- !,
       ssolve(noneq_elim,[],[]),
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlogTimeOut_opt(noran_elim,Goal,TimeOut,Constr,Res) :- !,
       ssolve(noran_elim,[],[]),
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).
setlogTimeOut_opt(nocomp_elim,Goal,TimeOut,Constr,Res) :- !,
       ssolve(nocomp_elim,[],[]),
       time_out(setlog2(Goal,Constr,Res1),TimeOut,Res2),
       check_timeout_res(Res2,Res1,Res).

%%%% setlog with timeout and different strategies (setlog/4)
%%%% setlog(+Goal,+TimeOut,-OutConstraintList,-Res) (Res = success | time_out | maybe)
%
setlog(Goal,TimeOut,OutConstrLst,Res) :-       %for backward compatibility
       setlog(Goal,TimeOut,OutConstrLst,Res,[clpfd,final,noirules,noneq_elim,noran_elim]).  

%%%% setlog_InOut(+Goal,+InConstraintList,-OutConstraintList) 
%
setlog_InOut(Goal,InConstrLst,OutConstrLst) :-  
       nonvar(Goal), nonvar(InConstrLst),
       set_default,
       list_to_conj(InConstr,InConstrLst),             %from list (InConstrLst) to conjunction (InConstr)     
       conj_append(Goal,InConstr,ExtdGoal),
       copy_term(ExtdGoal,NewGoal),
       solve(NewGoal,OutCLstIntl),
       remove_solved(OutCLstIntl,ROutCLstIntl),        %remove info about "solved" constraints
       add_intv(ROutCLstIntl,OutFinalCLstIntl,_),      %add the possibly remaining interval constr's
       postproc(OutFinalCLstIntl,OutConstrLst),        %from 'with' to {...} notation      
       postproc(NewGoal,NewGoal_ext),
       postproc(ExtdGoal,ExtdGoal_ext),
       ExtdGoal_ext = NewGoal_ext.                     %apply sustitutions to the original variables         

%%%% setlog_InOut_partial(+Goal,+InConstraintList,-OutConstraintList) 
%
setlog_InOut_partial(Goal,InConstrLst,OutConstrLst) :-  
       nonvar(Goal), nonvar(InConstrLst),
       set_default,
       list_to_conj(InConstr,InConstrLst),    %from list (InConstrLst) to conjunction (InConstr)     
       conj_append(Goal,InConstr,ExtdGoal),
       copy_term(ExtdGoal,NewGoal),       
       transform_goal(NewGoal,B),             %from extl to internal repr. (remove SF, RUQ, {...})
       solve_goal(B,Constr),                  %call the constraint solver (in 'non-final' mode)
       postproc(Constr,OutConstrLst),         %from 'with' to {...} notation     
       postproc(NewGoal,NewGoal_ext),
       postproc(ExtdGoal,ExtdGoal_ext),
       ExtdGoal_ext = NewGoal_ext.            %apply sustitutions to the original variables             

%%%% setlog_InOut_sc(+Constraint,+InConstraintList,-OutConstraintList) 
%
setlog_InOut_SC(Constr,InConstrLst,OutConstrLst) :- %to solve {log} Set Constraints (partial solve)
       nonvar(Constr), nonvar(InConstrLst),
       set_default,
       list_to_conj(InConstr,InConstrLst),    %from list (InConstrLst) to conjunction (InConstr) 
       conj_append(Constr,InConstr,CS),
       copy_term(CS,NewCS),
       preproc_goal(NewCS,NewCSIntl),         %from {...} to 'with' notation;   
       solve_goal(NewCSIntl,OutCLstIntl),     %call the constraint solver (in 'non-final' mode)
       postproc(OutCLstIntl,OutConstrLst),    %from 'with' to {...} notation  
       postproc(CS,CSExt),
       postproc(NewCS,NewCSExt),
       CSExt = NewCSExt.                      %apply sustitutions to the original variables

%map_warning(Warning,success) :-              %GFR per compatibilita' con versione precedente
map_warning(Warning,maybe) :- 
       nonvar(Warning),Warning == 'not_finite_domain',!.
map_warning(Warning,maybe) :- 
       nonvar(Warning),Warning == 'unsafe',!.
map_warning(Warning,maybe) :- 
       nonvar(Warning),Warning == 'maybe',!.
map_warning(_Warning,success).

check_timeout_res(success,Solve_res,Res) :- !,
       map_warning(Solve_res,Res).
check_timeout_res(timeout,_,timeout). 
check_timeout_res(Timeout_Res,_,Timeout_Res).

%not_save(success,maybe) :- !.     
%not_save(Res,Res) :- !.  


%%%% other predicates for Prolog to {log} interface 

setlog_consult(File) :-                   %like setlog(consult(File))
       setlog(consult(File,mute),_).      %but no message is sent to the std output

setlog_clause(Clause) :-                  %for compatibility with previous versions      
       setlog(assert(Clause),_).

consult_lib :-                            %to consult the {log} library file
       setlog(consult_lib,_).             

setlog_config(ConfigParams) :-            %to modify {log}'s configuration parameters
       set_params(ConfigParams).                      
  
setlog_rw_rules :-                        %to load the filtering rule library
       rw_rules(Lib),
       mk_file_name(Lib,FullName),
       consult(FullName). 
 
setlog_clear :-
       set_deafault.

%%%% auxiliary predicates for Prolog to {log} interface 

remove_solved([],[]).
remove_solved([solved(C,_,_,_)|R],[C|RR]) :- !,
    remove_solved(R,RR).
remove_solved([delay(irreducible(C)&true,_)|R],[irreducible(C)|RR]) :- !, 
    remove_solved(R,RR).
remove_solved([C|R],[C|RR]) :-
    remove_solved(R,RR).
   
set_params([]).                          
set_params([P1|ParamsList]) :-
    apply_params(P1),
    set_params(ParamsList).

apply_params(strategy(Str)) :- !,         
    replace_unitCl(strategy(_),Str).
apply_params(path(Path)) :- !,
    replace_unitCl(path(_),Path).
apply_params(rw_rules(FileName)) :- !,
    replace_unitCl(rw_rules(_),FileName).
apply_params(fd_labeling_strategy(Str)) :- !,         
    replace_unitCl(fd_labeling_strategy(_),Str).

%%% to be continued

replace_unitCl(Cl,NewParm) :-             
    retract(Cl),!,
    Cl =.. [F,_X], NewCl =.. [F,NewParm], 
    assert(NewCl).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%        The help sub-system   %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_help :- h(setlog).           

h(setlog) :- 
   nl, 
   write('   -   h(syntax), h(constraints), h(builtins), h(lib), h(prolog) to get help '), nl,
   write('       information (resp., about: {log} syntactic convenctions, {log} constraints, '), nl,
   write('       {log} built-in predicates, {log} library predicates, Prolog predicates'), nl,
   write('       for accessing {log})'), nl,
   write('   -   h(all) to get all available help information'), nl,
   write('   -   setlog/0: to enter the {log} interactive environment'),nl.

h(all) :-
   h(syntax), 
   h(constraints),
   h(builtins),
   h(prolog),
   h(lib).

h(syntax) :- 
   nl,    
write('%%%%%%%%%   Syntactic differences w.r.t. std Prolog  %%%%%%%%%'),
   nl, nl,
   write('   - ''&'' is used in place of '','' in clause bodies'), nl,
   write('   - ''or'' is used in place of '';'''),
                   write('  to represent goal disjunction.'), nl,
   write('   - neg or naf are used in place of  ''\\+'''),
                   write('  to represent negation (resp., '), nl,
   write('     simplified Constructive Negation and Negation as Failure)'),  
   nl, 
   write('   - Interpreted terms.'),
   nl, 
   write('     1. Extensional sets:'), nl,                  
   write('        (a, b, c: any term; R: variable, set, interval, IS, RIS, CP)'), nl,
   write('        - {}: the empty set/multiset'), nl,                             
   write('        - {a,b,c}: the set containing three elements, a, b, c'),nl,
   write('        - {a,b/R}: the set {a,b} U R,'), nl,          
   write('     2. Extensional multisets:'), nl,                  
   write('        (a, b, c: any term; R: variable, multiset)'), nl,
   write('        - *({a,b,b}) (or, * {a,b,b}): the multiset containing the elements,'),nl,
   write('          ''a'' (1 occurrence) and  ''b'' (2 occurrences)'),nl,   
   write('        - *({a,b/R}): the multiset *({a,b}) U R'), nl,      
   write('     3. Intervals:'), nl,                  
   write('        (h, k: variable, integer number)'), nl,
   write('        - int(h,k): the set of'), nl,
   write('          integer numbers ranging from h to k (k>=h) or the empty set (k<h)'), nl, 
   write('     4. Cartesian Products (CP):'), nl,                  
   write('        (A, B: variable, set, IS)'), nl,       
   write('        - cp(A,B): the set {[x,y] : x in A & y in B}'), nl,
   write('     5. Intensional Sets (IS):'), nl,                                 
   write('        (X: variable; G: any {log} goal containing X)'), nl,
   write('        - {X : G}'), nl,
   write('        - {X : exists(V,G)}, V variable local to G'), nl,
   write('        - {X : exists([V1,...,Vn],G)}, '), nl, 
   write('          V1,...,Vn variables local to G'), nl,
   write('     6. Restricted Intensional Sets (RIS):'), nl,                                 
   write('        - ris(C in D,[V1,...,Vn],G,t,aux) ([V1,...,Vn], aux optional): '), nl, 
   write('          the set {Y : exists([C,V1,...,Vn],C in D & G & Y=t & aux)}'), nl, 
   write('        - ris(C in D,[V1,...,Vn],G) ([V1,...,Vn] optional): '), nl, 
   write('          the set {Y : exists([C,V1,...,Vn],C in D & G & Y=X)}'), nl, 
   write('          C (control term): X, [X,Y], {X/Y}, '), nl,
   write('          D (domain): variable, set, interval, RIS, CP, '), nl,
   write('          V1,...,Vn: variables local to G, '), nl,
   write('          G: any {log} goal, '), nl,
   write('          t (pattern): any term but not a RIS, '), nl,
   write('          aux (auxiliary predicates for t): any {log} goal (e.g. t: [X,Y], aux: Y is X+1)'), nl,
   write('   - Special atoms.'),  
   nl, 
   write('     1. Restricted Universal Quantifiers (RUQ): '), nl,                            
   write('        (A: variable, set, multiset, list, interval, IS)'), nl,
   write('        - forall(X in A, G),'), nl, 
   write('          X variable and G any {log} goal containing X'), nl,  
   write('        - forall(X in A, exists(V,G)),'),nl,
   write('        - forall(X in A, exists([V1,...,Vn],G)),'), nl, 
   write('          V1,...,Vn variables local to G'), nl,
   nl.   

h(constraints) :- 
   nl,    
   write('%%%%%%%%%   {log} constraints  %%%%%%%%%'),
   nl, nl,
write('   1.  General constraints:'), nl,
   write('       (u: any term; t: any term but not a CP nor a RIS; '), nl,
   write('        A: variable, set, multiset, list, interval, CP, IS, RIS)'), nl,
   write('        - u1 = u2  (equality)'), nl,
   write('        - u1 neq u2  (non-equality)'), nl, 
   write('        - t in A (membership)'), nl,
   write('        - t nin A (non-membership)'), nl,   
   nl, 
write('   2.  Set constraints:'), nl,
   write('       (A, B, C: variable, set, interval, IS, CP) '), nl,
   write('        - un(A,B,C)/nun(A,B,C) (union/not-union)'), nl,
   write('        - disj(A,B)/ndisj(A,B) (disjointness/non-disjointness)'), nl,
   write('        - inters(A,B,C)/ninters(A,B,C) (intersection/not-intersection)'), nl,
   write('        - subset(A,B)/nsubset(A,B) (subset/not-subset)'), nl,
   write('        - ssubset(A,B) (strict subset)'), nl,
   write('        - diff(A,B,C)/ndiff(A,B,C) (difference/not-difference)'), nl,
   write('        - sdiff(A,B,C) (symmetric difference)'), nl,
   write('        - less(A,t,B) (element removal; t any term)'), nl,
   write('       (D: variable, set, interval, IS; '), nl,
   write('        Aint: variable, interval, set or IS of non-negative integers; '), nl,
   write('        n: variable, integer constant)'), nl,
   write('        - size(D,n) (cardinality)'), nl,
   write('        - sum(Aint,n) (sum all elements (non-negative integers only))'), nl,
   write('        - smin(Aint,n) (minimum element)'), nl,
   write('        - smax(Aint,n) (maximum element)'), nl,
   write('       (u: any term) '), nl,
   write('        - set(u)/nset(u) (u is/is_not a set)'), nl,  
   write('        - pair(u)/npair(u) (u is/s_not a pair)'), nl, 
   write('        - bag(u) (u is a multiset)'), nl, 
   write('        - list(u) (u is a list)'), nl, 
   nl,
write('   3.  Integer constraints:'), nl,
   write('       (e: integer expression; n: variable or integer constant)'), nl,
   write('        - n is e1 (equality - with evaluation of expression e)'), nl,
   write('        - e1 =< e2 (less or equal), e1 < e2 (less)'), nl,  
   write('        - e1 >= e2 (greater or equal), e1 > e2 (greater)'), nl,  
   write('        - e1 =:= e2 (equal), e1 =\\= e2 (not equal)'), nl,  
   write('        - integer(n)/ninteger(n) (n isis_not an integer number)'), nl,  
   nl, 
write('   4.  Binary relation and partial function constraints:'), nl,   
   write('       (A: variable, set, interval, IS, CP; R, RR: variable, binary relation, CP) '), nl,
   write('        - dom(R,A)/ndom(R,A) (domain/not-domain)'), nl, 
   write('        - inv(R,RR)/ninv(R,RR) (inverse/not-inverse)'), nl,   
   write('       (S: variable, binary relation) '), nl,  
   write('        - ran(S,A)/nran(S,A) (range/not-range)'), nl,   
   write('        - comp(S1,S2,S3)/ncomp(S1,S2,S3) (composition/not-composition)'), nl, 
   write('       (B: variable, set, IS) '), nl,
   write('        - id(B,S) (identity relation)'), nl,   
   write('        - dres(B,S1,S2) (domain restriction)'), nl,   
   write('        - rres(S1,B,S2) (range restriction)'), nl,   
   write('        - dares(B,S1,S2) domain anti-restriction)'), nl,   
   write('        - rares(S1,B,S2) (range anti-restriction)'), nl, 
   write('        - rimg(S,B1,B2) (relational image)'), nl,   
   write('        - oplus(S1,S2,S3) (overriding)'), nl,  
   write('       (F: variable, partial function; t: any term but not a CP nor a RIS) '), nl,
   write('        - apply(F,t1,t2) (function application)'), nl,  
   write('       (u: any term) '), nl,
   write('        - rel(u)/nrel(u) (u is/is_not a binary relation)'), nl,  
   write('        - pfun(u)/npfun(u)(u is/is_not a partial function)'), nl,  
   nl.
        
h(builtins) :-
   h(sbuilt),
   h(pbuilt).

h(sbuilt) :-
   nl,
   write('%%%%%%%%% {log} specific built-in predicates %%%%%%%%%'),
   nl, nl,
   write('   -   halt/0: to leave the {log} interactive environment'),
        write(' (go back to the host environment) '), nl,
   write('   -   help/0: to get general help information about {log}'), nl,
   write('   -   prolog_call(G): to call any Prolog goal G from {log}'),nl,  
   write('   -   call(G), call(G,C): to call a {log} goal G, possibly getting constraint C'),nl,  
   write('   -   solve(G): like call(G) but all constraints generated by G are immediately solved'),nl,  
   write('   -   consult_lib/0: to consult the {log} library file setloglib.slog'),nl,  
   write('   -   add_lib(F): to add any file F to the {log} library '),nl,  
   write('   -   G!: to make a {log} goal G deterministic'), nl,
   write('   -   delay(G,C), G, C {log} goals: to delay execution of G '),nl,     
   write('       until either C holds or the computation ends; '), nl,
   write('   -   delay(irreducible(G),C), G, C {log} goals: to delay execution of G '),nl,
   write('       until C holds; otherwise return irreducible(G)'), nl,
   write('   -   labeling(X): to force labeling for the domain variable X'),nl,
   write('   -   strategy(S): to change goal atom selection strategy to S'),nl,
   write('       (S: cfirst, ordered, cfirst(list_of_atoms))'), nl, 
   write('   -   noirules/0, irules/0: to deactivate/activate inference rules '),nl,
   write('       (default: irules)'), nl, 
   write('   -   nolabel/0, label/0: to deactivate/activate labeling on integer variables'),nl,
   write('       (default: label; possible unreliable solutions when nolabel)'), nl, 
   write('   -   noneq_elim/0, neq_elim/0: to deactivate/activate elimination of neq-'),nl,
   write('       constraints (default: neq_elim; possible unreliable solutions when noneq_elim)'), nl, 
   write('   -   noran_elim/0, ran_elim/0: to deactivate/activate elimination of ran-'),nl,
   write('       constraints of the form ran(R,{...})'), nl, 
   write('       (default: ran_elim; possible unreliable solutions when noran_elim)'), nl, 
   write('   -   notrace/0, trace(Mode): to deactivate/activate constraint solving tracing; '),nl,
   write('       Mode=sat: general, Mode=irules: inference rules only (default: notrace)'), nl, 
   write('   -   time(G,T): to get CPU time (in milliseconds) for solving goal G'),
   nl.

h(pbuilt) :-
   nl,
   write('%%%%%%%% Prolog-like built-in predicates (redefined in {log} %%%%%%%%'),
   nl, nl,
   write_built_list,
   write('   -   read/1'),nl,
   write('   -   write/1'),nl,
   write('   -   call/1'),nl,
   write('   -   assert/1'),nl,
   write('   -   consult/1'),nl,
   write('   -   listing/0'),nl,
   write('   -   abolish/0'),nl.
  
h(lib) :-
   nl,
   write('%%%%%%%% {log} library %%%%%%%%'), nl, nl,
   check_lib,
   nl. 

h(prolog) :- 
   nl,
   write('%%%%%%%% Prolog predicates for accessing {log} facilities %%%%%%%%%'),
   nl,nl,
   write('   -   setlog/0: to enter the {log} interactive environment'),nl,
   write('   -   setlog(G), setlog(G,C): to call a {log} goal G, '), nl,
   write('       possibly getting an (output) {log} constraint C'), nl,
   write('   -   setlog_InOut(G,InCLst,OutCLst), setlog_InOut_partial(G,InCLst,OutCLst), '), nl,
   write('       setlog_InOut_sc(C,InCLst,OutCLst): to solve a {log} goal G / constraint C '), nl,
   write('       with a (possibly empty) input constraint list InCLst '), nl,
   write('       and output constraint list OutCLst '), nl,
   write('   -   setlog_consult(F): to consult a {log} file F '),nl,
   write('   -   consult_lib: to consult the {log} library file '),nl,
   write('   -   setlog_clause(Cl): to add a {log} clause Cl to the current {log} program '),nl,
   write('   -   setlog_config(list_of_params): to modify {log} configuration parameters '),nl,
   write('       (parameters: strategy(S), path(Path), rw_rules(File))'), nl,
   write('   -   setlog_rw_rules: to load the filtering rule library'),
   nl.
 
write_built_list :-
   sys(N,Ar),
   write('   -   '),write(N),write('/'),write(Ar),nl,
   fail.
write_built_list.
 
check_lib :-
   solve(setlog_lib_help,_),!.
check_lib :-
   write('{log} library predicates not available'),nl,
   write('Type consult_lib to load the {log} library '),nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     The inference engine     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
%%%% solve(+Goal,-Constraint)            Goal: {log} goal in external form
%
solve(Goal_int_ruq,Constr):-   
       transform_goal(Goal_int_ruq,GoalNew),    
%DBG%       nl,write('NEW GOAL: '),write(GoalNew),nl,  
       solve_goal_fin(GoalNew,Constr).

%%%% solve_goal_fin(+Goal,-Constraint)   Goal: {log} goal in internal form
%
solve_goal_fin(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_fin_constr(GClist,GAlist,ClistNew).

solve_goal_fin_constr(GClist,GAlist,ClistNew):-  
       solve_goal_constr(GClist,GAlist,Clist), 
       final_sat(Clist,ClistNew).

%%%% solve_goal(+Goal,-Constraint)       Goal: {log} goal in internal form
%
solve_goal(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_constr(GClist,GAlist,ClistNew). 

%%%% solve_goal_constr(+Constraint,+Non_Constraint,-Constraint)
%
solve_goal_constr(Clist,[],CListCan):- !, 
       sat(Clist,CListCan,nf). 
solve_goal_constr(Clist,[true],CListCan):- !, 
       sat(Clist,CListCan,nf). 
solve_goal_constr(Clist,[A|B],CListOut):-
       sat(Clist,ClistSolved,nf),
       sat_or_solve(A,ClistSolved,ClistNew,AlistCl,nf),
       append(AlistCl,B,AlistNew),
       solve_goal_constr(ClistNew,AlistNew,CListOut).

sat_or_solve(A,Clist_in,Clist_out,[],F) :-
       atomic_constr(A),!,
       sat([A|Clist_in],Clist_out,F).
sat_or_solve(A,Clist_in,Clist_out,Alist_out,_) :-
       ssolve(A,ClistCl,Alist_out),
       append(Clist_in,ClistCl,Clist_out).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%%%% ssolve(+Atom,-Constraint,-Non_Constraint)

ssolve(true,[],[]):- !.                  %% unit goal

ssolve(neg A,ClistNew,[]):-              %% simplified constructive negation
        !,c_negate(A,ClistNew).
ssolve(naf A,ClistNew,[]):-              %% negation as failure
        !,naf_negate(A,ClistNew).

ssolve((G1 or G2),ClistNew,[]):-         %% goal disjunction 
        !,(solve_goal(G1,ClistNew)
          ;
           solve_goal(G2,ClistNew) ).

ssolve(call(A),C,[]):-                   %% meta call    
        !,solve_goal(A,C).
ssolve(call(A,C),C,[]):-                 %% meta call       
        !,solve_goal(A,C).

ssolve(solve(A),C,[]):-                  %% forces goal A to be completely solved    
        !,solve_goal_fin(A,C).

ssolve((A)!,C,[]):-                      %% deterministic call
        !,solve_goal(A,C),!.
  
ssolve(ruq_call(S,InName,VarList),Cout,[]) :- !,      %% RUQs
        solve_RUQ(S,InName,VarList,[],Cout).   

ssolve(sf_call(S,GName,PName,VarList),Cout,[]) :- !,  %% SF
        solve_SF(S,GName,PName,VarList,[],Cout).   

ssolve(prolog_call(A),[],[]):-    %% Prolog call (any predicate)
        nonvar(A),!,A.   
                 
ssolve(A,[],[]):-                 %% {log} built-in predicates inherited from Prolog
        nonvar(A),functor(A,F,N),
        sys(F,N),!,A.   

ssolve(A,C,[]):-                  %% {log} specific built-in predicates
        sys_special(A,C),!.   

ssolve(labeling(X),[],[]):-       %% explicit labeling for integer variables
        nonvar(X),!. 
ssolve(labeling(X),[],[]):- !,   
        labeling(X).         

ssolve(label,[],[]):- !,          %% (re-)activate automatic labeling
        cond_retract(nolabel).
ssolve(nolabel,[],[]):-           %% deactivate automatic labeling
        nolabel,!.
ssolve(nolabel,[],[]):- !,   
        assert(nolabel).

ssolve(notrace,[],[]):- !,        %% deactivate constraint solving tracing
        retract_trace.
ssolve(trace(sat),[],[]):-        %% activate constraint solving tracing
        trace(sat),!.
ssolve(trace(irules),[],[]):-        
        trace(irules),!.
ssolve(trace(Mode),[],[]):- !,
        (Mode==sat,! ; Mode==irules),   
        assert(trace(Mode)).

ssolve(neq_elim,[],[]):- !,       %% (re-)activate automatic neq elimination
        cond_retract(noneq_elim).
ssolve(noneq_elim,[],[]):-        %% deactivate automatic neq elimination
        noneq_elim,!.
ssolve(noneq_elim,[],[]):- !,     
        assert(noneq_elim).

ssolve(ran_elim,[],[]):- !,       %% (re-)activate automatic ran elimination
        cond_retract(noran_elim).
ssolve(noran_elim,[],[]):-        %% deactivate automatic ran elimination
        noran_elim,!.
ssolve(noran_elim,[],[]):- !,    
        assert(noran_elim).

ssolve(comp_elim,[],[]):- !,      %% (re-)activate automatic comp elimination
        cond_retract(nocomp_elim).
ssolve(nocomp_elim,[],[]):-       %% deactivate automatic comp elimination
        nocomp_elim,!.
ssolve(nocomp_elim,[],[]):- !,    
        assert(nocomp_elim).

ssolve(irules,[],[]):- !,         %% (re-)activate automatic application of inference rules
        cond_retract(noirules).
ssolve(noirules,[],[]):-          %% deactivate automatic application of inference rules
        noirules,!.
ssolve(noirules,[],[]):- !,   
        assert(noirules).

ssolve(strategy(Str),[],[]):- !,  %% change goal atom selection strategy    
        retract(strategy(_)),
        assert(strategy(Str)).

ssolve(int_solver(Slv),[],[]):-   %% get the current integer solver    
        var(Slv),!,
        int_solver(Slv).
ssolve(int_solver(Slv),[],[]):- !,  %% change the integer solver    
        cond_retract(int_solver(_)),
        assert(int_solver(Slv)).

ssolve(nofinal,[],[]):- !,        %% deactivate final mode for constraint solving
        cond_retract(final).
ssolve(final,[],[]):- !,          %% activate final mode for constraint solving
        set_final.

ssolve(nosubset_elim,[],[]):- !,  %% deactivate automatic subset elimination
        cond_retract(subset_elim).
ssolve(subset_elim,[],[]):-       %% (re-)activate deactivate automatic subset elimination
        subset_elim,!.
ssolve(subset_elim,[],[]):- !,   
        assert(subset_elim).

ssolve(A,C,D):-                   %% program defined predicates              
        our_clause(A,B,C1),
        constrlist(B,C2,D),
        append(C1,C2,C).

our_clause(A,B,C):-
        functor(A,Pname,N),
        functor(P,Pname,N),
        isetlog((P :- B),_), 
        sunify(P,A,C).

cond_retract(C) :-
       retract(C),!.
cond_retract(_).

retract_trace :-
        retractall(trace(_)),!.
retract_trace.


%%%% constrlist(+Atom_conj,-Constraint_list,-Constraint/Non_Constraint_list)

constrlist(A,CList,C_NCList) :-    
        constrlist(A,CList,StdC_NCList,SpecC_NCList),
        append(SpecC_NCList,StdC_NCList,C_NCList).
constrlist(A & B,[A|B1],B2,B3):-
        selected_atomic_constr(A),!,  
        constrlist(B,B1,B2,B3).         
constrlist(A & B,B1,B2,[A|B3]):-
        selected_user_atom(A),!,  
        constrlist(B,B1,B2,B3).         
constrlist(A & B,B1,[A|B2],B3):-
        !,constrlist(B,B1,B2,B3).                       
constrlist(A,[A],[],[]):-
        selected_atomic_constr(A),!.   
constrlist(A,[],[],[A]):-
        selected_user_atom(A),!.   
constrlist(A,[],[A],[]).

selected_atomic_constr(A) :-       
        strategy(cfirst),!,        %% cfirst: select primitive constraints first    
        atomic_constr(A).
selected_atomic_constr(A) :-
        strategy(cfirst(_)),!,
        atomic_constr(A).
selected_atomic_constr(A) :-
        strategy(ordered),!,       %% ordered: select all atoms in the order they occur    
        A = (_ = _).

selected_user_atom(A) :-           
        strategy(cfirst(LAtoms)),  %% cfirst(LAtoms): select atoms in LAtoms just after primitive constraints  
        member(A,LAtoms).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Negation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

naf_negate(A,[]) :-                 %% Negation as Failure
       \+ solve_goal_fin(A,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

c_negate(A,ClistNew) :-             %% Simplified Constructive Negation 
       chvar([],L1,A,[],L1new,B),
       constrlist(B,Clist,Alist),
       solve_goal_fin_constr(Clist,Alist,Clist0),
       final_sat(Clist0,Clist1),!, 
       dis(L1,L1new,Dis),
       append(Clist1,Dis,CC),
       neg_solve(CC,ClistNew,L1).
c_negate(_A,[]). 
       
neg_solve([],[],_) :- !, fail.
neg_solve(Clist,ClistNew,LVars) :-
       neg_constr_l(Clist,ClistNew,LVars).     

neg_constr_l([],_,_) :- !,fail.
neg_constr_l(Clist,ClistNew,LVars) :-
       member(C,Clist),
       neg_constr(C,ClistNew,LVars).       

neg_constr(A nin B,[A in B],_) :- !.           
neg_constr(A neq B,[],LVars) :- !,            
      extract_vars(B,V),
      subset_strong(V,LVars),
      sunify(A,B,_).     
neg_constr(A = B,[A neq B],LVars) :-   
      extract_vars(B,V),
      subset_strong(V,LVars),!.
neg_constr(_A = _B,_,_) :-   
      print_warning('***WARNING***: unimplemented form of negation').

dis([],[],[]):-!.
dis([X|L1],[Y|L2],[X=Y|L3]):-
      nonvar(Y),!,
      dis(L1,L2,L3).
dis([X|L1],[Y|L2],[X=Y|L3]):-
      var(Y),
      member_strong(Y,L2),!,
      dis(L1,L2,L3).
dis([X|L1],[Y|L2],L3):-
      X=Y,
      dis(L1,L2,L3).     

print_warning(Msg) :-
       \+nowarning,!,
       nl, write(Msg), nl,
       assert(nowarning).
print_warning(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%  Intensional sets and RUQs processing   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Intensional sets

solve_SF(S,_GName,PName,VarList,Cin,Cout) :- 
        nonvar(S), S = {},!,
        InPred =.. [PName,{}|VarList],  
        check_subset_elim(Ck),
        solve_goal_fin_constr(Cin,[neg(InPred & true)],Cout),
        restore_subset_elim(Ck).
        % print_warning_SF(VarList).
solve_SF({},_GName,PName,VarList,Cin,Cout) :- 
        InPred =.. [PName,{}|VarList],     
        check_subset_elim(Ck),  
        solve_goal_fin_constr(Cin,[neg(InPred & true)],Cout),
        restore_subset_elim(Ck).
        % print_warning_SF(VarList).
solve_SF(S,GName,_PName,VarList,_Cin,Cout) :- 
        InPred =.. [GName,X|VarList],
        check_subset_elim(Ck),  
        setof(X,solve_goal_fin(InPred,C1),L),
        restore_subset_elim(Ck),  
        list_to_set(L,S,C2),
        append(C2,C1,Cout).
        % print_warning_SF(VarList).

%print_warning_SF(VarList) :-      % uncomment to check possibly unsafe uses of intensional sets
%         \+ground(VarList),!,     
%         print_warning('***WARNING***: uninstantiated free vaiable in intensional set').

check_subset_elim(_) :-
        subset_elim,!.
check_subset_elim(added) :-
        assert(subset_elim).

restore_subset_elim(R) :-
        var(R),!.
restore_subset_elim(added) :-
        retract(subset_elim).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% RUQs

solve_RUQ(S,_,_,C,C) :-
        nonvar(S), 
        empty_aggr(S),!.
solve_RUQ(S,InName,VarList,Cin,Cout) :-
        nonvar(S), S = int(L,H),!,                % solve RUQ's over intervals
        force_bounds_values(L,H,IntC),
        check_subset_elim(Ck),  
        solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout1),
        append(IntC,Cout1,Cout),
        restore_subset_elim(Ck).
solve_RUQ(S,InName,VarList,Cin,Cout) :-           % over a given aggregate
        nonvar(S),!,
        aggr_comps(S,X,R),
        InPred =.. [InName,X|VarList],
        check_subset_elim(Ck), 
        solve_goal_fin_constr(Cin,[InPred],C2),
        restore_subset_elim(Ck),  
        solve_RUQ(R,InName,VarList,C2,Cout).
solve_RUQ(S,_,_,C,C) :-
        var(S), S = {}.
solve_RUQ(S,InName,VarList,Cin,Cout) :-           % over an unspecified aggregate
        var(S), S = R with X,                             
        InPred =.. [InName,X|VarList],
        check_subset_elim(Ck), 
        solve_goal_fin_constr([X nin R|Cin],[InPred],C2),
        restore_subset_elim(Ck),  
        solve_RUQ(R,InName,VarList,C2,Cout), 
        aggr_ordered(S).

solve_RUQ_int(int(L,L),InName,VarList,Cin,Cout) :- !,   
        InPred =.. [InName,L|VarList],    % forall(X in int(L,L),InName(X,VarList))
        solve_goal_fin_constr(Cin,[InPred],Cout).
solve_RUQ_int(int(L,H),InName,VarList,Cin,Cout) :-    
        InPred =.. [InName,L|VarList],    % forall(X in int(L,H),InName(X,VarList))
        solve_goal_fin_constr(Cin,[InPred],C2),
        L1 is L + 1,
        solve_RUQ(int(L1,H),InName,VarList,C2,Cout).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for solve_RUQ/5

aggr_ordered(S) :- var(S),!.
aggr_ordered({}) :- !.
aggr_ordered(S) :- 
       S = R with X,
       in_order(X,R), 
       aggr_ordered(R).

in_order(_A,S) :- var(S),!.
in_order(_A,{}) :- !.
in_order(A,S) :-  
       S = _R with _B,
       var(A), !.
in_order(A,S) :-  
       S = R with B,
       var(B), in_order(A,R),!.
in_order(A,S) :-  
       S = _R with B,
       A @=< B.

force_bounds_values(A,B,IntC) :-
       solve_int(A =< B,IntC),     
       (var(A),!, labeling(A) ; true),
       (var(B),!, labeling(B) ; true).

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%  "Built-in" predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Prolog built-in predicates

sys(nl,0).
sys(ground,1).
sys(var,1).
sys(nonvar,1).
sys(name,2).
sys(functor,3).
sys(arg,3).
sys(=..,2).
sys(==,2).
sys(\==,2).
sys(@<,2).
sys(@>,2).
sys(@=<,2).
sys(@>=,2).
%%********* list to be completed!!********* 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% {log} built-in predicates

sys_special(write(T),[]) :-            %% write
      !,postproc(T,NewT),
      write(NewT).

sys_special(read(T),C) :-              %% read
      !,setlog_read(Tout),
      preproc(Tout,T,C).

sys_special(assert(Clause),[]):-       %% assert
      !,setassert(Clause).

sys_special(consult_lib,[]):-          %% stores clauses contained in the {log} library file into                       
      !,rem_clause(lib), rem_clause(tmp(lib)),       %% the current program in the library ctxt   
      setlog_open('setloglib.slog',read,FileStream), %% (removing all clauses possibly stored 
      switch_ctxt(lib,OldCtxt),                      %% in the same ctxt) 
      read_loop_np(FileStream),
      switch_ctxt(OldCtxt,_),
      close(FileStream). 

sys_special(add_lib(File),[]):-        %% adds clauses contained in file F to the current 
      !, setlog_open(File,read,FileStream),          %% program in the library ctxt (without
      switch_ctxt(lib,OldCtxt),                      %% removing existing clauses)
      read_loop_np(FileStream),
      switch_ctxt(OldCtxt,_),
      close(FileStream). 

sys_special(consult(File),[]):-        %% stores clauses contained in file F into                            
      !, setlog_open(File,read,FileStream),          %% the current program in the user ctxt
      write('consulting file '), write(File),        %% (removing all clauses possibly stored
      write(' ...'), nl,                             %% in the same ctxt)
      sys_special(abolish,_),
      read_loop(FileStream,1),
      write('file '), write(File), write(' consulted.'), nl,
      close(FileStream). 

sys_special(consult(File,mute),[]):-   %% consult using mute mode 
      !, setlog_open(File,read,FileStream), 
      sys_special(abolish,_),
      read_loop_np(FileStream),
      close(FileStream). 

sys_special(listing,[]):-              %% listing
      !,nl, list_all.
          
sys_special(abolish,[]):-              %% abolish
      !,rem_clause(usr),
      rem_clause(tmp(usr)).

sys_special(abort,[]):-                %% abort
      !,nl, write('Execution aborted'), nl,
      setlog. 

sys_special(help,[]):- !, h(setlog).   %% help
sys_special(h(X),[]):- !, h(X). 

sys_special(halt,[]):-                 %% halt
%     confirm, !, 
      abort.     
% sys_special(halt,[]). 

sys_special(time(G,T),C):-             %% time
      statistics(runtime,_),
      write('STARTING ...'),nl,
      solve_goal_fin(G,C),!,
      write('END'),nl,
      statistics(runtime,[_,T]).
sys_special(time(_G,T),_C):-           %% time
      write('END'),nl,
      statistics(runtime,[_,T]).

consult_mute(File) :-                    %% like setlog(consult(File),_)
      setlog_open(File,read,FileStream), %% but no message is sent to the std output
      sys_special(abolish,_),
      read_loop_np(FileStream),
      close(FileStream). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for sys_special/2

setlog_read(Term) :- 
      on_exception(Msg,read(Term),syntax_error_msg(Msg)).   

setlog_open(File,Mode,Stream) :- 
      mk_file_name(File,FullName),       
      on_exception(Msg,open(FullName,Mode,Stream),existence_error_msg(Msg)).    

existence_error_msg(Text) :-
      write('Existence error:'), nl,    
      write('file '), write(Text), write(' does not exist'), nl,
      fail.

rem_clause(Ctxt):-              
      retract(isetlog(_,Ctxt)), 
      fail. 
rem_clause(_).

confirm :-
      nl, write('Are you sure you want to leave {log}? (y/n)'),
      get(C), skip(10),
      C == 121,
      nl, write('Bye, bye. See you later').

mk_file_name(F,FullName) :-             
      path(Dir),
      name(Dir,DirList),
      name(F,FList),
      append(DirList,FList,FullNameList),
      name(FullName,FullNameList).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%% Program storing and printing %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Consulting and storing {log} clauses  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

context(usr).

read_loop_np(FileStream):-
       setlog_read(FileStream,Clause), 
       Clause \== end_of_file,!, 
       assert_or_solve(Clause),   
       read_loop_np(FileStream).
read_loop_np(_).

read_loop(FileStream,N):-
       setlog_read(FileStream,Clause), 
       Clause \== end_of_file,!, 
       assert_or_solve(Clause,N),
       N1 is N + 1,
       read_loop(FileStream,N1).
read_loop(_,_).

setlog_read(Stream,Term) :- 
       on_exception(Msg,read(Stream,Term),syntax_error_cont_msg(Msg)).   

assert_or_solve((:- Goal)):-!,  
       solve(Goal,_).
assert_or_solve(Clause):- 
       setassert(Clause).

assert_or_solve((:- Goal),_):-!,
       solve(Goal,_).
assert_or_solve(Clause,N):- 
       setassert(Clause),
       write('Clause '), write(N), write(' stored'), nl.

setassert(Clause):- 
       context(Ctxt),
       setassert(Clause,Ctxt).
setassert(Clause,Ctxt):- 
       transform_clause(Clause,BaseClause),
       assert(setlog:isetlog(BaseClause,Ctxt)).

switch_ctxt(NewCtxt,OldCtxt) :-
       retract(context(OldCtxt)),
       assert(context(NewCtxt)).

tmp_switch_ctxt(OldCtxt) :-
       context(OldCtxt), 
       functor(OldCtxt,tmp,_),!.
tmp_switch_ctxt(OldCtxt) :-
       retract(context(OldCtxt)),
       NewCtxt =.. [tmp,OldCtxt],
       assert(context(NewCtxt)).

syntax_error_cont_msg(Text) :-
       write('Syntax error:'), nl,      
       write(Text), nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%   Program listing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_all :-                            
      isetlog((H :- B),usr), 
      postproc(H,Hnew), write(Hnew), 
      write_body(B).
list_all. 

write_body(true) :-
      !, write('.'),nl,nl,
      fail.
write_body(type(_) & true) :-
      !, write('.'),nl,nl,
      fail.
write_body(B) :-
      write((:-)), nl, 
      write('   '), postproc(B,Bnew), write_atoms(Bnew), write('.'),nl,nl,
      fail.

write_atoms(B & true) :-
      !, write_atom(B).
write_atoms(B1 & B2) :- 
      write_atom(B1), 
      (B2 = (type(_) & _), ! 
      ;
       write(' & '), nl, write('   ')), 
      write_atoms(B2).

write_atom(A) :-    
      var(A),!,
      write(A).
write_atom(ruq_call(Aggr,Goal_name,FV)) :- 
      !, write('forall('),write(X),write(' in '),write(Aggr),write(','), 
      RUQ_body_pred =.. [Goal_name,X|FV], isetlog((RUQ_body_pred :- RUQ_body),_),
      extract_vars(RUQ_body,Vars),
      remove_list([X|FV],Vars,LocalVars),
      postproc(RUQ_body,RUQ_bodyNew),
      (LocalVars = [],!,
       write_atoms(RUQ_bodyNew), write(')')
       ;
       write('exists('),write(LocalVars),write(','),
       write_atoms(RUQ_bodyNew), write('))') 
      ).
write_atom(type(_)) :- !.
write_atom(neg A) :- !,
      write('neg '), 
      write('('), write_atoms(A), write(')').
write_atom(naf A) :- !,
      write('naf '), 
      write('('), write_atoms(A), write(')').
write_atom(call(A)) :- !,
      write(call),
      write('('), write_atoms(A), write(')').
write_atom(call(A,C)) :- !,     
      write(call),
      write('('), write_atoms(A),write(','),write(C),write(')').
write_atom(solve(A)) :- !,
      write(solve),
      write('('), write_atoms(A), write(')').
write_atom((A)!) :- !,
      write('('),
      write_atoms(A),
      write(')!').
write_atom(delay(A,G)) :- !,
      write(delay),write('('),
      write_atoms(A),write(','),
      write_atoms(G),
      write(')').
write_atom((A1 or A2)) :- !,
      write('('), write_atoms(A1),
      write(' or '),
      write_atoms(A2), write(')').
write_atom(B) :- 
      write(B).

               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%% The {log] Constraint Solver  %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             atomic_constr/1,
%             sat/3,
%             final_sat/2,
%             sunify/3,
%        
%             solve_int/1
%             add_intv/2,
%             labeling/1,
%             test_integer_expr/1
%             integer_expr/1
%             is_int_var/1
%             check_int_constr/2
%             finalize_int_constr/1

%%%%%%%%%%%%%%%%%%% Atomic constraints %%%%%%%%%%%%%%%%%%%%%%

atomic_constr(_ nin _) :-!.
atomic_constr(_ in _) :-!. 
atomic_constr(_ neq _) :-!.  
atomic_constr(_ = _) :-!.      
atomic_constr(type(_)) :-!.
atomic_constr(set(_)) :-!.
atomic_constr(integer(_)) :-!.        
atomic_constr(un(_,_,_)) :-!.
atomic_constr(subset(_,_)) :-!.  
atomic_constr(disj(_,_)) :-!.
atomic_constr(inters(_,_,_)) :-!.   
atomic_constr(ssubset(_,_)) :-!.  

atomic_constr(delay(_,_)) :-!.
atomic_constr(solved(_,_,_,_)) :-!.   
atomic_constr(glb_state(_)) :-!.     

atomic_constr(size(_,_)) :-!.   
atomic_constr(sum(_,_)) :-!.  
atomic_constr(smin(_,_)) :-!.             
atomic_constr(smax(_,_)) :-!.  
        
atomic_constr(bag(_)) :-!.
atomic_constr(list(_)) :-!.

atomic_constr(_ is _) :-!.     
atomic_constr(_ =< _) :-!.      
atomic_constr(_ < _) :-!.       
atomic_constr(_ >= _) :-!.      
atomic_constr(_ > _) :-!. 
      
atomic_constr(pfun(_)) :-!.
atomic_constr(rel(_)) :-!.   
atomic_constr(pair(_)) :-!.     
atomic_constr(dom(_,_)) :-!. 
atomic_constr(inv(_,_)) :-!.    
atomic_constr(id(_,_)) :-!.        
atomic_constr(ran(_,_)) :-!. 
atomic_constr(comp(_,_,_)) :-!.  
atomic_constr(dompf(_,_)).             
atomic_constr(comppf(_,_,_)) :-!. 
atomic_constr(apply(_,_,_)) :-!.  
atomic_constr(dres(_,_,_)) :-!.
atomic_constr(drespf(_,_,_)) :-!.
atomic_constr(rres(_,_,_)) :-!.  
atomic_constr(dares(_,_,_)) :-!.
atomic_constr(rares(_,_,_)) :-!.  
atomic_constr(oplus(_,_,_)) :-!.  

atomic_constr(nset(_)) :-!.
atomic_constr(ninteger(_)) :-!.        
atomic_constr(npair(_)) :-!.
atomic_constr(npfun(_)) :-!.
atomic_constr(nrel(_)) :-!.

atomic_constr(nun(_,_,_)) :-!.
atomic_constr(ndisj(_,_)) :-!.
atomic_constr(ndom(_,_)) :-!.
atomic_constr(ninv(_,_)) :-!.
atomic_constr(ncomp(_,_,_)) :-!.

atomic_constr(nran(_,_)) :-!.
atomic_constr(ndres(_,_,_)) :-!.
%
atomic_constr(ndares(_,_,_)) :-!.
atomic_constr(nrres(_,_,_)) :-!.
atomic_constr(nrares(_,_,_)) :-!.
atomic_constr(napply(_,_,_)) :-!.
atomic_constr(nrimg(_,_,_)) :-!.
atomic_constr(noplus(_,_,_)) :-!.
atomic_constr(nid(_,_)) :-!.


%%%%%%%%%%%%  Constraint solver main procedure %%%%%%%%%%%%   

%%%% sat(+Constraint,-Solved_Form_Constraint,+final/non-final)

sat([],[],_) :-!.
sat(C,SFC,F):- 
      trace_in(C,1),
      sat_step(C,NewC,R,F), 
      sat_cont(R,NewC,SFC,F).

sat_cont(R,NewC,SFC,F) :-           %if R=='stop', then no rule has changed the CS in the last 
      R == stop,!,                  %call to 'sat_step' (-> fixpoint); otherwise, call 'sat' again
      trace_out(NewC,1),
      norep_in_list_split(NewC,RedC,RedCS),   %remove possibly repeated constraints in the CS
                                              %and split the CS into <neq-constraints,other-constraints>      
      trace_in(RedC,2),
      global_check1(RedC,RedCS,RevC1,F),      %rewrite RedC to RevC
      global_check2(RevC1,RedCS,RevC,F),      %rewrite RedC to RevC
      (RevC == RedC,!,SFC=RevC,     %if RedC==RevC, then no rewriting has been applied:
       trace_out(NewC,2)
       ;                            %RevC is the resulting constraint; 
       sat(RevC,SFC,F)              %otherwise, call 'sat' again
      ).
sat_cont(_R,NewC,SFC,F) :-
      sat(NewC,SFC,F).

norep_in_list_split([],[],cs([],[])):-!.
norep_in_list_split([A|R],S,CS):-
        member_strong(A,R),!,
        norep_in_list_split(R,S,CS).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS)) :-
        A = (_ neq _),!,
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS)) :-
        type_constr(A),!,
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).
norep_in_list_split([A|R],[A|S],cs([A|NeqCS],OtherCS)) :-
        A = glb_state(_),!,
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).
norep_in_list_split([A|R],[A|S],cs(NeqCS,[A|OtherCS])) :-
        norep_in_list_split(R,S,cs(NeqCS,OtherCS)).

split_cs([],cs([],[])):-!.                    %split the CS into <neq-constraints,other-constraints> 
split_cs([A|R],cs([A|NeqCS],OtherCS)) :-
        (A = (_ neq _),!;
         type_constr(A),!;
         A = glb_state(_)
        ),!,
        split_cs(R,cs(NeqCS,OtherCS)).
split_cs([A|R],cs(NeqCS,[A|OtherCS])) :-
        split_cs(R,cs(NeqCS,OtherCS)).

%%%%%%%%%%%%%
%sat_step(InC,_OutC,_Stop,_F):-   %only for debugging purposes
%        write('    >>>>> sat step: '), write(InC),nl,
%        get0(_),
%        fail. 

sat_step([],[],stop,_F) :- !.
sat_step([C1|R1],R2,Z,F):- 
        sat_step(C1,[C1|R1],R2,Z,F). 

sat_step(glb_state(Rel),[glb_state(Rel)|R1],R2,Stop,F):-    
         (ground(Rel),!
          ;
          Rel =.. [_OP,E1,E2], E1 == E2,!
          ;
          Rel =.. [is,E1,E2], ground(E1), term_variables(E2,[_])
         ),!,    
         sat_step(R1,R2,Stop,F).
sat_step(glb_state(Rel),[glb_state(Rel)|R1],[glb_state(Rel)|R2],Stop,F):- !,       
         sat_step(R1,R2,Stop,F).

%%%%%%%%%%%%%             % equality/inequality constraints
sat_step(_ neq _,C,R2,Z,F):- !,
          sat_neq(C,R2,Z,F).
sat_step(_ = _,C,R2,Z,F):- !,
          sat_eq(C,R2,Z,F).
%%%%%%%%%%%%%             % membership/not membership constraints
sat_step(_ nin _,C,R2,Z,F):- !,
          sat_nin(C,R2,Z,F).
sat_step(_ in _,C,R2,Z,F):- !,
          sat_in(C,R2,Z,F).
%%%%%%%%%%%%%             % set/interval positive constraints
sat_step(un(X,Y,W),[un(X,Y,W)|R1],R2,Z,F):- !,  %GFR sostituire un(X,Y,W) nella lista con C (ovunque)
          sat_un([un(X,Y,W)|R1],R2,Z,F).
sat_step(subset(X,Y),[subset(X,Y)|R1],R2,Z,F):- !,     
          sat_sub([subset(X,Y)|R1],R2,Z,F).
sat_step(ssubset(X,Y),[ssubset(X,Y)|R1],R2,Z,F):- !,     
          sat_ssub([ssubset(X,Y)|R1],R2,Z,F).
sat_step(inters(X,Y,W),[inters(X,Y,W)|R1],R2,Z,F):- !,     
          sat_inters([inters(X,Y,W)|R1],R2,Z,F).
sat_step(disj(X,Y),[disj(X,Y)|R1],R2,Z,F):- !,
          sat_disj([disj(X,Y)|R1],R2,Z,F).
sat_step(size(X,Y),[size(X,Y)|R1],R2,Z,F):- !,       
          sat_size([size(X,Y)|R1],R2,Z,F).
sat_step(sum(X,Y),[sum(X,Y)|R1],R2,Z,F):- !,       
          sat_sum([sum(X,Y)|R1],R2,Z,F).   
sat_step(smin(X,Y),[smin(X,Y)|R1],R2,Z,F):- !,         
          sat_min([smin(X,Y)|R1],R2,Z,F).  
sat_step(smax(X,Y),[smax(X,Y)|R1],R2,Z,F):- !,            
          sat_max([smax(X,Y)|R1],R2,Z,F).      
%%%%%%%%%%%%%             % set/interval negative constraints
sat_step(nun(X,Y,W),[nun(X,Y,W)|R1],R2,Z,F):- !,
          sat_nun([nun(X,Y,W)|R1],R2,Z,F).
sat_step(ndisj(X,Y),[ndisj(X,Y)|R1],R2,Z,F):- !,
          sat_ndisj([ndisj(X,Y)|R1],R2,Z,F).               
%%%%%%%%%%%%%             % type constraints
sat_step(type(TypeC),[type(TypeC)|R1],R2,Z,F):- !,          % type(C), where C is a type constraint, 
          sat_step([TypeC|R1],R2,Z,F).          % is dealt with as C, but it is not printed when listing a program
sat_step(set(X),[set(X)|R1],R2,Z,F):- !,             
          sat_set([set(X)|R1],R2,Z,F).
sat_step(integer(X),[integer(X)|R1],R2,Z,F):-!,            
          sat_integer([integer(X)|R1],R2,Z,F).
sat_step(pair(X),[pair(X)|R1],R2,Z,F):- !,               
          sat_pair([pair(X)|R1],R2,Z,F).
sat_step(bag(X),[bag(X)|R1],R2,Z,F):- !,               
          sat_bag([bag(X)|R1],R2,Z,F).
sat_step(list(X),[list(X)|R1],R2,Z,F):- !,
          sat_list([list(X)|R1],R2,Z,F).
sat_step(nset(X),[nset(X)|R1],R2,Z,F):- !,             
          sat_nset([nset(X)|R1],R2,Z,F).
sat_step(ninteger(X),[ninteger(X)|R1],R2,Z,F):-!,            
          sat_ninteger([ninteger(X)|R1],R2,Z,F).
sat_step(npair(X),[npair(X)|R1],R2,Z,F):- !,               
          sat_npair([npair(X)|R1],R2,Z,F).
%%%%%%%%%%%%%             % control constraints
sat_step(delay(A,G),[delay(A,G)|R1],R2,Z,F):- !,
          sat_delay([delay(A,G)|R1],R2,Z,F).
sat_step(solved(C,G,Lev,Mode),[solved(C,G,Lev,Mode)|R1],R2,Z,F):- !,         % "solved" constraints: used to avoid 
          sat_solved([solved(C,G,Lev,Mode)|R1],R2,Z,F). % repeated additions of the same constraints
%%%%%%%%%%%%%             % arithmetic constraints
sat_step(X is Y,[X is Y|R1],R2,Z,F):-                  % ris set grouping
          nonvar(Y), is_ris(Y,Ris),!,
          check_ris(Ris),
          sat_riseq([X is Y|R1],R2,Z,F).
sat_step(X is Y,[X is Y|R1],R2,Z,F):- !,               % integer equality
          sat_eeq([X is Y|R1],R2,Z,F).
sat_step(_ =< _,C,R2,Z,F):- !,                    % integer comparison relations
          sat_crel(C,R2,Z,F).
sat_step(_ < _,C,R2,Z,F):- !,                    % integer comparison relations
          sat_crel(C,R2,Z,F).
sat_step(_ >= _,C,R2,Z,F):- !,                    % integer comparison relations
          sat_crel(C,R2,Z,F).
sat_step(_ > _,C,R2,Z,F):- !,                    % integer comparison relations
          sat_crel(C,R2,Z,F).
%%%%%%%%%%%%%             % binary relation and partial function positive constraints
sat_step(rel(X),[rel(X)|R1],R2,Z,F):- !,               
          sat_rel([rel(X)|R1],R2,Z,F).  
sat_step(pfun(X),[pfun(X)|R1],R2,Z,F):- !,               
          sat_pfun([pfun(X)|R1],R2,Z,F).
sat_step(dom(X,Y),[dom(X,Y)|R1],R2,Z,F):- !,
          sat_dom([dom(X,Y)|R1],R2,Z,F).
sat_step(ran(X,Y),[ran(X,Y)|R1],R2,Z,F):- !,
          sat_ran([ran(X,Y)|R1],R2,Z,F).
sat_step(comp(R,S,T),[comp(R,S,T)|R1],R2,Z,F):- !,
          sat_comp([comp(R,S,T)|R1],R2,Z,F).
sat_step(inv(X,Y),[inv(X,Y)|R1],R2,Z,F):- !,
          sat_inv([inv(X,Y)|R1],R2,Z,F).
sat_step(id(X,Y),[id(X,Y)|R1],R2,Z,F):- !,     
          sat_id([id(X,Y)|R1],R2,Z,F).
sat_step(dompf(R,A),[dompf(R,A)|R1],R2,Z,F):- !,
          sat_dompf([dompf(R,A)|R1],R2,Z,F).       
sat_step(comppf(R,S,T),[comppf(R,S,T)|R1],R2,Z,F):- !,
          sat_comppf([comppf(R,S,T)|R1],R2,Z,F).   
sat_step(dres(A,R,S),[dres(A,R,S)|R1],R2,Z,F):- !,
          sat_dres([dres(A,R,S)|R1],R2,Z,F).
sat_step(drespf(A,R,S),[drespf(A,R,S)|R1],R2,Z,F):- !,
          sat_drespf([drespf(A,R,S)|R1],R2,Z,F).
sat_step(rres(R,A,S),[rres(R,A,S)|R1],R2,Z,F):- !,
          sat_rres([rres(R,A,S)|R1],R2,Z,F).
sat_step(dares(A,R,S),[dares(A,R,S)|R1],R2,Z,F):- !,
          sat_dares([dares(A,R,S)|R1],R2,Z,F).
sat_step(rares(R,A,S),[rares(R,A,S)|R1],R2,Z,F):- !,
          sat_rares([rares(R,A,S)|R1],R2,Z,F).
sat_step(apply(S,X,Y),[apply(S,X,Y)|R1],R2,Z,F):- !,
          sat_apply([apply(S,X,Y)|R1],R2,Z,F).
sat_step(oplus(S,R,T),[oplus(S,R,T)|R1],R2,Z,F):- !,
          sat_oplus([oplus(S,R,T)|R1],R2,Z,F).

%%%%%%%%%%%%%             % binary relation and partial function negative constraints
sat_step(npfun(X),[npfun(X)|R1],R2,Z,F):- !,               
          sat_npfun([npfun(X)|R1],R2,Z,F).
sat_step(nrel(X),[nrel(X)|R1],R2,Z,F):- !,               
          sat_nrel([nrel(X)|R1],R2,Z,F).
sat_step(ndom(R,A),[ndom(R,A)|R1],R2,Z,F):- !,
          sat_ndom([ndom(R,A)|R1],R2,Z,F).
sat_step(ninv(R,S),[ninv(R,S)|R1],R2,Z,F):- !,
          sat_ninv([ninv(R,S)|R1],R2,Z,F).
sat_step(ncomp(R,S,T),[ncomp(R,S,T)|R1],R2,Z,F):- !,
          sat_ncomp([ncomp(R,S,T)|R1],R2,Z,F).
sat_step(nran(R,A),[nran(R,A)|R1],R2,Z,F):- !,
          sat_nran([nran(R,A)|R1],R2,Z,F).
sat_step(ndres(A,R,S),[ndres(A,R,S)|R1],R2,Z,F):- !,
          sat_ndres([ndres(A,R,S)|R1],R2,Z,F).
%
sat_step(ndares(A,R,S),[ndares(A,R,S)|R1],R2,Z,F):- !,
          sat_ndares([ndares(A,R,S)|R1],R2,Z,F).
sat_step(nrres(R,A,S),[nrres(R,A,S)|R1],R2,Z,F):- !,
          sat_nrres([nrres(R,A,S)|R1],R2,Z,F).
sat_step(nrares(R,A,S),[nrares(R,A,S)|R1],R2,Z,F):- !,
          sat_nrares([nrares(R,A,S)|R1],R2,Z,F).
sat_step(napply(S,X,Y),[napply(S,X,Y)|R1],R2,Z,F):- !,
          sat_napply([napply(S,X,Y)|R1],R2,Z,F).
sat_step(nrimg(R,A,B),[nrimg(R,A,B)|R1],R2,Z,F):- !,
          sat_nrimg([nrimg(R,A,B)|R1],R2,Z,F).
sat_step(noplus(A,R,S),[noplus(A,R,S)|R1],R2,Z,F):- !,
          sat_noplus([noplus(A,R,S)|R1],R2,Z,F).
sat_step(nid(X,Y),[nid(X,Y)|R1],R2,Z,F):- !,
          sat_nid([nid(X,Y)|R1],R2,Z,F).

%%%%%%%%%%%%%%%%%%%% constraint solving tracing

trace_in(C,L) :-
      trace(sat),!,
      write('>>> Entering Level '), write(L),nl, 
      write('>>> Input constraint: '), write(C), nl,
      write('Press return to continue '), nl,
      get0(_). 
trace_in(_,_).

trace_out(_C,L) :-
      trace(sat),!,
      write('<<< Level '), write(L), write(' fixed point reached'),nl,
%DBG% write('<<< Output constraint: '), write(C),nl,
      nl.
trace_out(_,_).

trace_irules(Rule) :-
      trace(irules),!,
      write('\n>>> Using inference rule '), write(Rule),nl.
trace_irules(_).
   
trace_firules(Rule) :-
      trace(irules),!,
      write('\n>>> Using filtering inference rule '), write(Rule),nl.
trace_firules(_).
  
trace_ffrules(Rule) :-
      trace(irules),!,
      write('\n>>> Using filtering fail rule '), write(Rule),nl.
trace_ffrules(_).
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%      Level 1     %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for general constraints (=, neq) %%%%%%%%%%%%%              
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% equality (=/2)

sat_eq([T1 = T2|R1],[T1 = T2|R2],Stop,nf):-        % int(A,B) = {} --> delayed until final_sat is called  
        nonvar(T1), T1 = int(A,B), var(A), var(B),
        nonvar(T2), is_empty(T2),!,                        
        sat_step(R1,R2,Stop,nf).                   
sat_eq([T1 = T2|R1],[T2 = T1|R2],Stop,nf):-        % {} = int(A,B)  --> delayed until final_sat is called 
        nonvar(T2), T2 = int(A,B), var(A), var(B),
        nonvar(T1), is_empty(T1),!,       
        %write(rule(eq_open_intv2)),nl,                 
        sat_step(R1,R2,Stop,nf).     
sat_eq([T1 = T2|R1],R2,R,F):-                      % ris = t or t = ris
        (nonvar(T1), is_ris(T1,_),!
        ;
         nonvar(T2), is_ris(T2,_)
        ),!,
        %write(rule(eq_ris)),nl,
        sat_eq_ris([T1 = T2|R1],R2,R,F).
sat_eq([T1 = T2|R1],R2,R,F):-                      % cp = t or t = cp
        (nonvar(T1), is_cp(T1,_,_),!
        ;
         nonvar(T2), is_cp(T2,_,_)
        ),!,
        sat_eq_cp([T1 = T2|R1],R2,R,F).
sat_eq([T1 = T2|R1],R2,c,F):-                      % t1 = t2 (t1, t2 not ris-term)
        %write(rule(sunify)),nl,
        sunify(T1,T2,C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).

%%%%%%%%%%% equality involving RIS

sat_eq_ris([T1 = T2|R1],R2,c,F) :-                 % ris(Z in D,...) = X  (var-ris D, var X)
        %write('1-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom,_,_,_,_)), var_ris(Dom),   
        var(T2), 
        occur_check(T2,T1),!,
        %write(rule('ris(var)=var')),nl,
        T2 = T1,
        sat_step(R1,R2,_,F).
sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F):-     % ris(Z in X,...)=X or ris(Z in D,t[X]...)=X  (var-ris D, var X) --> irreducible
        %write('2-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom,_,_,_,_)), var_ris(Dom),   
        var(T2),!, 
        %rite(rule('ris(X)=X')),nl,
        sat_step(R1,R2,Stop,F).  
     
sat_eq_ris([T1 = T2|R1],R2,c,F) :-                 % X = ris(...) --> ris(...) = X   (var X)
        %write('3-'),
        var(T1),!, 
        %write(rule('X=ris-->ris=X')),nl,
        sat_eq_ris([T2 = T1|R1],R2,_,F).           
sat_eq_ris([T1 = T2|R1],R2,c,F) :-                 % t = ris(...) (t not ris-term) ---> ris(...) = t
        %write('4-'),
        nonvar(T1), \+is_ris(T1,_),!,
        %write(rule('t=ris-->ris=t')),nl,
        sat_eq_ris([T2 = T1|R1],R2,_,F).  
                     
sat_eq_ris([T1 = T2|R1],R2,c,F):-                  % ris(X in {},...) = T (T any term, including another RIS)
        %write('5-'),
        nonvar(T1), is_empty(T1),!,
        %write(rule('ris({})=t')),nl,
        sunify(T2,{},C), append(C,R1,R3), 
        sat_step(R3,R2,_,F).

sat_eq_ris([T1 = E|R1],[T1 = E|R2],Stop,F):-       % ris(V,D,F,P) = {}   (var-ris D) --> irreducible   
        %write('6-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom,_,_,_,_)), var_ris(Dom),   
        nonvar(E), is_empty(E),!,       
        %write(rule('ris(var)={}')),nl,  
        sat_step(R1,R2,Stop,F).
sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F) :-   % ris(X in int(A.B),...) = T (int(A,B) open interval --> irreducible) 
        %write('7-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom,_,_,_,_)), 
        open_intv(Dom),!,     
        %write(rule('ris(int(A,B))=t')),nl,  
        sat_step(R1,R2,Stop,F).

sat_eq_ris([T1 = E |R1],R2,c,F):-                  % ris(V,{...},F,P) = {}   (nonvar-ris D)
        %write('8-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)), 
        nonvar(E), is_empty(E),
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,    
        %write(rule('ris(d)={}')),nl,
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        first_rest(Dom,CtrlExprNew,D,CNS), 
        (nonvar(CNS),!,
        append(CNS,R1,R3),
        chvar(LV,[],Vars,[Fl,CtrlExpr],[],VarsNew,[FlNew,_]),
        find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),      
        negate(FlNew,NegFl),
        mk_atomic_constraint(NegFl,NegFlD),!,
        sat_step([NegFlD,ris(CtrlExpr in D,V,Fl,P,PP) = E|R3],R2,_,F)
        ;
        sat_step([ris(CtrlExpr in D,V,Fl,P,PP) = E|R1],R2,_,F)).  
                   
sat_eq_ris([T1 = S|R1],[T1 = S|R2],Stop,F) :-   % ris(X in D,...) = int(A,B) (open interval --> irreducible) 
        %write('9-'),
        nonvar(S), open_intv(S),!,     
        %write(rule('ris=int(A,B)')),nl,
        sat_step(R1,R2,Stop,F).

sat_eq_ris([T1 = S |R1],R2,c,F):-               % ris(V,{...},F,P)={...} or ris(V,{...},F,P)=S (var S, nonvar-ris D)
        %write('10-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)), 
%%%       set_int_var(S),
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,
        %write(rule('ris(d)={...} OR ris(d)=var')),nl,
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        first_rest(Dom,CtrlExprNew,D,CNS), 
       (nonvar(CNS),!,
        append(CNS,R1,R3), 
        chvar(LV,[],FVars,[Fl,P,PP,CtrlExpr],[],FVarsNew,[FlNew,PNew,PPNew,_]),
        find_corr_list(CtrlExpr,CtrlExprNew,FVars,FVarsNew),      
        mk_atomic_constraint(PPNew,PPNewD),!,
        (
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        sat_step([FlNewD,PPNewD,ris(CtrlExpr in D,V,Fl,P,PP) with Z = S |R3],R2,_,F)                         
        ;
        negate(FlNew,NegFl),
        mk_atomic_constraint(NegFl,NegFlD),
        sat_step([NegFlD,PPNewD,ris(CtrlExpr in D,V,Fl,P,PP) = S |R3],R2,_,F)   
        )
       ;
        sat_step([ris(CtrlExpr in D,V,Fl,P,PP) = S |R1],R2,_,F) 
       ).     
                 
sat_eq_ris([T1 = S|R1],R2,c,F):-                % ris(V,D,F,P) = {.../D}   (var-ris D)   % special case
        %write('11-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)),      
        nonvar(S), set_int(S),                                        
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var_ris(Dom),     
        first_rest(S,X,A,CNS), append(CNS,R1,R3),  
        tail(S,TS), samevar(Dom,TS),!, 
        %write(rule('ris(X)={_/X}')),nl,
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        chvar(LV,[],Vars,[Fl,P,PP,CtrlExpr],[],VarsNew,[FlNew,PNew,PPNew,_]),
        find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),   
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
        Z = X,
        replace_tail(A,D,NewA),  
        sat_step([FlNewD,PPNewD,Dom=D with CtrlExprNew,CtrlExprNew nin D,ris(CtrlExpr in D,V,Fl,P,PP)=NewA |R3],R2,_,F).  
sat_eq_ris([T1 = S|R1],R2,c,F):-                % ris(V,D,F,P) = {...}   (var-ris D)
        %write('12-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)),      
        nonvar(S), set_int(S), 
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), var_ris(Dom),!, 
        %write(rule('ris(var)={...}')),nl,
        first_rest(S,X,A,CNS), 
        append(CNS,R1,R3),  
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        chvar(LV,[],Vars,[Fl,P,PP,CtrlExpr],[],VarsNew,[FlNew,PNew,PPNew,_]),
        find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),   
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
        Z = X,
        sat_step([FlNewD,PPNewD,Dom=D with CtrlExprNew,CtrlExprNew nin D,ris(CtrlExpr in D,V,Fl,P,PP)=A |R3],R2,_,F).  

sat_eq_ris([T1 = T2 |R1],R2,c,F):-              % ris(V1,{...},F1,P1) = ris(V2,{...},F2,P2)  (nonvar-ris D1, D2)
        %write('13-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom1,V1,Fl1,P1,PP1)),                              
        nonvar(T2), is_ris(T2,ris(CE_Dom2,V2,Fl2,P2,PP2)),                              
        nonvar(CE_Dom1), CE_Dom1 = (CtrlExpr1 in Dom1), nonvar_ris(Dom1),    
        nonvar(CE_Dom2), CE_Dom2 = (CtrlExpr2 in Dom2), nonvar_ris(Dom2), !,   
        write(rule('***************************************ris(d)=ris(e)')),nl,   
        ctrl_expr(CtrlExpr1,V1,LV1,CtrlExprNew1),
        first_rest(Dom1,CtrlExprNew1,D1,CNS1), 
        append(CNS1,R1,R31), 
        ctrl_expr(CtrlExpr2,V2,LV2,CtrlExprNew2),
        first_rest(Dom2,CtrlExprNew2,D2,CNS2), 
        append(CNS2,R31,R3), 
        chvar(LV1,[],Vars1,[Fl1,P1,PP1,CtrlExpr1],[],VarsNew1,[FlNew1,PNew1,PPNew1,_]),
        find_corr_list(CtrlExpr1,CtrlExprNew1,Vars1,VarsNew1),      
        chvar(LV2,[],Vars2,[Fl2,P2,PP2,CtrlExpr2],[],VarsNew2,[FlNew2,PNew2,PPNew2,_]),
        find_corr_list(CtrlExpr2,CtrlExprNew2,Vars2,VarsNew2),      
        solve_expression(Z1,PNew1),
        solve_expression(Z2,PNew2),
        mk_atomic_constraint(PPNew1,PPNew1D),
        mk_atomic_constraint(PPNew2,PPNew2D),
       (
        mk_atomic_constraint(FlNew1,FlNew1D),
        mk_atomic_constraint(FlNew2,FlNew2D),
        sat_step([FlNew1D,FlNew2D,PPNew1D,PPNew2D,
           ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) with Z1 = ris(CtrlExpr2 in D2,V2,Fl2,P2,PP2) with Z2 |R3],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        mk_atomic_constraint(NegFl1,NegFl1D),
        sat_step([NegFl1D,FlNew2,PPNew1D,PPNew2D, 
           ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) = ris(CtrlExpr2 in D2,V2,Fl2,P2,PP2) with Z2 |R3],R2,_,F)
       ;
        negate(FlNew2,NegFl2),
        mk_atomic_constraint(NegFl2,NegFl2D),
        sat_step([FlNew1,NegFl2D,PPNew1D,PPNew2D,
           ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) with Z1 = ris(CtrlExpr2 in D2,V2,Fl2,P2,PP2) |R3],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        negate(FlNew2,NegFl2),
        mk_atomic_constraint(NegFl1,NegFl1D),
        mk_atomic_constraint(NegFl2,NegFl2D),
        sat_step([NegFl1D,NegFl2D,PPNew1D,PPNew2D, 
           ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) = ris(CtrlExpr2 in D2,V2,Fl2,P2,PP2) |R3],R2,_,F)
       ).

sat_eq_ris([T2 = T1 |R1],R2,c,F):-                   % ris(V2,D2,F2,P2)=ris(V1,D1,F1,P1)  (nonvar-ris D1, var-ris D2)
        %write('14-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom1,_,_,_,_)), 
        nonvar(T2), is_ris(T2,ris(_ in Dom2,_,_,_,_)),
        nonvar_ris(Dom1), %%%first_rest(Dom1,_,_,_),                        
        var_ris(Dom2),!,  
        %write(rule('ris(var)=ris(d) --> ris(d)=ris(var)')),nl,
        sat_eq_ris([T1 = T2|R1],R2,_,F).

sat_eq_ris([T1 = T2 |R1],R2,c,F):-                   % ris(V1,D1,F1,P1) = ris(V2,D2,F2,P2)  (nonvar-ris D1, var-ris D2)
        %write('15-'),
        nonvar(T1), is_ris(T1,ris(CE_Dom1,V1,Fl1,P1,PP1)),                              
        nonvar(T2), is_ris(T2,ris(CE_Dom2,V2,Fl2,P2,PP2)),                              
        nonvar(CE_Dom1), CE_Dom1 = (CtrlExpr1 in Dom1), nonvar_ris(Dom1),   
        nonvar(CE_Dom2), CE_Dom2 = (CtrlExpr2 in Dom2), var_ris(Dom2), !,   
        write(rule('***************************************ris(d)=ris(var)')),nl,
        ctrl_expr(CtrlExpr1,V1,LV1,CtrlExprNew1), first_rest(Dom1,CtrlExprNew1,D1,CNS), 
        append(CNS,R1,R3),        
        ctrl_expr(CtrlExpr2,V2,LV2,CtrlExprNew2),
        chvar(LV1,[],Vars1,[Fl1,P1,PP1,CtrlExpr1],[],VarsNew1,[FlNew1,PNew1,PPNew1,_]),
        find_corr_list(CtrlExpr1,CtrlExprNew1,Vars1,VarsNew1),      
        chvar(LV2,[],Vars2,[Fl2,P2,PP2,CtrlExpr2],[],VarsNew2,[FlNew2,PNew2,PPNew2,_]),
        find_corr_list(CtrlExpr2,CtrlExprNew2,Vars2,VarsNew2),      
        solve_expression(Z1,PNew1),
        solve_expression(Z2,PNew2),
        mk_atomic_constraint(PPNew1,PPNew1D),
        mk_atomic_constraint(PPNew2,PPNew2D),
       (
        Dom2 = D2 with CtrlExprNew2,
        mk_atomic_constraint(FlNew1,FlNew1D),
        mk_atomic_constraint(FlNew2,FlNew2D),
        sat_step([FlNew1D,FlNew2D,Z1=Z2,PPNew1D,PPNew2D, 
                  ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) = ris(CtrlExpr2 in D2,V2,Fl2,P2,PP2) |R3],R2,_,F)
       ;
        negate(FlNew1,NegFl1),
        mk_atomic_constraint(NegFl1,NegFl1D),
        sat_step([NegFl1D,PPNew1D,PPNew2D, 
                  ris(CtrlExpr1 in D1,V1,Fl1,P1,PP1) = ris(CtrlExpr2 in Dom2,V2,Fl2,P2,PP2) |R3],R2,_,F)
       ).

sat_eq_ris([T1 = T2|R1],[T1 = T2|R2],Stop,F):-  % ris(V1,D1,F1,P1)=ris(V2,D2,F2,P2)  (var-ris D1, var-ris D2) --> irreducible
        %write('16-'),
        nonvar(T1), is_ris(T1,ris(_ in Dom1,_,_,_,_)),      
        nonvar(T2), is_ris(T2,ris(_ in Dom2,_,_,_,_)),  
        var_ris(Dom1), var_ris(Dom2),!,   
        %write(rule('ris(var)=ris(var)')),nl,
        sat_step(R1,R2,Stop,F).

sat_riseq([X is RIS|R1],[X is RIS|R2],Stop,nf) :-                    % X is ris(...Dom...), Dom var.
        nonvar(RIS), is_ris(RIS,ris(_ in Dom,_,_,_,_)), var_ris(Dom),!,  % delayed until final_sat is called                        
        sat_step(R1,R2,Stop,nf).                   
sat_riseq([X is RIS|R1],R2,c,f) :-              % collecting all values satisfying the RIS
        nonvar(RIS), is_ris(RIS,ris(_ in Dom,_,_,_,_)), var_ris(Dom),!,        
        X = RIS,                   
        sat_step(R1,R2,_,f).
sat_riseq([X is RIS|R1],R2,c,F):-               % collecting all values satisfying the RIS
        final_sat([RIS = R with A, A nin R, set(R)],C),
        append(C,R1,R3),
        X = RR with A,  
        sat_riseq_notemptyset(R,RR,R2,R3,F). 
sat_riseq([X is RIS|R1],R2,c,F):-                      
        final_sat([RIS = {}],C),
        append(C,R1,R3),
        X = {},      
        sat_step(R3,R2,_,F).

sat_riseq_notemptyset(R,RR,R2,R3,F) :-                           
        (var(R),!, RR=R, sat_step(R3,R2,_,F)     
         ;
         is_ris(R,_),!, sat_step([RR is R,set(RR)|R3],R2,_,F)
         ;
         is_empty(R),!, RR=R, sat_step(R3,R2,_,F)
         ;
         tail2(R,T), nonvar(T), \+is_ris(T,_), RR=R, sat_step(R3,R2,_,F)
        ).

is_ris(ris(CE_Dom,Fl),ris(CE_Dom,[],Fl,CtrlExpr,true)) :-             % ris/2 --> ris/5 (no parms)
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in _).   
is_ris(ris(CE_Dom,LVars,Fl),ris(CE_Dom,LVars,Fl,CtrlExpr,true)) :-    % ris/3 --> ris/5
        list_term(LVars), !, nonvar(CE_Dom), CE_Dom = (CtrlExpr in _).             
is_ris(ris(CE_Dom,Fl,P),ris(CE_Dom,[],Fl,P,true)).                    % ris/3 --> ris/5 (no parms)
is_ris(ris(CE_Dom,LVars,Fl,P),ris(CE_Dom,LVars,Fl,P,true)) :-         % ris/4 --> ris/5 
        list_term(LVars), !.
is_ris(ris(CE_Dom,Fl,P,PP),ris(CE_Dom,[],Fl,P,PP)).                   % ris/4 --> ris/5 (no parms)
is_ris(ris(CE_Dom,LVars,Fl,P,PP),ris(CE_Dom,LVars,Fl,P,PP)).

var_ris(Ris) :-    
       var(Ris),!.
var_ris(Ris) :- 
       is_ris(Ris,ris(_ in Dom,_,_,_,_)),!,
       var_ris(Dom).

nonvar_ris(Ris) :-    
       nonvar(Ris), 
       \+is_ris(Ris,_),!.
nonvar_ris(Ris) :- 
       nonvar(Ris),       
       is_ris(Ris,ris(_ in Dom,_,_,_,_)),!,
       nonvar_ris(Dom).

check_ris(ris(CE_Dom,_,_Fl,_P,_PP)) :-
       (nonvar(CE_Dom), CE_Dom = (_ in Dom), ground_elems(Dom),!
        ;
        write('ERROR: is/2: Arguments are not sufficiently instantiated'),nl,
        fail).

ground_elems(R) :- 
       var_ris(R),!.  
ground_elems(R) :- 
       closed_intv(R,_,_),!.
ground_elems({}) :- !.
ground_elems(R with A) :- !,
       ground(A), ground_elems(R).
ground_elems(cp(A,B)) :- !,      
       ground(A), ground(B).
ground_elems(Ris) :-            
       is_ris(Ris,ris(_ in Dom,_,_,_,_)),!,
       ground_elems(Dom).

ctrl_expr(X0,V,[X0|V], _X) :- 
       var(X0),!.
ctrl_expr([X0|Y0],V,[X0,Y0|V],[_X|_Y]) :- 
       var(X0), var(Y0),!.
ctrl_expr([X0,Y0],V,[X0,Y0|V],[_X,_Y]) :- !,
       var(X0), var(Y0).
ctrl_expr(Y0 with X0,V,[X0,Y0|V],_Y with _X) :- 
       var(X0), var(Y0).

first_rest(R with X,X,R,[]) :- !.     % first_rest(S,X,R,C): true if: S is a not-empty set (interval, RIS, CP)         
first_rest(int(X,B),X,R,[]) :-        % R is S without its first component and:
        integer(X), integer(B),       % X is the first component of S and C is the list of computed constraints; 
        X < B,!, X1 is X + 1,         % OR (only for S set) X in not the first component of S and C an unbound var.
        R = int(X1,B).
first_rest(int(X,B),X,{},[]) :-       
        integer(X), integer(B),
        X = B,!.
first_rest(RIS,A,R,C) :- 
        is_ris(RIS,RISe), !, 
        final_sat([RISe = R with A, A nin R, set(R)],C),!.   
first_rest(cp(X,Y),A,R,C) :- !, 
        final_sat([cp(X,Y) = R with A, A nin R, set(R)],C),!.   
first_rest(R with _,_,R,_).                                    

set_int(_ with _) :-!.
set_int(int(_,_)) :- !.
set_int(cp(_,_)).

set_int_var(S) :-     %unused
        var(S),!.     
set_int_var(S) :- 
        nonvar(S), set_int(S).

find_corr_list(X0,X,Vars,VarsNew) :- 
        var(X0),!,
        find_corr(X0,X,Vars,VarsNew).        
find_corr_list([X0|Y0],[X|Y],Vars,VarsNew) :- 
        var(X0), var(Y0),!,
        find_corr(X0,X,Vars,VarsNew),    
        find_corr(Y0,Y,Vars,VarsNew).    
find_corr_list([X0,Y0],[X,Y],Vars,VarsNew) :- !,
        find_corr(X0,X,Vars,VarsNew),    
        find_corr(Y0,Y,Vars,VarsNew).    
find_corr_list(Y0 with X0,Y with X,Vars,VarsNew) :- !,
        find_corr(X0,X,Vars,VarsNew),    
        find_corr(Y0,Y,Vars,VarsNew).    
                  
negate(true,false) :- !.           % exists X,Y (not p(X,Y))
negate(false,true) :- !.         
negate(A=B,A neq B) :- !.
negate(A neq B,A = B) :- !.
negate(A in B,A nin B) :- !.
negate(A nin B,A in B) :- !.
negate(A >= B,A < B) :- !.
negate(A > B,A =< B) :- !.
negate(A =< B,A > B) :- !.
negate(A < B,A >= B) :- !.
negate(un(A,B,C),nun(A,B,C)) :- !.
negate(nun(A,B,C),un(A,B,C)) :- !.
negate(disj(A,B),ndisj(A,B)) :- !.
negate(ndisj(A,B),disj(A,B)) :- !.
negate(subset(A,B),nsubset(A,B)) :- !.
negate(inters(A,B,C),ninters(A,B,C)) :- !.
negate(diff(A,B,C),ndiff(A,B,C)) :- !.
negate(nsubset(A,B),subset(A,B)) :- !.
negate(ninters(A,B,C),inters(A,B,C)) :- !.
negate(ndiff(A,B,C),diff(A,B,C)) :- !.
negate((B1 & B2),(NB1 or NB2)) :- !,   
    negate(B1,NB1), 
    negate(B2,NB2).
negate((B1 or B2),(NB1 & NB2)) :- !,   
    negate(B1,NB1), 
    negate(B2,NB2).
%negate(A,NegA) :-                 % user-defined predicates, with user-defined negative counterparts
%    nonvar(A), functor(A,F,N),    % check if the negation of A is present; otherwise use the next clause
%    functor(AGen,F,N), isetlog((exists_not(AGen) :- _B),_),!,
%    NegA = exists_not(A).
negate(A,NegA) :-                  % user-defined predicates, without user-defined negative counterparts
    (\+ground(A),!, write('************* Unsafe use of negation for predicate '), write(A), nl ; true),
    NegA = (naf A).

solve_expression(X,E) :-
     nonvar(E),   
     test_integer_expr(E),!,
     solve_int(X is E,_).   %<====== QUI
solve_expression(X,E) :-
     X = E.

chvar(V,L1,L1,X,L2,L2,X) :-   %chvar(LocalVars,InitialVars,FinalVars,Term,InitialNewVars,FinalNewVars,NewTerm):
    var(X), notin(X,V), !.    %same as chvar/6 but it replaces only variables which odccur in the list 'LocalVars'
chvar(_,L1,[X|L1],X,L2,[Y|L2],Y):-        %e.g. chvar([X,Y],[],V1,f(X,g(Y,Z),Z,X),[],V2,T2) -->  
    var(X), notin(X,L1), !.               % T2 = f(X',g(Y',Z),Z,X'), V1 = [Y,X], V2 = [Y',X']
chvar(_,L1,L1,X,L2,L2,Y):-
    var(X), find_corr(X,Y,L1,L2),!.
chvar(_,L1,L1,F,L2,L2,F):-
    atomic(F),!.
chvar(V,L1,L1new,F,L2,L2new,F1):-
    F =.. [Fname|Args],
    chvar_all(V,L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].

chvar_all(_,L1,L1,[],L2,L2,[]).
chvar_all(V,L1,L1b,[A|R],L2,L2b,[B|S]):-
    chvar(V,L1,L1a,A,L2,L2a,B),
    chvar_all(V,L1a,L1b,R,L2a,L2b,S).

mk_atomic_constraint(B,X=X) :-   
    nonvar(B), B=true, !.
mk_atomic_constraint(B,delay(BB,true)) :- 
    nonvar(B), B=(_B1 & _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(BB,true)) :- 
    nonvar(B), B=(_B1 or _B2), !,
    conj_append(B,true,BB).
mk_atomic_constraint(B,delay(B & true,true)) :-   % user-defned atomic predicates
    nonvar(B), \+atomic_constr(B), !.
mk_atomic_constraint(B,B).                        % primitive atomic constraints

%%%%%%%%%%% equality involving CP

sat_eq_cp([T1 = T2|R1],R2,c,F) :-              % cp(...) = X --> substitute X
        var(T2), 
        occur_check(T2,T1),!,
        (T1 = cp(A,_), nonvar(A), is_empty(A),!,T2={}
         ;
         T1 = cp(_,B), nonvar(B), is_empty(B),!,T2={}
         ;
         T2 = T1
        ),
        sat_step(R1,R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F) :-              % X = cp(...) --> cp(...) = X
        var(T1),!, 
        %write(rule(inverti_X_cp)),nl,
        sat_eq_cp([T2 = T1|R1],R2,_,F).           
sat_eq_cp([T1 = T2|R1],R2,c,F) :-              % t = cp(...) --> cp(...) = t   (t not cp-term)
        nonvar(T1), \+(T1 = cp(_,_)),!,
        %write(rule(inverti_ncp_cp)),nl,
        sat_eq_cp([T2 = T1|R1],R2,_,F). 
 
sat_eq_cp([T1 = T2|R1],R2,c,F):-               % cp({},_) = T --> T={}
        T1 = cp(A,_), nonvar(A), is_empty(A),!,
        %write(rule(4)),nl, 
        sunify(T2,{},C1),
        append(C1,R1,R3),
        sat_step(R3,R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F):-               % cp(_,{}) = T --> T={}
        T1 = cp(_,B), nonvar(B), is_empty(B),!,
        %write(rule(5)),nl, 
        sunify(T2,{},C1),
        append(C1,R1,R3),
        sat_step(R3,R2,_,F).
sat_eq_cp([T1 = E|R1],R2,c,F):-                % cp(A,B) = {} --> A={} or B ={}
        T1 = cp(A,B),
        nonvar(E), is_empty(E),!,   
        %write(rule(2)),nl,   
        (sat_step([A={}|R1],R2,_,F)
         ;
         sat_step([B={}|R1],R2,_,F)).
%sat_eq_cp([T1 = T2|_R1],_R2,c,_F):-            % cp(A,t) = t or cp(t,B) = t; e.g. cp({X/S},{Y/R}) = {X/S} (special case)
%        nonvar(T1), T1 = cp(A,B),              % not necessary
%        nonvar(T2), T2 = _ with _,
%        (nonvar(A),T2==A,! ; nonvar(B),T2==B),!,
%        fail.
sat_eq_cp([T1 = T2|R1],R2,c,F):-               % e.g. cp({Z/S},{Y/R}) = {X/S} (special case)
        nonvar(T1), T1 = cp(A,B), 
        tail(T2,TT2),
        same_tail(A,B,TT2),!,  
        TT2 = {},                          
        sat_step([T1 = T2|R1],R2,_,F).
sat_eq_cp([T1 = T2|R1],R2,c,F):-               % cp(A,B) = cp(C,D) 
        nonvar(T1), T1 = cp(A,B),
        nonvar(T2), T2 = cp(C,D),!,
        %write(rule(3)),nl, 
        (sunify(A,C,C1), append(C1,R1,R3),
         sunify(B,D,C2), append(C2,R3,R4),
         sat_step([A neq {},B neq {},C neq {},D neq {}|R4],R2,_,F)
        ;
         sat_step([T1 = {},T2 = {}|R1],R2,_,F)
        ).
sat_eq_cp([T1 = T2|R1],R2,c,F):-               % cp(A,B)={x...y|cp(A,B)} (special case)
        nonvar(T1), var_st(T1), T1 = cp(A,B),              
        nonvar(T2), tail(T2,TT2),           
        nonvar(TT2), TT2 = cp(TA,TB), TA==A, TB==B,!,      %GFR var(A), var(B) ????                             
        eq_cp_all(T2,A,B,Const),
        append(Const,R1,R4),
%        sat_step([set(A),set(B)|R4],R2,_,F).
        sat_step(R4,R2,_,F).

sat_eq_cp([T1 = T2|R1],R2,c,F):-               % cp(A,B)={x|C} 
        nonvar(T1), T1 = cp(A,B),
        nonvar(T2), T2 = _ with X,!,
        %write(rule(6)),nl,
        sunify(T2,N with X,C0), append(C0,R1,R1_0),
        sunify(A,A1 with N1,C1), append(C1,R1_0,R3),
        sunify(B,B1 with N2,C2), append(C2,R3,R4),
        sat_step([X nin N,N2 nin B1,N1 nin A1,X=[N1,N2],
                  delay(un(cp({} with N1,B1),cp(A1,B1 with N2),N),false),
                  set(N),set(A1),set(B1)|R4],R2,_,F).

%eq_cp_all(+S,+A,+B,C): S is a set term of the form cp(A,B) with tn with ... with t1,   
%t1,...,tn either variables or pairs [x_i,y_i], and C is a list of constraint of the
%form x_i in A, y_i in B
                                                     %GFR  t1,...,tn possono essere anche variabili????
eq_cp_all(cp(_,_) with [X,Y],A,B,[X in A,Y in B]) :-!.      
eq_cp_all(S with [X,Y],A,B,[X in A,Y in B|RConst]) :-
        eq_cp_all(S,A,B,RConst).

same_tail(A,B,X) :-        
     (tail(A,TA),samevar(X,TA),!
      ;
      tail(B,TB),samevar(X,TB)).   

%%%%%%%%%%%  Set/Multiset Unification Algorithm  %%%%%%%%%%%%               
         
sunify(X,Y,[]) :-                   % X = X  
      X == Y,!.
sunify(T1,T2,[T1 = T2]) :-          % ris = t or cp(...) = t
      nonvar(T1), 
      (is_ris(T1,_),! ; T1 = cp(_,_)),!.
sunify(T1,T2,[T1 = T2]) :-          % t = ris or t = cp(...)
      nonvar(T2), 
      (is_ris(T2,_),! ; T2 = cp(_,_)),!.
sunify(X,Y,C) :-                    % X = t  
      var(X),!,
      %write(rule(sunifyXt1)),nl,
      sunifyXt(X,Y,C).
sunify(X,Y,C) :-                    % t = Y ---> Y = t 
      var(Y),!,
      %write(rule(sunifyXt2)),nl,
      sunify(Y,X,C).  
sunify(int(X1,X2),T2,C) :-                  % intervals 
      is_int(int(X1,X2)), is_int(T2),!,
      intint_unify(int(X1,X2),T2,C). 
sunify(int(X1,X2),T2,C) :-                  % intervals
      is_int(int(X1,X2)), set_term(T2),!,
      int_unify(int(X1,X2),T2,C).
sunify(T1,T2,C) :-                  % intervals
      is_int(T2), set_term(T1),!,
      int_unify(T2,T1,C). 
sunify(X1 with X2,S,C) :-                   % {...} = {...}     
      tail(X1 with X2,TR),
      tail(S,TS),!,
      (samevar(TR,TS),!,
       stunify_samevar(X1 with X2,S,TR,C)
       %,write(rule({t1/'X'}={t2/'X'})),nl
       ;
       %write(rule({t1/'X'}={t2/'Y'})),nl,
       stunify_ss(X1 with X2,S,C) ).
sunify(X1 mwith X2,Y,C) :-                    % bag unification +{...} = +{...}
      bag_tail(X1 mwith X2,BX),   
      bag_tail(Y,BY),!,
      (samevar(BX,BY),!,
       stunify_bag_same(X1 mwith X2,Y,C)
       ;
       stunify_bag(X1 mwith X2,Y,C) ).
sunify(X,Y,C) :-                    % f(...) = f(...) 
      X=..[F|Ax],Y=..[F|Ay],!,
      sunifylist(Ax,Ay,C).

sunifyXt(X,Y,[set(N)]) :-           % X = {...|X} 
      nonvar(Y),tail(Y,TY),samevar(X,TY),!,
      %write(rule('X'={t1/'X'})),nl,
      replace_tail(Y,N,NewY),
      occur_check(X,NewY),          
      X = NewY.   
sunifyXt(X,Y,[]) :-                 % X = t  
      occur_check(X,Y),             % occur_check can be suppressed for efficiency reasons
      check_int_constr(X,Y),
      X = Y.     

%%%%%%%%%%% Set unification %%%%%%%%%%%%%%%%%
%%  distinct tail vars.

stunify_ss(R with X,S with Y,C) :-  % {t,...} = {t,...}
      X==Y,!,
      stunify1_2_3(R,S,X,Y,C).       
stunify_ss(R with X,S with Y,C) :-  % ground case: {...} = {...}
      ground(X), ground(Y),!,
      (sunify(X,Y,C1),!, 
       stunify1_2_3(R,S,X,Y,C2),
       append(C1,C2,C)
      ;
       sunify(R,N with Y,C1), 
       sunify(S,N with X,C2),
       append(C1,C2,C3),
       C = [set(N)|C3] ).       
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y}                        
      sunify(X,Y,C1),
      stunify1_2_3(R,S,X,Y,C2),
      append(C1,C2,C).
stunify_ss(R with X,S with Y,C) :-  % {...|X} = {...|Y} (permutativity)
      sunify(R,N with Y,C1),
      sunify(S,N with X,C2),
      append(C1,C2,C3),
      C = [set(N)|C3].      
%      C = [X neq Y,set(N)|C3].      

stunify1_2_3(R,S,_,_,C) :-          % 1
      sunify(R,S,C).
stunify1_2_3(R,S,_,Y,C) :-          % 2
      sunify(R,S with Y,C).
stunify1_2_3(R,S,X,_,C) :-          % 3 
      sunify(R with X,S,C).

%%  same tail vars.
stunify_samevar(R with X,S with Y,_TR,C):-   % {...|X} = {...|X} 
      select_var(Z,S with Y,Rest),
      sunify(X,Z,C1),
      (sunify(R,Rest,C2)            % 1
       %,write(rule({t1/'X'}={t2/'X'} - 'case 1')),nl
      ;
       sunify(R with X,Rest,C2)     % 2
       %,write(rule({t1/'X'}={t2/'X'} - 'case 2')),nl
      ;
       sunify(R,S with Y,C2)
       %,write(rule({t1/'X'}={t2/'X'} - 'case 3')),nl
      ),      % 3
      append(C1,C2,C).
stunify_samevar(R with X,S with Y,TR,C):-    % 4
      %write(rule({t1/'X'}={t2/'X'} - 'case 4')),nl,
      replace_tail(R,N,NewR),
      replace_tail(S with Y,N,NewSS),
      sunify(TR,N with X,C1),
      sunify(NewR,NewSS,C2),
      append(C1,C2,C3),
%      C = [set(N)|C3].      
      C = [X nin N,set(N)|C3].

sunifylist([],[],[]).
sunifylist([X|AX],[Y|AY],C):-
      sunify(X,Y,C1),
      sunifylist(AX,AY,C2),
      append(C1,C2,C).

%%%%%%%%%%% Interval unification %%%%%%%%%%%%%%%%%

intint_unify(int(L,H),T2,[int(L,H) = T2]) :-            % int(A,B) = int(a,b), a > b (delayed)
        var(L), var(H), is_empty_int(T2), !.    
intint_unify(T2,int(L,H),[int(L,H) = T2]) :-            % int(a,b) = int(A,B), a > b  (delayed)
        var(L), var(H), is_empty_int(T2), !.  
intint_unify(int(L,H),T2,[integer(H), integer(L), H < L]) :-    % int(t1,t2) = int(a,b), a > b
        is_empty_int(T2), !. 
intint_unify(T2,int(L,H),[integer(H), integer(L), H < L]) :-    % int(a,b) = int(t1,t2), a > b
        is_empty_int(T2), !. 

intint_unify(int(L1,H1),int(L2,H2),[]) :-               % int(t1,t2) = int(a,b), a =< b                      
        ground(int(L2,H2)), L2 =< H2,!,
        L1 = L2, H1 = H2.
intint_unify(int(L1,H1),int(L2,H2),[]) :-               % int(a,b) = int(t1,t2), a =< b, \+ground(int(t1,t2))            
        ground(int(L1,H1)), L1 =< H1,!,
        L1 = L2, H1 = H2.
intint_unify(T1,T2,C) :-                                % int(t1,t2) = int(s1,s2)
        T1 = int(L1,H1), T2 = int(L2,H2),
        \+ground(T1), \+ground(T2), !,
        (C = [T1 neq {}, T2 neq {}, L1 = L2, H1 = H2]
         ;
         C = [T1 = {}, T2 = {}] 
        ).

int_unify(int(L,H),S2,[int(L,H) = S2]) :-            % int(A,B) = {}
        var(L), var(H), nonvar(S2), S2 = {}, !.   
int_unify(int(L,H),T2,C) :-                          % int(t1,t2) = {} 
        nonvar(T2), T2 = {}, !,
        C = [integer(H), integer(L), H < L].
int_unify(int(A,B),T2,[]) :-                         % int(a,b) = {...}   (novar(a) and novar(b))
        integer(A), integer(B), A > B,!,  
        T2 = {}.   
int_unify(int(A,B),T2,C) :-                          % int(a,b) = {...}   (novar(a) and novar(b))
        integer(A), integer(B), A =< B,!,  
        final_sat([T2 = R with A, A nin R, set(R)],C1),
        A1 is A + 1,
        int_unify(int(A1,B),R,C2),
        append(C1,C2,C).   
int_unify(T1,T2,C) :-                                % int(A,B) = {...}   (var(A) or var(B))
        T2 = _ with _, T1 = int(A,B),          
        C = [smin(T2,A), smax(T2,B), size(T2,K), K is B-A+1].

is_empty_int(int(A,B)) :-             
        integer(A), integer(B),
        A > B.

%%%%%%%%%%% Multiset unification %%%%%%%%%%%%%%%%%

stunify_bag_same(R mwith X, S mwith Y, C) :-   % +{...|X} = +{...|X} 
        de_tail(R mwith X,ZX),
        de_tail(S mwith Y,ZY),
        sunify(ZX,ZY,C).

stunify_bag(R mwith X, S mwith Y, C) :-        % +{...|X} = +{...|Y} 
        sunify(X,Y,C1),
        sunify(R,S,C2),
        append(C1,C2,C).
stunify_bag(R mwith X, S mwith Y,C) :-
        sunify(R, N mwith Y, C1),
        sunify(S, N mwith X, C2),
        append(C1,C2,C3),
        C = [bag(N)|C3].        

%%%%%%%%%%%%%% Auxiliary predicates for unification

select_var(_,S,_):-
        var(S), !, fail.
select_var(Z, R with Z, R).
select_var(Z, R with Y, A with Y):-
        select_var(Z, R, A).


%%%%%%%%%%%%%%%%%%%%%% inequality (neq/2)

%solved form: X neq T, var(X) & \+simple_integer_expr(T) & \+occurs(X,T) 
%
sat_neq([X neq T|R1],[X neq T|R2],Stop,nf):-         % X neq t (nf-irreducible form)
        var(X),\+simple_integer_expr(T),!,  
        sat_step(R1,R2,Stop,nf).

%%%%%%%%%%%% switch cases
%%%-RIS
sat_neq([T1 neq T2|R1],R2,R,F):-                     % ris neq ris
        nonvar(T1), is_ris(T1,ris(_ in Dom1,_,_,_,_)),
        nonvar(T2), is_ris(T2,ris(_ in Dom2,_,_,_,_)),!, 
        nonopen_intv(Dom1),nonopen_intv(Dom2),
        sat_neq_ris([T1 neq T2|R1],R2,R,F).
sat_neq([T1 neq T2|R1],R2,R,F):-                     % ris neq t (t not ris)
        nonvar(T1), is_ris(T1,ris(_ in Dom,_,_,_,_)),!,
        nonopen_intv(Dom),nonopen_intv(T2),
        sat_neq_ris([T1 neq T2|R1],R2,R,F).
sat_neq([T1 neq T2|R1],R2,R,F):-                     % t neq ris (t not ris)
        nonvar(T2), is_ris(T2,ris(_ in Dom,_,_,_,_)),!,
        nonopen_intv(Dom),nonopen_intv(T1),
        sat_neq_ris([T1 neq T2|R1],R2,R,F).
%%%-CP
sat_neq([T1 neq T2|R1],R2,R,F):-                     % cp neq t
        (nonvar(T1), T1 = cp(_,_),!
         ;
         nonvar(T2),T2 = cp(_,_)
        ),!,
%        sat_neq_cp([T1 neq T2,set(A),set(B)|R1],R2,R,F).
        sat_neq_cp([T1 neq T2|R1],R2,R,F).
%%%-variables
sat_neq([T1 neq T2|R1],R2,R,F):-                     % X neq t (t not ris-term)
        var(T1), nonvar(T2), !,
        sat_neq_vn([T1 neq T2|R1],R2,R,F).                         
sat_neq([T1 neq T2|R1],R2,c,F):-                     % t neq X  
        nonvar(T1), var(T2),!,
        sat_neq([T2 neq T1|R1],R2,_,F).                         
sat_neq([T1 neq T2|R1],R2,R,F):-                     % X neq Y
        var(T1), var(T2),!,
        sat_neq_vv([T1 neq T2|R1],R2,R,F).  
%%%-open intervals 
sat_neq([T1 neq T2|R1],[T1 neq T2|R2],Stop,nf):-     % unbounded intervals int(A,B) neq {}    
        nonvar(T1), T1 = int(A,B), var(A), var(B),   % delayed until final_sat is called (--> Level 3)
        nonvar(T2), is_empty(T2),!,                            
        sat_step(R1,R2,Stop,nf).                   
sat_neq([T1 neq T2|R1],R2,R,F):-                     % unbounded intervals int(A,B) neq t
        is_int(T1), \+ground(T1), !,
        sat_neq_ui([T1 neq T2|R1],R2,R,F).  
sat_neq([T1 neq T2|R1],R2,R,F):-                     % unbounded intervals t neq int(A,B) 
        is_int(T2), \+ground(T2), !,
        sat_neq_ui([T2 neq T1|R1],R2,R,F).  
%%%-closed intervals
sat_neq([T1 neq T2|R1],R2,R,F):-                     % bounded intervals int(a,b) neq t
        nonvar(T1), T1 = int(A,B),
        integer(A), integer(B),!,
        sat_neq_i([T1 neq T2|R1],R2,R,F).   
sat_neq([T1 neq T2|R1],R2,R,F):-                     % bounded intervals t neq int(a,b)
        nonvar(T2), T2 = int(A,B),
        integer(A), integer(B),!,
        sat_neq_i([T2 neq T1|R1],R2,R,F).   
%%%-extensional sets/multisets                      
sat_neq([T1 neq T2|R1],R2,R,F):-                     % t1 neq t2
        nonvar(T1), nonvar(T2),!,
        sat_neq_nn([T1 neq T2|R1],R2,R,F).   
                                               
%%%%%%%%%%%% unbounded intervals 
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq empty 
         nonvar(T2), is_empty(T2),!,
         sat_step([A =< B|R1],R2,_,F).   
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq {S|R}
         nonvar(T2), T2 = _ with _, !,
         (sat_step([Z >= A, Z =< B, Z nin T2|R1],R2,_,F)
         ;  
          sat_step([Z < A, Z in T2|R1],R2,_,F)
         ;
          sat_step([Z > B, Z in T2|R1],R2,_,F)
         ).
sat_neq_ui([int(A,B) neq T2|R1],R2,c,F):-       % int(A,B) neq int(C,D)
         nonvar(T2), T2 = int(C,D), !,
         (sat_step([Z >= A, Z =< B, Z < C|R1],R2,_,F)
         ;  
          sat_step([Z >= A, Z =< B, Z > D|R1],R2,_,F)
         ; 
          sat_step([Z < A, Z >= C, Z =< D|R1],R2,_,F)
         ).
sat_neq_ui([_T1 neq _T2|R1],R2,c,F):-           % int(A,B) neq t  (t non-set term)
         sat_step(R1,R2,_,F).   
                  
%%%%%%%%%%%% variable and general non-variable term 
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq t[X] 
         is_ker(T),
         occurs(X,T),!,
         sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq {... | X} 
         T = _S with _T,
         tail2(T,TS),samevar(X,TS),!,
         split(T,_,L), 
         member(Ti,L) ,
         sat_step([Ti nin X|R1],R2,_,F).
sat_neq_vn([X neq T|R1],R2,c,F):-               % X neq {...,t[X],...}
         T = _S with _T,
         occurs(X,T),!,
         sat_step(R1,R2,_,F).
sat_neq_vn([X neq T|R1],[solved(X neq T,var(X),1,f)|R2],c,F):-  
         simple_integer_expr(T),                % X neq t, t simple integer expr  
         is_int_var(X), !,                    
         solve_int(X neq T,_),
         sat_step([integer(X)|R1],R2,_,F). 
sat_neq_vn([C|R1],[C|R2],Stop,F):-              % X neq t (irreducible form)
         sat_step(R1,R2,Stop,F).

%%%%%%%%%%%% variable terms 
sat_neq_vv([X neq Y|_],_,_,_F):-                % X neq X 
         samevar(X,Y),!,fail.
sat_neq_vv([T1 neq T2|R1],R2,c,F):-             % Y neq X --> X neq Y
         T1 @> T2,!,
         sat_step([T2 neq T1|R1],R2,_,F).                         
sat_neq_vv([X neq Y|R1],[solved(X neq Y,(var(X),var(Y)),1,f)|R2],c,F):-  % X neq Y, X,Y domain variables  
         is_int_var(X),
         is_int_var(Y),!,
         solve_int(X neq Y,_),
         sat_step([integer(X),integer(Y)|R1],R2,_,F). 
sat_neq_vv([C|R1],[C|R2],Stop,F):-              % X neq Y (irreducible form)
         sat_step(R1,R2,Stop,F).

%%%%%%%%%%%% bounded intervals 
sat_neq_i([T1 neq T2|_R1],_R2,_,_F):-           % int(a,b) neq empty
         nonvar(T1), nonvar(T2), 
         is_empty(T1),is_empty(T2),!, fail.
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq int(c,d)
         closed_intv(T1,A1,_B1), closed_intv(T2,A2,_B2), 
         A1 \== A2,!,
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq int(c,d)
         closed_intv(T1,_A1,B1), closed_intv(T2,_A2,B2), 
         B1 \== B2,!, 
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq {S|R} (special)
         set_length(T2,SetL),
         int_length(T1,IntL),
         SetL < IntL, !,
         sat_step(R1,R2,_,F).
sat_neq_i([T1 neq T2|R1],R2,c,F):-              % int(a,b) neq {S|R} 
         nonvar(T2), T2 = _ with _, !,
         (sat_step([Z in T1, Z nin T2, integer(Z) | R1],R2,_,F)     % (i)
          ;
          sat_step([Z nin T1, Z in T2| R1],R2,_,F)                  % (ii)
         ).
sat_neq_i([_T1 neq _T2|R1],R2,c,F):-            % int(a,b) neq t (t non-set term)
         sat_step(R1,R2,_,F).   

%%%%%%%%%%%% general non-variable terms 
sat_neq_nn([F neq G|R1],R2,c,Fin):-             % ground case: t1 neq t2
         ground(F),ground(G),!,
         g_neq(F,G),
         sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin):-             % t1 neq t2 
         functor(F,Fname,Far),functor(G,Gname,Gar),
         (Fname \== Gname ; Far \== Gar),!,
         sat_step(R1,R2,_,Fin).
sat_neq_nn([F neq G|R1],R2,c,Fin):-             % t1 neq t2 
         functor(F,Fname,Far),functor(G,Gname,Gar),
         Fname == Gname, Far == Gar, 
         Fname \== with, Fname \== mwith,
         F =.. [_|Flist], G =.. [_|Glist],!,
         memberall(A,B,Flist,Glist),
         sat_step([A neq B|R1],R2,_,Fin).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between sets  %NEW
         T1 = _S with _A, T2 = _R with _B,      % 
         \+sunify(T1,T2,_),!,
         sat_step(R1,R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between sets
         T1 = _S with _A, T2 = _R with _B,      % {A|S} neq {B|R} (i)
         sat_step([Z in T1, Z nin T2 | R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between sets
         T1 = _S with _A, T2 = _R with _B,!,    % {A|S} neq {B|R} (ii)
         sat_step([Z in T2, Z nin T1 | R1],R2,_,F).

%%%%%%%%%%%% multisets 
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between multisets
         nonvar(T1),nonvar(T2),                 % with the same tail variables
         bag_tail(T1,TT1), bag_tail(T2,TT2), 
         samevar(TT1,TT2),!,
         de_tail(T1,DT1), de_tail(T2,DT2),
         sat_step([DT1 neq DT2|R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-             % inequality between multisets
         T1 = _S mwith A, T2 = R mwith B,       % with distinct tail variables
         sat_step([A neq B, A nin R| R1],R2,_,F).
sat_neq_nn([T1 neq T2|R1],R2,c,F):-      
         T1 = _S mwith A, T2 = R mwith B,!,
         sunify(R mwith B, _N mwith A,C),
         append(C,R1,R3),
         sat_step([Z in T2, Z nin T1 | R3],R2,_,F).

%%%%%%%%%%%% RIS 
sat_neq_ris([T1 neq T2|R1],R2,c,F):-             % ris(...) neq t or t neq  ris(...) (t any term, including var and RIS)
        (sat_step([Z in T1,Z nin T2,set(T1),set(T2)|R1],R2,_,F)                         
        ;
         sat_step([Z nin T1,Z in T2,set(T1),set(T2)|R1],R2,_,F)   
        ).                      
               
%%%%%%%%%%%% CP
sat_neq_cp([T1 neq T2|R1],R2,c,F):-              % cp(...) neq t or t neq cp(...) (t any term, including var and CP)
        %write(rule(cp neq t)),nl,
        (sat_step([N in T1,N nin T2,set(T1),set(T2)|R1],R2,_,F)
         ;
         sat_step([N nin T1,N in T2,set(T1),set(T2)|R1],R2,_,F)
        ).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for arithmetic constraints %%%%%%%%%%%% 
%%%%%%%%%%%%            

sat_eeq([X is E|R1],R2,c,F):-        % integer equality (is/2)            
        ground(E),!,
        simple_arithm_expr(X),       % to catch type errors within {log} 
        arithm_expr(E),           
        X is E,
        sat_step(R1,R2,_,F).
sat_eeq([X is E|R1],R2,c,F):-        % integer equality             
        simple_integer_expr(X),      % to catch type errors within {log} 
        integer_expr(E),           
        solve_int(X is E,IntC1),
        allintvars(X is E,IntC2),
        append(IntC1,IntC2,IntC),
        append(IntC,R1,Newc),
        sat_step(Newc,R2,_,F).

sat_crel([Rel|R1],R2,c,F):-          % integer comparison relations (=<,<,>=,>)                 
        Rel =.. [_OP,E1,E2],
        ground(E1), ground(E2),!,
        arithm_expr(E1),             % to catch type errors within {log} 
        arithm_expr(E2), 
        call(Rel),          
        sat_step(R1,R2,_,F).
sat_crel([Rel|R1],R2,c,F):-                  
        Rel =.. [_OP,E1,E2],
        integer_expr(E1),            % to catch type errors within {log} 
        integer_expr(E2),
        solve_int(Rel,IntC1),
        allintvars(Rel,IntC2),
        append(IntC1,IntC2,IntC),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).

allintvars(E,Evars) :-     % true if E is an arithmetic expression and Evars
    E =.. [_F|Args],       % is a list containing a contraint integer(X) for 
    addint(Args,Evars).    % each variable X in E
    
addint([],[]):-!.
addint([X|R],[integer(X)|Rvars]) :-
    var(X),!,
    addint(R,Rvars).
addint([E|R],Allvars) :-
    allintvars(E,Evars),
    addint(R,Rvars),
    append(Evars,Rvars,Allvars).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/bag/list/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%              

%%%%%%%%%%%%%%%%%%%%%% membership (in/2)

sat_in([T in I|R1],R2,R,F):-                 % variable                      
         var(I),!,
         sat_in_v([T in I|R1],R2,R,F).   
sat_in([T in I|R1],R2,R,F):-                 % bounded interval: t in int(a,b)                         
         closed_intv(I,L,H),!,
         sat_in_i([T in int(L,H)|R1],R2,R,F).                      
sat_in([T in I|R1],R2,R,F):-                 % unbounded interval: t in int(A,B)         
         is_int(I),!,
         sat_in_ui([T in I|R1],R2,R,F). 
sat_in([T in I|R1],R2,R,F):-                 % ris                              
         nonvar(I), is_ris(I,_),!,
         sat_in_ris([T in I|R1],R2,R,F).   
sat_in([T in I|R1],R2,R,F):-                 % cp
         nonvar(I), is_cp(I,_,_),!,
         sat_in_cp([T in I|R1],R2,R,F).                                         
sat_in([T in I|R1],R2,R,F):-                 % extensional set/multiset/list;  t in {...}                  
         nonvar(I),!,
         sat_in_s([T in I|R1],R2,R,F).                         

sat_in_v([T in X|R1],R2,c,F):-               % t in X, set 
         sunify(X,N with T,C1),    
         append(C1,R1,R3),
         sat_step([set(N)|R3],R2,_,F).
sat_in_v([T in X|R1],R2,c,F):-               % t in X, multiset
         sunify(X,N mwith T,_),
         sat_step([bag(N)|R1],R2,_,F).
sat_in_v([T in X|R1],                        
         [solved(T in X,(var(X),occur_check(X,T)),3,f),list(X)|R2],Stop,F):-  
         occur_check(X,T),                   % t in X, list (irreducible form)
         sat_step(R1,R2,Stop,F).  
           
sat_in_i([T in int(A,B)|R1],R2,c,F):-        % bounded interval: t in int(a,b)
         simple_integer_expr(T),!,            
         solve_int(T in int(A,B),IntC),
         append(IntC,R1,R3),
         sat_step([integer(T)|R3],R2,_,F).  
 
sat_in_ui([T in I|R1],R2,c,F):-              % unbounded interval: t in int(A,B)
         simple_integer_expr(T),!,           % either A or B vars  
         I=int(A,B),
         solve_int(T >= A,IntC1),    
         solve_int(T =< B,IntC2),
         append(IntC1,IntC2,IntC),
         append(IntC,R1,R3),
         sat_step([integer(T)|R3],R2,_,F).  

sat_in_s([T in Aggr|R1],R2,c,F):-            % ground set/multiset/list: t in {...} 
         ground(T), ground(Aggr),!,
         g_member(T,Aggr), 
         sat_step(R1,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F):-            % non-ground set/multiset/list (case i): t in {...} 
         aggr_comps(Aggr,A,_R),
         sunify(A,T,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).
sat_in_s([T in Aggr|R1],R2,c,F):-            % non-ground set/multiset/list (case ii): t in {...}
         aggr_comps(Aggr,_A,R),!,
         sat_step([T in R|R1],R2,_,F).

sat_in_ris([X in T1|R1],R2,c,F):-            % ris: X in ris(v,D,...)    (var(D))
         nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)),
         CE_Dom = (CtrlExpr in D), var_ris(D),!,                  
         ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
         chvar(LV,[],Vars,[Fl,P,PP,CtrlExpr],[],VarsNew,[FlNew,PNew,PPNew,_]),
         find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),   
         solve_expression(Z,PNew),
         X = Z,                                                   
         mk_atomic_constraint(PPNew,PPNewD),
        (
         FlNew = (D1 or D2),
         D1 = (apply(this,XX,FF) & A),!,                            
         chvar([],_Vars,ris(CE_Dom,V,Fl,P,PP),[],_VarsNew,RisNew),
         FlNew1 = ((delay([XX,FF] in RisNew,a=b) & A) or D2),
         mk_atomic_constraint(FlNew1,FlNewD)
         ;
         mk_atomic_constraint(FlNew,FlNewD)
         ),
         sat_step([CtrlExprNew in D,set(D),FlNewD,PPNewD |R1],R2,_,F).   

sat_in_ris([X in T1|R1],R2,c,F):-           % ris: X in ris{v,{...},...)   
         nonvar(T1), is_ris(T1,ris(CE_Dom,V,Fl,P,PP)),
         CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,             
         nonopen_intv(Dom),
         ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
         first_rest(Dom,CtrlExprNew,D,CNS), 
        (nonvar(CNS),!,
         append(CNS,R1,R3), 
         chvar(LV,[],Vars,[Fl,P,PP,CtrlExpr],[],VarsNew,[FlNew,PNew,PPNew,_]),
         find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),   
         solve_expression(Z,PNew),
         mk_atomic_constraint(FlNew,FlNewD),
         mk_atomic_constraint(PPNew,PPNewD),
         (sat_step([FlNewD,PPNewD,X in ris(CtrlExpr in D,V,Fl,P,PP) with Z |R3],R2,_,F)
          ;
          negate(FlNew,NegFl),
          mk_atomic_constraint(NegFl,NegFlD),
          sat_step([NegFlD,X in ris(CtrlExpr in D,V,Fl,P,PP) |R3],R2,_,F) 
         )
        ;
         sat_step([X in ris(CtrlExpr in D,V,Fl,P,PP) |R1],R2,_,F)
        ).

sat_in_cp([T in cp(A,B)|R1],R2,c,F):-       % [X,Y] in cp(A,B)
        T = [X,Y],!,
%        sat_step([X in A,Y in B,set(A),set(B)|R1],R2,_,F).                      
        sat_step([X in A,Y in B|R1],R2,_,F).                      


%%%%%%%%%%%%%%%%%%%%%% non-membership (nin/2)

%solved form: T nin A, var(A) & \+occurs(A,T)
%             or nonvar(A) & is_ris(I,ris(_ in Dom,_,_,_,_)) & var_ris(Dom)
%
sat_nin([T nin A|R1],[T nin A|R2],Stop,nf):- % t nin X, nf-irreducible form
        var(A),!, 
        sat_step(R1,R2,Stop,nf).

sat_nin([T nin A|R1],R2,c,F):-              % ground set/multiset/list/interval: 
        ground(T), ground(A), \+(A = cp(_,_)),!, % t nin {A|R} or t nin +{A|R} or t nin [A|R] or t nin int(a,b)
        \+g_member(T,A), 
        sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],R2,c,F):-              % t nin X, t[X] 
        var(A), occurs(A,T),!,                          
        sat_step(R1,R2,_,F).
sat_nin([T nin A|R1],[T nin A|R2],Stop,F):- % t nin X, irreducible form
        var(A),!, 
        sat_step(R1,R2,Stop,F).
sat_nin([_T nin A|R1],R2,c,F):-             % t nin {}  or  t nin []  or  t nin int(a,b) with a>b  
        nonvar(A), empty_aggr(A),!,         
        sat_step(R1,R2,_,F).
sat_nin([T nin I|R1],R2,R,F) :-             % t nin int(A,B)
        is_int(I),!,  
        sat_nin_int([T nin I|R1],R2,R,F).           
sat_nin([T nin I|R1],R2,R,F) :-             % t nin ris(v,D,...) 
        nonvar(I), is_ris(I,_),!, 
        sat_nin_ris([T nin I|R1],R2,R,F).
sat_nin([T nin I|R1],R2,R,F) :-             % t nin cp(...) 
        nonvar(I), is_cp(I,_,_),!,
        sat_nin_cp([T nin I|R1],R2,R,F).
sat_nin([T1 nin A|R1],R2,c,F):-             % t nin {...} or t nin +{...} or t nin [...]   
        nonvar(A), aggr_comps(A,T2,S),!,     
        sat_step([T1 neq T2,T1 nin S|R1],R2,_,F).
sat_nin([_T nin A|R1],R2,c,F):-             % t nin a, a not a set neither an interval 
        nonvar(A),                           
        sat_step(R1,R2,_,F).

sat_nin_int([R nin I|R1],R2,c,F) :-         % bounded/unbounded interval: t nin int(A,B)
%        is_int(I),                         %   (case i)
        simple_integer_expr(R),                          
        I=int(S,_T),
        solve_int(R + 1 =< S,IntC),
        append(IntC,R1,R3),
        sat_step([integer(R),integer(S)|R3], R2, _, F).
sat_nin_int([R nin I|R1],R2,c,F) :-         %   (case ii)
%        is_int(I),
        simple_integer_expr(R), 
        I=int(_S,T),                         
        solve_int(T + 1 =< R,IntC),
        append(IntC,R1,R3),
        sat_step([integer(R),integer(T)|R3], R2, _, F).
sat_nin_int([R nin _I|R1], R2, c, F) :-      %   (case iii)
%        is_int(I),!,       
        sat_step([ninteger(R)|R1], R2, _, F).

sat_nin_ris([X nin I|R1],[X nin I|R2],Stop,F):- % ris: X nin ris{v,D,...) (var-ris D): irreducible
        is_ris(I,ris(_ in Dom,_,_,_,_)), var_ris(Dom),!,   
        sat_step(R1,R2,Stop,F).
sat_nin_ris([_X nin I|R1],R2,c,F):-         % ris: X nin ris{v,{},...) -> true
        is_ris(I,ris(_ in Dom,_,_,_,_)), is_empty(Dom),!, 
        sat_step(R1,R2,_,F).
sat_nin_ris([X nin I|R1],R2,c,F):-          % ris: X nin ris{v,{...},...)   
        nonvar(I), is_ris(I,ris(CE_Dom,V,Fl,P,PP)), 
        nonvar(CE_Dom), CE_Dom = (CtrlExpr in Dom), nonvar_ris(Dom),!,   
        nonopen_intv(Dom),
        ctrl_expr(CtrlExpr,V,LV,CtrlExprNew),
        first_rest(Dom,CtrlExprNew,D,CNS), 
       (nonvar(CNS),!,
        append(CNS,R1,R3), 
        chvar(LV,[],Vars,[Fl,P,PP,CtrlExpr],[],VarsNew,[FlNew,PNew,PPNew,_]),
        find_corr_list(CtrlExpr,CtrlExprNew,Vars,VarsNew),   
        solve_expression(Z,PNew),
        mk_atomic_constraint(FlNew,FlNewD),
        mk_atomic_constraint(PPNew,PPNewD),
        (sat_step([FlNewD,PPNewD,X neq Z,X nin ris(CtrlExpr in D,V,Fl,P,PP) |R3],R2,_,F)
         ;
         negate(FlNew,NegFl),
         mk_atomic_constraint(NegFl,NegFlD),
         sat_step([NegFlD,X nin ris(CtrlExpr in D,V,Fl,P,PP) |R3],R2,_,F) 
        )
       ;
        sat_step([X nin ris(CtrlExpr in D,V,Fl,P,PP) |R1],R2,_,F)
       ).

sat_nin_cp([T nin I|R1],R2,c,F):-           % cp: [X,Y] nin cp(...)
        I = cp(A,B), T=[X,Y],
        (sat_step([X nin A |R1],R2,_,F) %,!   
         ;
         sat_step([Y nin B |R1],R2,_,F)
        ).
sat_nin_cp([T nin _I|R1],R2,c,F):-          % cp: T nin cp(...)  (npair(T))
        sat_step([npair(T)|R1],R2,_,F).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for set/interval constraints %%%%%%%%%%%%
%%%%%%%%%%%%              

%%%%%%%%%%%%%%%%%%%%%% subset (subset/2)  

%solved form: subset(S1,S2), var(S1) & \+subset_elim & \+nonvar_is_empty(S2) 
%             or nonvar(S1) & open_intv(S1)
%
sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,nf):-     % subset(X,s): nf-irreducible form
         var(S1),\+subset_elim,\+nonvar_is_empty(S2),!, 
         sat_step(R1,R2,Stop,nf).

sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % subset(S,S)
        S1 == S2,!,
        sat_step(R1,R2,_,F).                                 
sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % ground case: subset({X|R},S2)            
         ground(S1), ground(S2),
         set_term(S1), set_term(S2),!,
         g_subset(S1,S2),
         sat_step(R1,R2,_,F).

sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,F):- % subset(int(A,B),S2) (open interval --> irreducible) 
        nonvar(S1), open_intv(S1),!,                    % <====== GFR:  to be improved 
        sat_step(R1,R2,Stop,F).
sat_sub([subset(S1,S2)|R1],[subset(S1,S2)|R2],Stop,F):- % subset(S1,int(A,B)) (open interval --> irreducible) 
        nonvar(S2), open_intv(S2),!,    
        sat_step(R1,R2,Stop,F).

sat_sub([subset(S1,I2)|R1],R2,c,F):-                 % subset(X,int(a,b)), var(X)   
         subset_elim, 
         var(S1), closed_intv(I2,_,_),!,      
         (S1 = {},
          sat_step(R1,R2,_,F) 
         ;
          S1 = _R with X,
          sat_step([X in I2,subset(S1,setlog_term(I2))|R1],R2,_,F)
         ). 
sat_sub([subset(S,I)|R1],R2,c,F):-                   % subset({A/X},setlog_term(int(L,H)))    
         nonvar(I), I = setlog_term(I2),!,           % for internal use only
         S = S1 with Z,
         (S1 = {},
          sat_step([Z in I2|R1],R2,_,F) 
         ;
          S1 = _R with X,
          sat_step([Z in I2,X in I2,X > Z,subset(S1,I)|R1],R2,_,F)
         ).
sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % subset(X,S2) - subset_elim                  
         subset_elim, 
         var(S1),!,
         sat_step([un(S1,S2,S2)|R1],R2,_,F). 

sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % subset(X,{})  
         var(S1), nonvar(S2), is_empty(S2),!,    
         S1 = {},   
         sat_step(R1,R2,_,F). 
sat_sub([subset(R,S)|R1],[subset(R,S)|R2],Stop,F):-  % subset(X,s): irreducible form
         var(R),!, 
         sat_step(R1,R2,Stop,F).
sat_sub([subset(S1,_S2)|R1],R2,c,F):-                % subset({},S2)  
         is_empty(S1),!,                
         sat_step(R1,R2,_,F). 
sat_sub([subset(S1,S2)|R1],R2,c,F) :-                % subset(r,s) and either r or s are CP
         (nonvar(S1), is_cp(S1,_,_),!
          ;
          nonvar(S2), is_cp(S2,_,_)
          ),!,
         sat_step([un(S1,S2,S2)|R1],R2,_,F). 
sat_sub([subset(R with X,I2)|R1],R2,c,F):-           % subset({X|R},int(L,H))                 
         closed_intv(I2,_,_),!,
         sat_step([X in I2,subset(R,I2)|R1],R2,_,F).

sat_sub([subset(S1,S2)|R1],R2,c,F):-                 % subset({...|X},{...|X}) (special case)  
         tail(S1,TS1), tail(S2,TS2),
         samevar(TS1,TS2),!,
         sat_step([un(S1,S2,S2)|R1],R2,_,F). 
sat_sub([subset(R with X,S)|R1],R2,c,F):-            % subset({X|R},S) - subset_elim 
         subset_elim,!,
         sunify(S,N with X,C1),                     
         append(C1,R1,R3),                           
         sat_step([X nin N,subset(R,S),set(N)|R3],R2,_,F).
sat_sub([subset(R with X,S)|R1],R2,c,F):-            % subset({X|R},S) var S
         var(S),!,
         sunify(S,N with X,C1),  % <=========================  usare unif. sint. (GFR)                  
         append(C1,R1,R3),                           
         sat_step([subset(R,N with X),set(N)|R3],R2,_,F).
sat_sub([subset(R with X,S with Y)|R1],R2,c,F):- !,  % subset({X|R},S) 
         (sunify(X,Y,C1),                     
          append(C1,R1,R3),                           
          sat_step([subset(R,S with Y)|R3],R2,_,F)
         ;
          sat_step([X neq Y,X in S,subset(R,S with Y)|R1],R2,_,F)
         ).
sat_sub([subset(I,I2)|R1],R2,R,F):-                  % subset(int(l,h),S2) (closed interval) 
         closed_intv(I,_,_),!,
         sat_sub_cint([subset(I,I2)|R1],R2,R,F).

sat_sub_cint([subset(I,_)|R1],R2,c,F):-                   % subset(int(l,h),S2), with l>h   
         I=int(L,H), L>H,!,   
         sat_step(R1,R2,_,F). 
sat_sub_cint([subset(I,I2)|R1],R2,c,F):-                  % subset(int(l1,h1),int(l2,h2))
         I=int(L,H), closed_intv(I2,L2,H2),!,
         L2 =< L, H2 >= H,
         sat_step(R1,R2,_,F). 
sat_sub_cint([subset(I,S2)|R1],R2,c,F):-                  % subset(int(l,l),S2), S2 not interval   
         I=int(L,H), L==H, !,
         sat_step([L in S2|R1],R2,_,F).
sat_sub_cint([subset(I,S2)|R1],R2,c,F):-                  % subset(int(l,h),S2), S2 not interval
         I=int(L,H),
         L1 is L+1,
         sat_step([L in S2,subset(int(L1,H),S2)|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% strict subset (ssubset/2)  

sat_ssub([ssubset(S1,S2)|R1],R2,c,F):-                           
          sat_step([subset(S1,S2),S1 neq S2|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% intersection (inters/3)          

%solved form: inters(S1,S2,S3), one_var(S1,S2) & var(S3) & S1 \== S2 
%             & \+nonvar_is_empty(S1) & \+nonvar_is_empty(S2)
%
sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf):-  % inters(S1,S2,S3) nf-irreducible form
         one_var(S1,S2),var(S3),!, 
         sat_step(R1,R2,Stop,nf).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-       % inters(S,S,S)      
         S1 == S2,!,
         sunify(S1,S3,C),
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).

sat_inters([inters(_S1,S2,S3)|R1],R2,c,F):-      % ground empty-set/empty-interval:
         nonvar(S2), is_empty(S2),!,             % (case i) inters(t1,empty,t2) or
         sunify(S3,{},C),
         append(C,R1,R3),
         sat_step(R3,R2,_,F).
sat_inters([inters(S1,_S2,S3)|R1],R2,c,F):-      % (case ii) inters(empty,t1,t2)
         nonvar(S1), is_empty(S1),!,
         sunify(S3,{},C),
         append(C,R1,R3),
         sat_step(R3,R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,F):-  % inters(S1,S2,S3), S1,S3 var: irreducible form
         var(S1),var(S3),!, 
         sat_step(R1,R2,Stop,F).
sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,F):-  % inters(S1,S2,S3), S2,S3 var: irreducible form
         var(S2),var(S3),!, 
         sat_step(R1,R2,Stop,F).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-      % ground set: inters({...},{...},t)          
         ground(S1), ground(S2), 
         set_term(S1), set_term(S2),!,
         g_inters(S1,S2,S1_2),
         sunify(S1_2,S3,C),
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).

sat_inters([inters(I1,I2,S3)|R1],R2,R,F):-      % inters(int(a,b),int(c,d),t),  
         nonvar(I1), I1=int(_,_),                  
         nonvar(I2), I2=int(_,_),!,
         sat_inters_int([inters(I1,I2,S3)|R1],R2,R,F).    

sat_inters([inters(S1,S2,S3)|R1],R2,c,F) :-     % inters(r,s,t) and either r or s or t are CP
         (nonvar(S1), is_cp(S1,_,_),!
          ;
          nonvar(S2), is_cp(S2,_,_),!
          ;
          nonvar(S3), is_cp(S3,_,_)
         ),!,
         sat_step([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,F). 

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-      % inters(S1,S2,S3), S3 any term, both S1 and S2 not-var - special case
         nonvar(S1),tail(S1,TS1),
         nonvar(S2),tail(S2,TS2),
         tail(S3,TS3),
         samevar3(TS1,TS2,TS3),!,
         sat_step([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,F). 

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-      % inters(S1,S2,S3), S3 var, both S1 and S2 not-var         
         nonvar(S1),                                               
         nonvar(S2), S2 = RS2 with X,
         var(S3),!,
         (S3 = RS3 with X,
          sat_step([set(RS2),X in S1,inters(S1,RS2,RS3),set(RS2),set(RS3)|R1],R2,_,F)
          ;
          sat_step([set(RS2),X nin S1,inters(S1,RS2,S3),set(RS2)|R1],R2,_,F)
         ).

sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-       % inters(S1,S2,S3), S3 not-var, both S1 and S2 not-var       
         nonvar(S1),                             % S2 set term, S1, S3 either set or interval      
         nonvar(S2), S2 = _RS2 with _X,                 
         nonvar(S3),!,      
         sat_step([inters(S1,S2,SRes),SRes=S3|R1],R2,_,F).
sat_inters([inters(S1,S2,S3)|R1],R2,c,F):-       % inters(S1,S2,S3), S3 not-var, both S1 and S2 not-var  
         nonvar(S2),                             % S1 set term, S2,S3 either set or interval                                                      
         nonvar(S1), S1 = _RS1 with _X,!,               
         sat_step([inters(S2,S1,S3)|R1],R2,_,F).

sat_inters([inters(S1,S2,S3)|R1],[inters(S1,S2,S3)|R2],Stop,nf):-  % inters(S1,S2,S3), either S1 or S2 var  
         one_var(S1,S2),!,                                         % delayed until final_sat is called 
         sat_step(R1,R2,Stop,nf). 
                  
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-       % inters(S1,S2,S3), S3 not-var, either S1 or S2 var
         var(S1), var(S2),
         nonvar(S3),S3 = N3 with X,!,   
         S1 = N1 with X,
         S2 = N2 with X,
         sat_step([inters(N1,N2,N3),set(N1),set(N2),set(N3)|R1],R2,_,f). 
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-       % inters(S1,S2,S3), S3 not-var, either S1 or S2 var - special case
         nonvar(S3),tail(S3,TS3),
         one_var(S1,S2), tail(S2,TS2), tail(S1,TS1),
         samevar3(TS1,TS2,TS3),!,
         sat_step([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f). 
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-       % inters(S1,S2,S3), S3 not-var, either S1 or S2 var
         var(S1), 
         nonvar(S3),S3 = N3 with X,!,   
         S1 = N1 with X,
         sunify(S2,N2 with X,C1),
         append(C1,R1,R3),
         sat_step([X nin N2,inters(N1,N2,N3),set(N1),set(N2),set(N3)|R3],R2,_,f). 
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-       % inters(S1,S2,S3), S3 not-var, either S1 or S2 var
         var(S2), 
         nonvar(S3),S3 = N3 with X,!,   
         sunify(S1,N1 with X,C1),
         S2 = N2 with X,
         append(C1,R1,R3),
         sat_step([X nin N1,inters(N1,N2,N3),set(N1),set(N2),set(N3)|R3],R2,_,f). 
sat_inters([inters(S1,S2,S3)|R1],R2,c,f):-       % inters(S1,S2,S3), S3 any term, either S1 or S2 var (other cases)
         one_var(S1,S2),!,
         sat_step([un(D,S3,S1),un(E,S3,S2),disj(D,E),set(D),set(E)|R1],R2,_,f). 

sat_inters_int([inters(I1,I2,S3)|R1],R2,c,F):-          % ground interval: inters(int(a,b),int(c,d),t),  
         closed_intv(I1,L1,H1),                         % a,b,c,d constants
         closed_intv(I2,L2,H2),!,
         g_greater(L1,L2,L3), g_smaller(H1,H2,H3),
         (L3 > H3,!,
          sunify({},S3,C), 
          append(C,R1,R3)
          ; 
          sunify(int(L3,H3),S3,C),
          append(C,R1,R3)
         ), 
         sat_step(R3,R2,_,F).
sat_inters_int([inters(I1,I2,S3)|R1],R2,c,F):-          % non-ground interval - empty-interval case:
         is_int(I1),                                    % inters(int(L1,H1),int(L2,H2),t)
         is_int(I2),                                    % either L1 or H1 or L2 or H2 var 
         (sunify({},I1,C1) 
          ;
          sunify({},I2,C1)
         ),
         sunify({},S3,C2), 
         append(C1,C2,C12), append(C12,R1,R3),
         sat_step(R3,R2,_,F).
sat_inters_int([inters(I1,I2,S3)|R1],R2,c,F):-          % non-ground interval - not empty-interval case:
         is_int(I1),                                    % inters(int(L1,H1),int(L2,H2),t)
         is_int(I2),!,                                  % either L1 or H1 or L2 or H2 var
         I1=int(L1,H1), I2=int(L2,H2),
         int_max(L1,L2,L3,IntC1), int_min(H1,H2,H3,IntC2),
         append(IntC1,IntC2,IntC12),
         (solve_int(L3 > H3,IntC3),
          append(IntC12,IntC3,IntC),
          sunify({},S3,C1), 
          append(IntC,C1,C),
          append(C,R1,R3)
          ; 
          solve_int(L3 =< H3,IntC3),
          append(IntC12,IntC3,IntC),
          sunify(int(L3,H3),S3,C1),
          append(IntC,C1,C),
          append(C,R1,R3)
         ), 
         sat_step([I1 neq {},I2 neq {}|R3],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% union (un/3)

%solved form: un(X,Y,Z), var_st(X) & var_st(Y) & var_st(Z) & X \== Y
%
%sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,nf):-      % un(X,Y,Z) (nf-irreducible form)   
%         var(X),var(Y),var(Z),!,
%         sat_step(R1,R2,Stop,nf).

sat_un([un(S1,S2,T)|R1],R2,c,F):-                    % un(s,s,t) 
         S1==S2,!,                                   % (includes un({},{},t))
         sunify(S1,T,C),                             
         append(C,R1,R3),                            
         sat_step(R3,R2,_,F). 
sat_un([un(X,Y,Z)|R1],R2,c,F):-                      % un(Y,X,Z), var(X),var(Y),var(Z) --> un(X,Y,Z)
         var(X),var(Y),var(Z),
         X @> Y,!,
         sat_step([un(Y,X,Z)|R1],R2,_,F). 
  
sat_un([un(X,Y,Z)|R1],[un(X,Y,Z)|R2],Stop,F):-       % un(X,Y,Z), var_st(X),var_st(Y),var_st(Z) (irreducible form)   
         var_st(X), var_st(Y), var_st(Z),!,
         sat_step(R1,R2,Stop,F).

sat_un([un(T1,T2,S)|R1],R2,c,F):-                    % un({},s,t) 
         nonvar(T1), is_empty(T1),!, 
         sunify(S,T2,C), 
         append(C,R1,R3), 
         sat_step(R3,R2,_,F).         
sat_un([un(T1,T2,S)|R1],R2,c,F):-                    % un(t,{},s) 
         nonvar(T2), is_empty(T2),!,
         sunify(S,T1,C), 
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).         
sat_un([un(T1,T2,T3)|R1],R2,c,F):-                   % un(s,t,{}) 
         nonvar(T3), is_empty(T3),!, 
         unify_empty(T1), unify_empty(T2), 
         sat_step(R1,R2,_,F).

sat_un([un(X,Y,Z)|R1],R2,c,F) :-                     % un(r,s,t) and either r or s or t are CP (not all three)            
         special_cp3(X,Y,Z,TZ,A,B),!,                % and one of the CP components is identical to                      
         %write('NEW special1'),nl,                  % one of the other arguments of 'un'
         (TZ={} ; A={} ; B={}),
         sat_step([un(X,Y,Z)|R1],R2,_,F).
          
sat_un([un(S1,S2,T)|R1],R2,R,F) :-                   % un(r,s,t) and either r or s or t are non-var CP
         (nonvar(S1), is_cp(S1,A,B), nonvar(A),nonvar(B),!
          ;
          nonvar(S2), is_cp(S2,A,B), nonvar(A),nonvar(B),!
          ;
          nonvar(T), is_cp(T,A,B), nonvar(A),nonvar(B)
         ),!,
         %write('un(r,s,t) and either r or s or t are non-var CP'),nl, 
         cp_to_set(S1,SS1), cp_to_set(S2,SS2), cp_to_set(T,TT),   
         sat_un_cp([un(SS1,SS2,TT)|R1],R2,R,F).  
                      
sat_un([un(I1,I2,S)|R1],R2,R,F) :-                   % un(r,s,t) and either r or s or t are not-empty intervals
         (nonvar(I1), I1=int(_,_), nonvar(I2), I2=int(_,_),!
          ;
          nonvar(S), S=int(_,_),!
          ;
          var(S), nonvar(I1), I1=int(_,_),!
          ;
          var(S), nonvar(I2), I2=int(_,_),!
         ),!,
         sat_un_int([un(I1,I2,S)|R1],R2,R,F).    

sat_un([un(S1,S2,S3)|R1],R2,c,F):-                   % un({.../R},s2,{.../R}) or un(s1,{.../R},{.../R}) (special cases) 
         nonvar(S3), S3=_ with T1,
         tail(S1,TS1), tail(S2,TS2), tail(S3,TS3),
         (samevar(TS3,TS1,TS2),! ; samevarcp(TS3,TS1,TS2)),!,
         %write('un({.../R},s2,{.../R}) or un(s1,{.../R},{.../R}) (special cases)'),nl,      
         sunify(N with T1,S3,C1),
         ( sunify(N1 with T1,S1,C2),                               % (i)
           append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin S2,set(N1),set(N),un(N1,S2,N)|C3]
         ;
           sunify(N1 with T1,S2,C2),                               % (ii)
           append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin S1,set(N1),set(N),un(S1,N1,N)|C3]
         ;
           sunify(N1 with T1,S1,C21), sunify(N2 with T1,S2,C22),   % (iii)
           append(C21,C22,C2), append(C1,C2,C3), 
           R = [T1 nin N,T1 nin N1,T1 nin N2,set(N1),set(N2),set(N),un(N1,N2,N)|C3] 
         ),                
         append(R,R1,R3),
         sat_step(R3,R2,_,F).

sat_un([un(S1,S2,S3)|R1],R2,c,F):-                  % un(s1,s2,{...})  
%         nonvar(S3), S3=_ with T1,!,    % TOPLAS paper & release setlog495-20d
%         sunify(N with T1,S3,C1),

%         nonvar(S3), S3=_ with T1,      % release setlog495-21b
%         sunify(S3,N with T1,C1), !,

         nonvar(S3), S3=N with T1, C1=[],!,
         %write('un(s1,s2,{...})'),nl,  

         ( sunify(S1,N1 with T1,C2),                             % (i)
           append(C1,C2,C20),
%           R = [T1 nin N,T1 nin S2, set(N1),set(N), un(S2,N1,N)|C20]     % release setlog495-21b
%           R = [T1 nin N,T1 nin N1, set(N1),set(N), un(N1,S2,N)|C20]     % TOPLAS paper
           R = [T1 nin S2, set(N1),set(N), un(S2,N1,N)|C20]
         ;
           sunify(S2,N1 with T1,C2),                             % (ii)
           append(C1,C2,C20),
%           R = [T1 nin N,T1 nin S1, set(N1),set(N), un(S1,N1,N)|C20]     % release setlog495-21b
%           R = [T1 nin N,T1 nin N1, set(N1),set(N), un(S1,N1,N)|C20]     % TOPLAS paper
           R = [T1 nin S1, set(N1),set(N), un(S1,N1,N)|C20]
         ;
           sunify(S1,N1 with T1,C21), sunify(S2,N2 with T1,C22), % (iii)
           append(C1,C21,C2), append(C2,C22,C20), 
%           R = [T1 nin N, set(N1),set(N2),set(N), un(N1,N2,N)|C20]       % release setlog495-21b
%           R = [T1 nin N,T1 nin N1,T1 nin N2, set(N1),set(N2),set(N), un(N1,N2,N)|C20]  % TOPLAS paper
           R = [set(N1),set(N2),set(N), un(N1,N2,N)|C20]
         ),                
         append(R,R1,R3), 
         sat_step(R3,R2,_,F).

%GFR - con la versione "TOPLAS paper" il goal  un({1/A},{3},{{2/B}}) (o anche  un({1/A},C,{{2/B}}))
% termina con ERROR: Out of global stack!!!
%GFR - precisamente, il goal  un({1/A},{3},{{2/B}}) genera il goal
%  {{2/B}}={T1/N} & {1/A} = {T1/N1} & T1 nin N & T1 nin N1 & un(N1,S2,N).
% che va in ciclo (non riesce ad applicare T1 nin N prima di richiamare la 'un'
% e quindi ha anche la soluzione N1 = {1/_N1},N = {{2/B}} che fa andare in ciclo )
% n.b. {{2/B}}={T1/N} & {1/A} = {T1/N1} & T1 nin N & T1 nin N1 & delay(un(N1,S2,N),false).
% oppure solve({{2/B}}={T1/N} & {1/A} = {T1/N1} & T1 nin N & T1 nin N1) & un(N1,S2,N).
% funzionano bene

sat_un([un(S,T,X)|R1],R2,R,F):-                      % un(s1,s2,X) (X var or variable-cp) 
         var_st(X),!,   
         %write('un(s1,s2,X) (X var or variable-cp)'),nl,      
         sat_un_v([un(S,T,X)|R1],R2,R,F).

%member_all(S,_S1,_S2,[]) :-
%         var(S),!.
%member_all({},_S1,_S2,[]) :- !.
%member_all(R with X,S1,S2,C) :-
%         (C = [X in S1,X nin S2|C1]
%          ;
%          C = [X in S2,X nin S1|C1]
%          ;
%          C = [X in S1,X in S2|C1]
%         ),
%         member_all(R,S1,S2,C1).    

%%% un(s1,s2,X) (X var or variable-cp) 

sat_un_v([un(S,T,X)|R1],R2,R,F):-                    % un({...},s2,X) (bounded sets) 
         var(X),bounded(S),
         occur_check(X,S), occur_check(X,T),!,
         sat_un_s([un(S,T,X)|R1],R2,R,F).
sat_un_v([un(S,T,X)|R1],R2,R,F):-                    % un(s1,{...},X) (bounded sets) 
         var(X),bounded(T),
         occur_check(X,S), occur_check(X,T),!,
         sat_un_t([un(S,T,X)|R1],R2,R,F).
sat_un_v([un(S,T,X)|R1],R2,c,F):-                    % un({...|X},t,X) (special case) 
         nonvar(S), var(X),
         tail(S,TS),samevar(TS,X),!,
         replace_tail(S,N,NewS),
         (samevar(TS,T),!,sat_step([X=NewS,set(N)|R1],R2,_,F)  % un({...|X},X,X) 
          ;
          sat_step([X=NewS,un(T,N,N),set(N)|R1],R2,_,F)).   
sat_un_v([un(S,T,X)|R1],R2,c,F):-                    % un(s,{...|X},X) (special case)    
         nonvar(T), var(X),
         tail(T,TT),samevar(TT,X),!,
         replace_tail(T,N,NewT),
         (samevar(TT,S),!,sat_step([X=NewT,set(N)|R1],R2,_,F)  % un(X,{...|X},X) 
          ;
          sat_step([X=NewT,un(S,N,N),set(N)|R1],R2,_,F)).   
sat_un_v([un(S,T,X)|R1],[un(S,T,X)|R2],Stop,nf):-    %  
         var(X),!,                                   % delayed until final_sat is called
         sat_step(R1,R2,Stop,nf).                    % (--> Level 3)
sat_un_v([un(S,T,X)|R1],R2,c,f):-                    % un({.../R},s,X) 
         var(X),  
         nonvar(S), S = N1 with T1,
         occur_check(X,S), novar_occur_check(X,T),!, 
         X = N with T1,     
         sat_step([un(N1,T,N),set(N),set(N1)|R1],R2,_,f).
sat_un_v([un(T,S,X)|R1],R2,c,f):-                    % un(t,{.../S},X) --> un({.../S},t,X)
         var(X), nonvar(S),
         S=_T2 with _T1,!,
         sat_step([un(S,T,X)|R1],R2,_,f).  

sat_un_v([un(S,T,X)|R1],R2,c,F):-                    % un({.../S},T,cp(A,B)),
         nonvar(X), X = cp(A,B), var_st(X),          %GFR var_st(X) inutile??
         nonvar(S), S = N1 with T1, T1 = [A1,B1],!, 
         %write(sat_un_v_cp1),nl,         
         ( not_cp(T),!,                              % un({.../S},T,cp(A,B))   (not_cp(T))                          
           sat_step([cp(A,B) = N with [A1,B1], %%NO%% [A1,B1] nin N,
                     un(N1,T,N),
                     set(N),set(N1)|R1],R2,_,F)
         ;
           nonvar(T), T = cp(A,B), A == B,!,         % un({.../S},cp(A,A),cp(A,A))  
           sunify(A,N with A1 with B1,CA),append(CA,R1,R3),
           sat_step([A1 nin N, B1 nin N,
                     dom(N1,DRS),ran(N1,RRS),
                     un(DRS,RRS,U),
                     subset(U,A),set(N),rel(N1),set(DRS),set(RRS)|R3],R2,_,F)
         ;
           nonvar(T), T = cp(_,_),!,                 % un({.../S},cp(_,_),cp(A,B))   
           sunify(X,N with T1,CX),append(CX,R1,R3),
           sat_step([un(N1,T,N),set(N),set(N1)|R3],R2,_,F)
         ).
sat_un_v([un(T,S,X)|R1],R2,c,F):-                    % un(T,{.../S},cp(A,B)) --> un({.../S},T,cp(A,B)) 
         var_st(X), nonvar(S),                        
         S=_T2 with _T1,!,
         sat_step([un(S,T,X)|R1],R2,_,F).  

sat_un_s([un(S,T,X)|R1],R2,c,F):-                    % un({...},s2,X) (bounded set case)
         g_union(S,T,X),
         sat_step(R1,R2,_,F).
sat_un_t([un(S,T,X)|R1],R2,c,F):-                    % un(s1,{...},X) (bounded set case)
         g_union(T,S,X),
         sat_step(R1,R2,_,F).

%%% un(r,s,t) and either r or s or t are not-empty intervals

sat_un_int([un(I1,I2,S)|R1],R2,c,F) :-               % un(int(...),int(...),s) 
         %nonvar(I1), nonvar(I2),
         closed_intv(I1,A1,B1), closed_intv(I2,A2,B2), 
         B1 >= A2,!,
         A3 is min(A1,A2),
         B3 is max(B1,B2),
         sunify(int(A3,B3),S,C),
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).  
sat_un_int([un(I1,I2,S)|R1],R2,c,F) :-               % un(int(...),int(...),s) 
         %nonvar(I1), nonvar(I2),
         closed_intv(I1,_A1,B1), closed_intv(I2,A2,_B2), 
         B1 < A2,!,
         int_to_set(I2,S2),
         int_to_set(I1,S1,S2),
         sunify(S1,S,C),
         append(C,R1,R3),  
         sat_step(R3,R2,_,F).  
sat_un_int([un(S1,S2,I)|R1],R2,c,F) :-               % un(s1,s2,int(L,L)) 
         closed_intv(I,T1,T2), T1==T2, !,
         sat_step([un(S1,S2,{} with T1)|R1],R2,_,F).               
sat_un_int([un(S1,S2,I)|R1], R2, c, F) :-            % un(s1,s2,int(...)) 
         closed_intv(I,T1,T2), 
         sunify(N1 with T1,S1,C1), append(C1,R1,C2),
         T3 is T1 + 1,
         sat_step([T1 nin N1,set(N1),un(N1,S2,int(T3,T2)) | C2],R2,_,F).               
sat_un_int([un(S1,S2,I)|R1],R2,c,F) :-               % un(s1,s2,int(...)) 
         closed_intv(I,T1,T2), 
         sunify(N1 with T1,S2,C1), append(C1,R1,C2),
         T3 is T1 + 1,
         sat_step([T1 nin N1,set(N1),un(S1,N1,int(T3,T2)) | C2],R2,_,F).
sat_un_int([un(S1,S2,I)|R1],R2,c,F) :-               % un(s1,s2,int(...)) 
         closed_intv(I,T1,T2), !,
         sunify(N1 with T1,S1,C1),
         sunify(N2 with T1,S2,C2),
         append(C1,R1,C3), append(C2,C3,C4),
         T3 is T1 + 1,
         sat_step([T1 nin N1,T1 nin N2,set(N1),set(N2),un(N1,N2,int(T3,T2)) | C4],R2,_,F).
sat_un_int([un(I,S,X)|R1],R2,c,F) :-                 % un(int(L,L),s,X) 
         var(X), 
         closed_intv(I,T1,T2), T1==T2, !, 
         sat_step([un({} with T1,S,X)|R1],R2,_,F).               
sat_un_int([un(I,S,X)|R1],R2,c,F) :-                 % un(int(...),s,X) (i)
         var(X), 
         closed_intv(I,T1,T2),  
         T3 is T1 + 1,
         sunify(N with T1, X, C1),
         append(C1, R1, C2),
         sat_step([T1 nin N,T1 nin S,set(N),un(int(T3,T2),S,N) | C2], R2, _, F).
sat_un_int([un(I,S,X)|R1],R2,c,F) :-                  % un(int(...),s,X) (ii)
         var(X), 
         closed_intv(I,T1,T2),!,
         T3 is T1 + 1,
         sunify(N with T1, X, C1),
         sunify(N1 with T1, S, C2),
         append(C1, R1, C3),
         append(C2, C3, C4),
         sat_step([T1 nin N,T1 nin N1,set(N),set(N1),un(int(T3,T2),N1,N) | C4], R2, _, F).
sat_un_int([un(S,I,X)|R1],R2,c,F):-                   % un(s,int(...),X)           
         var(X),
         closed_intv(I,_T1,_T2),!,
         sat_step([un(I,S,X)|R1],R2,_,F).                  

%%% un(r,s,t) and either r or s or t are non-var CP

sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(X,Y,Z) (not_cp(X), not_cp(Y), not_cp(Z))
         not_cp(X), not_cp(Y), not_cp(Z),!,
         %write(ncp_ncp_ncp),nl, 
         sat_un([un(Y,X,Z)|R1],R2,_,F).                       
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(X,cp(A,B),Z) (not_cp(X)) --> un(cp(A,B),X,Z)
         nonvar(Y), Y = cp(_,_), not_cp(X),!,
         %write('ncp_cp_?'),nl, 
         sat_un_cp([un(Y,X,Z)|R1],R2,_,F).  
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(cp(A,B),Y,Z) (not_cp(Y), not_cp(Z))
         nonvar(X), X = cp(_,_), un_cp(1,X,Xt,Xu),
         not_cp(Y), not_cp(Z),!,
         %write(cp_ncp_ncp),nl, 
         append(Xu,R1,R3),
         sat_step([un(Xt,Y,Z),set(Xt)|R3],R2,_,F). 
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(cp(A,B),cp(C,D),Z) (not_cp(Z))
         nonvar(X), X = cp(_,_), un_cp(1,X,Xt,Xu),
         nonvar(Y), Y = cp(_,_), un_cp(2,Y,Yt,Yu),
         not_cp(Z),!,
         %write(cp_cp_ncp),nl, 
         append(Xu,Yu,XYu), append(XYu,R1,R3),     
         sat_step([un(Xt,Yt,Z),set(Xt),set(Yt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(X,Y,cp(C,D)) (not_cp(X), not_cp(Y))    
         not_cp(X),
         not_cp(Y),
         nonvar(Z), Z = cp(_,_), un_cp(3,Z,Zt,Zu),!,
         %write(ncp_ncp_cp),nl, 
         append(Zu,R1,R3), 
         sat_step([un(X,Y,Zt),set(Zt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(cp(A,B),Y,cp(C,D)) (not_cp(Y))
         nonvar(X), X = cp(_,_), un_cp(1,X,Xt,Xu),
         not_cp(Y),
         nonvar(Z), Z = cp(_,_), un_cp(3,Z,Zt,Zu),!,
         %write(cp_ncp_cp),nl,  
         append(Xu,Zu,XZu), append(XZu,R1,R3),  
         sat_step([un(Xt,Y,Zt),set(Xt),set(Zt)|R3],R2,_,F).
sat_un_cp([un(X,Y,Z)|R1],R2,c,F):-                    % un(cp(A,B),cp(C,D),cp(E,F)) 
         nonvar(X), X = cp(_,_), un_cp(1,X,Xt,Xu),
         nonvar(Y), Y = cp(_,_), un_cp(2,Y,Yt,Yu),
         nonvar(Z), Z = cp(_,_), un_cp(3,Z,Zt,Zu),!,
         %write(cp_cp_cp),nl,  
         append(Xu,Yu,XYu),append(XYu,Zu,XYZu),    
         append(XYZu,R1,R3),
         sat_step([un(Xt,Yt,Zt),set(Xt),set(Yt),set(Zt)|R3],R2,_,F).

un_cp(N,X,T,U) :-             %GFR - N.B. X e' sempre un cp
       un_cp_t(N,X,T1), 
       un_cp_u(N,X,U1), 
       subs_cp(N,T1,U1,T,U).

un_cp_t(_,X,T) :-
       nonvar(X), X = cp(A,_),
       nonvar(A), is_empty(A),!,
       T = {}.
un_cp_t(_,X,T) :-
       nonvar(X), X = cp(_,B),
       nonvar(B), is_empty(B),!,
       T = {}.
un_cp_t(_,X,T) :-       
       var_st(X),!,
       %write(var_cp_t),nl, 
       T = X.
un_cp_t(N,X,T) :-
       nonvar(X), X = cp(A,B),
       nonvar(A), A = _ with Ea,
       nonvar(B), B = _ with Eb,!,
       T = N with [Ea,Eb].
un_cp_t(_,X,X).

un_cp_u(N,X,U) :-       
       var_st(X),!,
       %write(var_cp_u),nl, 
       U = [N = N].  %GFR da migliorare
un_cp_u(N,X,U) :-
       nonvar(X), X = cp(A,B),
       nonvar(A), A = Sa with _, nonvar(Sa), is_empty(Sa), 
       nonvar(B), B = Sb with _, nonvar(Sb), is_empty(Sb),!,
       U = [N = {}].
un_cp_u(N,X,U) :-
       nonvar(X), X = cp(A,B),
       nonvar(A), A = Sa with _,
       nonvar(B), B = Sb with _, nonvar(Sb), is_empty(Sb),!,
       U = [N = cp(Sa,B), set(Sa)].
un_cp_u(N,X,U) :-
       nonvar(X), X = cp(A,B),
       nonvar(A), A = Sa with _, nonvar(Sa), is_empty(Sa),
       nonvar(B), B = Sb with _,!,
       U = [N = cp(A,Sb), set(Sb)].
un_cp_u(N,X,U) :-
       nonvar(X), X = cp(A,B),
       nonvar(A), A = _ with _,
       nonvar(B), B = _ with _,!,
       get_elem(A,Ea,Sa,C1),     
       get_elem(B,Eb,Sb,C2),
       append(C1,C2,C),
       U = [un(cp({} with Ea,Sb),cp(Sa,Sb with Eb),N),
            [Ea,Eb] nin N, set(Sa), set(Sb)|C].
un_cp_u(_,_,U) :- 
       U = [a=a].   %GFR da migliore

%subs_cp(N,T1,U1,T,U) :- % MAXI 2017 is this case ever executed?     
%       nonvar(T1), T1 = N,!, 
%       T = M,
%       (U1 = [N = A|C],!, U = [M = A|C]
%        ;
%        U1 = [un(A,B,N),P in N|C], U = [un(A,B,M),P in M,set(M)|C]).
%              % MAXI 2017 shouldn't it be "nin" and not "in"?
subs_cp(N,T1,U1,T,U) :-
       nonvar(T1), T1 = N with E,!, 
       T = M with E,
       (U1 = [N = A|C],!, U = [M = A|C]
        ;
        U1 = [un(A,B,N), P nin N|C], 
        U = [delay(un(A,B,M),false),P nin M,set(M)|C] ).
subs_cp(_,T,U,T,U).

% get_elem(+S,?E,?R,-C): true if 
% S is a (non-variable) set term, E is an element of S,
% R is the remaining set part of S (not containing E), 
% C is a (possibly empty) output constraint
%
get_elem(S,E,R,C) :-                       
       nonvar(S), S = _ with E,          
       final_sat([S = R with E, E nin R, set(R)],C).

%%% auxiliary predicates for union

identical_two(T1,T2,A,B) :-
        (nonvar(A),T1==A,! ; nonvar(B),T1==B),
        (nonvar(A),T2==A,! ; nonvar(B),T2==B).

novar_occur_check(_X,T) :-
       var(T),!.
novar_occur_check(X,T) :-
       occur_check(X,T).

unify_empty(S) :-
        var(S), !, S = {}.
unify_empty({}) :- !.
unify_empty(S) :-    
        closed_intv(S,L,H),!,
        L > H.
unify_empty(S) :-   
        S = cp(A,B),
        (unify_empty(A) ; unify_empty(B)).    

var_st(X) :-
       var(X),!.
var_st(X) :-
       X = cp(X1,X2),
       (var(X1),! ; var(X2)).

not_cp(T) :-
       var(T),!.
not_cp(T) :-
       \+(T = cp(_,_)).

one_cp(S1,S2,S3) :-
         (nonvar(S1),S1 = cp(_,_),!
          ;
          nonvar(S2),S2 = cp(_,_),!
          ;
          nonvar(S3),S3 = cp(_,_)
         ).

%cp_component(X,CP): true if X is one of the components of CP
cp_component(X,CP) :-
        CP = cp(A,B),
        (A==X,! ; B==X).
%
%cp_component(X,CP1,CP2): true if X is one of the components of either CP1 or CP2
cp_component(X,CP1,CP2) :-
        (cp_component(X,CP1),! ; cp_component(X,CP2)).

%samevarcp(X,Y): true if X and Y are the same variable CP
samevarcp(X,Y) :-
       nonvar(X), X = cp(A,B), (var(A),! ; var(B)), 
       nonvar(Y), Y = cp(C,D), (var(C),! ; var(D)),
       A == C, B == D.
%
%samevarcp(X,Y,Z): true if X and either Y or Z are the same variable CP
samevarcp(X,Y,Z) :-
       (samevarcp(X,Y),!; samevarcp(X,Z)).

tail_cp(X,T) :-
       nonvar(X), X = cp(A,B),!,
       (tail(A,T) ; tail(B,T)).
tail_cp(X,T) :-
       tail(X,T).

cp_to_set(R,R) :-     %cp_to_set(R,S): if R is not a ground CP, S is R; otherwise S is the 
       var(R),!.      %extensional set corresponding to the cp R
cp_to_set(R,S) :- 
       R = cp(A,B),
       ground(A),ground(B),!,
       g_cp(A,B,S). 
cp_to_set(R,R). 

g_cp({},_,{}).
g_cp(A with X,B,CP) :-
     g_cp_elem(X,B,CPX),
     g_cp(A,B,CPA), 
     g_union(CPX,CPA,CP).
g_cp_elem(_,{},{}).
g_cp_elem(X,B with Y,CP with [X,Y]) :-
     g_cp_elem(X,B,CP). 

special_cp3(X,Y,Z,TZ,A,B) :-
         nonvar(Z), Z=cp(A,B),!, 
         tail_cp(Z,TZ),
         (not_cp(X), tail_cp(X,TX), samevar(TX,TZ),! 
          ; 
          not_cp(Y), tail_cp(Y,TY), samevar(TY,TZ)
         ). 
special_cp3(X,Y,Z,TZ,A,B) :-
         not_cp(Z), 
         tail_cp(Z,TZ),
         (nonvar(X), X=cp(A,B), tail_cp(X,TX), samevar(TX,TZ),!  
          ; 
          nonvar(Y), Y=cp(A,B), tail_cp(Y,TY), samevar(TY,TZ)
         ). 
   

%%%%%%%%%%%%%%%%%%%%%% disjointness (disj/2)

%solved form: disj(X,Y), var_st(X) & var_st(Y) & X \== Y
%
%sat_disj([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,nf):-             % disj(X,Y) (nf-irreducible form)
%        var(X), var(Y),!,
%        sat_step(R1,R2,Stop,nf).

sat_disj([disj(X,Y)|R1],R2,c,F):-                            % disj(X,X)
        var(X), var(Y), samevar(X,Y),!,
        X = {},
        sat_step(R1,R2,_,F).                                 
sat_disj([disj(X,Y)|R1],R2,c,F):-                            % disj(Y,X) --> disj(X,Y)
        var(X),var(Y),
        X @> Y,!,
        sat_step([disj(Y,X)|R1],R2,_,F).                         
sat_disj([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F):-             % disj(X,Y) (irreducible form)
        var(X), var(Y),!,
        sat_step(R1,R2,Stop,F).
sat_disj([disj(Set1,_)|R1],R2,c,F):-                         % disj({},t) or disj(int(a,b),t) with a > b 
        nonvar(Set1), is_empty(Set1),!,
        sat_step(R1,R2,_,F).
sat_disj([disj(_,Set2)|R1],R2,c,F):-                         % disj(t,{}) or disj(t,int(a,b)) with a > b  
        nonvar(Set2), is_empty(Set2),!,
        sat_step(R1,R2,_,F).
sat_disj([disj(Set1,Set2)|R1],R2,c,F):-                      % disj({...},{...}) 
        nonvar(Set1), Set1 = S1 with T1,
        nonvar(Set2), Set2 = S2 with T2,!,
        sat_step([T1 neq T2,T1 nin S2,T2 nin S1,set(S1),set(S2),disj(S1,S2)|R1],R2,_,F).
sat_disj([disj(Set,X)|R1],R2,c,F):-                          % disj({...},X)   
        nonvar(Set), Set = T2 with T1,
        var(X),!,
        sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).
sat_disj([disj(X,Set)|R1],R2,c,F):-                          % disj(X,{...})   
        nonvar(Set), Set = T2 with T1,
        var(X),!,
        sat_step([T1 nin X,set(T2),disj(X,T2)|R1],R2,_,F).
sat_disj([disj(I1,I2)|R1],R2,R,F):-                          % disj(s,t) and either s or t is an interval
        (nonvar(I1), I1=int(_,_), !
        ;
         nonvar(I2), I2=int(_,_)
        ),!,
        sat_disj_int([disj(I1,I2)|R1],R2,R,F).
sat_disj([disj(T1,T2)|R1],R2,R,F):-                          % disj(s,t) and either s or t is a CP
        (nonvar(T1), is_cp(T1,_,_),!
        ;
         nonvar(T2), is_cp(T2,_,_)
        ),!,
        sat_disj_cp([disj(T1,T2)|R1],R2,R,F).

sat_disj_int([disj(I1,I2)|R1],R2,c,F):-                      % disj(int(a,b),int(c,d)) 
        closed_intv(I1,S1,S2),        
        closed_intv(I2,T1,T2),!,        
        (solve_int(S2 + 1 =< T1,IntC)
         ;
         solve_int(T2 + 1 =< S1,IntC)
         ;
         solve_int(S2 + 1 =< T1,IntC1), solve_int(T2 + 1 =< S1,IntC2),
         append(IntC1,IntC2,IntC)
        ),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_disj_int([disj(I1,Set)|R1],R2,c,F):-                     % disj(int(A,A),t)  
        closed_intv(I1,S1,S2), S1==S2, !,
        sat_step([S1 nin Set|R1],R2,_,F).
sat_disj_int([disj(I1,Set)|R1],R2,c,F):-                     % disj(int(a,b),t)  
        nonvar(I1), closed_intv(I1,S1,S2),!,
        S3 is S1 + 1,
        sat_step([S1 nin Set, disj(int(S3,S2),Set)|R1],R2,_,F).
sat_disj_int([disj(Set,I1)|R1],R2,c,F):-                     % disj(t,int(a,b))  
        nonvar(I1), closed_intv(I1,_S1,_S2),
        sat_step([disj(I1,Set)|R1],R2,_,F).

sat_disj_cp([disj(X,Y)|R1],R2,c,F):-                         % disj(Y,cp(...)) --> disj(cp(...),Y)
        nonvar(Y), Y = cp(_,_),
        not_cp(X),!,
        sat_disj_cp([disj(Y,X)|R1],R2,_,F).                 
sat_disj_cp([disj(X,Y)|R1],[disj(X,Y)|R2],Stop,F):-          % disj(X,Y) (irreducible form)
        var_st(X), var_st(Y),!,
        sat_step(R1,R2,Stop,F).
sat_disj_cp([disj(CP,Set)|R1],R2,c,F):-                      % disj(cp(A,B),S) and either A or B are var. 
        nonvar(CP), var_st(CP),
        nonvar(Set), Set = S with E,!,      %GFR set-unify?
        sat_step([E nin CP, disj(CP,S), set(S) |R1],R2,_,F).
sat_disj_cp([disj(CP,Set)|R1],R2,c,F):-                      % disj(cp(...),S), S any set term or cp 
        nonvar(CP), CP = cp(A,B),
        A = A1 with Ea,                     %GFR set-unify?
        B = B1 with Eb,
        sat_step([disj(N with [Ea,Eb],Set), 
                  un(cp({} with Ea,B1),cp(A1,B1 with Eb),N), 
                  set(N),set(A1),set(B1) |R1],R2,_,F).

       
%%%%%%%%%%%%%%%%%%%%%% not union (nun/3)

sat_nun([nun(S1,S2,S3)|R1],R2,c,F):-               % nun(s1,s2,s3) 
        sat_step([N in S3,N nin S1,N nin S2|R1],R2,_,F).
sat_nun([nun(S1,_S2,S3)|R1],R2,c,F):-              % 
        sat_step([N in S1,N nin S3|R1],R2,_,F).
sat_nun([nun(_S1,S2,S3)|R1],R2,c,F):-              % 
        sat_step([N in S2,N nin S3|R1],R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% not disjointness (ndisj/2)

sat_ndisj([ndisj(I1,I2)|R1],R2,c,F):-              % ndisj(int(...),int(...)) 
        closed_intv(I1,S1,S2),        
        closed_intv(I2,T1,T2),!,        
        (solve_int(S1 =< T1,IntC1), solve_int(T1 =< S2,IntC2),
         append(IntC1,IntC2,IntC)
         ;
         solve_int(T1 =< S1,IntC1), solve_int(S1 =< T2,IntC2),
         append(IntC1,IntC2,IntC)
        ),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_ndisj([ndisj(X,Y)|R1],R2,c,F):-                % ndisj(X,X)    
        var(X), var(Y), samevar(X,Y),!,
        sat_step([X neq {}|R1],R2,_,F).                                 
sat_ndisj([ndisj(S,T)|R1],R2,c,F):-                % ndisj({...},{...})
        sat_step([N in S, N in T|R1],R2,_,F).

%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for aggregate constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set cardinality (size/2)              

%solved form: size(S,N), var(S) & var(N)
%
sat_size([size(S,N)|R1],
        [solved(size(S,N),(var(S),var(N)),1,f)|R2],c,F):-   
        var(S),var(N),!,                           % size(S,N) (irreducible form)
        solve_int(N >= 0,IntC),  
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_size([size(S,0)|R1],R2,c,F):-                  % size({},t) or size(int(a,b),t), 
        is_empty(S),!,                             % with a>b (S either var or nonvar)           
        sat_step(R1,R2,_,F).                       
sat_size([size(I,T)|R1],R2,c,F):-                  % size(int(a,b),t)
        closed_intv(I,A,B),!,   
        simple_integer_expr(T),     
        solve_int(T is B-A+1,IntC),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_size([size(I,T)|R1],R2,c,F):-                  % size(cp(a,b),t) 
        nonvar(I), I = cp(A,B),!,   
        (sat_step([T=0,A={}|R1],R2,_,F)           
         ;
         sat_step([T=0,B={}|R1],R2,_,F)
         ;
         solve_int(T is N1*N2,IntC),
         append(IntC,R1,R3),
         sat_step([T neq 0,size(A,N1),size(B,N2),integer(N1),integer(N2)|R3],R2,_,F)
        ).
sat_size([size(S,T)|R1],R2,c,F):-                  % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_size(S,T),
        sat_step(R1,R2,_,F).
sat_size([size(S,T)|R1],[size(S,T)|R2],Stop,nf):-  % size(S,k), S var., k nonvar
        var(S),!,                                  % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf). 
                  
sat_size([size(S,T)|R1],R2,c,f):-                  % LEVEL 3: size(S,k), S var., k int. const.
        var(S),!,                                  
        integer(T),         
        solve_int(T >= 1,IntC1),
        S = R with X,
        solve_int(M is T-1,IntC2),
        append(IntC1,IntC2,IntC),
        append(IntC,R1,R3),
        sat_step([X nin R,set(R),integer(M),size(R,M)|R3],R2,_,f). 
sat_size([size(R with X,T)|R1],R2,c,F):-           
        simple_integer_expr(T),                    % LEVEL 3: size({...},t)
        solve_int(T >= 1,IntC1),
        solve_int(M is T-1,IntC2),
        append(IntC1,IntC2,IntC),
        append(IntC,R1,R3),
        (sat_step([X nin R,set(R),integer(M),size(R,M)|R3],R2,_,F)     
         ;
         sat_step([R=N with X,set(N),X nin N,integer(M),size(N,M)|R3],R2,_,F)).

count_var(T,0,0) :-      % count_var/3 not used at present
        is_empty(T),!.                
count_var(R with A,NonVar,Var):-           % var(A)
        var(A),!,     
        count_var(R,NonVar,Var1),
        Var is Var1 + 1.
count_var(R with A,NonVar,Var):-           % nonvar(A), duplicate A
        find_gdup(A,R),!,
        count_var(R,NonVar,Var).
count_var(R with _A,NonVar,Var):-          % nonvar(A)
        count_var(R,NonVar1,Var),
        NonVar is NonVar1 + 1.

find_gdup(X,R with Y) :-
        var(Y),!,
        find_gdup(X,R).
find_gdup(X,_R with Y) :-
        sunify(X,Y,_),!.
find_gdup(X,R with _Y) :-
        find_gdup(X,R).

%%%%%%%%%%%%%%%%%%%%% set sum (sum/2)              

sat_sum([sum(S,N)|R1],
        [solved(sum(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %  
        var(S),var(N),!,                           % sum(S,N) (irreducible form)
        solve_int(N >= 0,IntC),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_sum([sum(S,0)|R1],R2,c,F):-                    % sum({},t) or sum(int(a,b),t), 
        is_empty(S),!,                             % with a>b (S either var or nonvar)
        sat_step(R1,R2,_,F).                       
sat_sum([sum(I,T)|R1],R2,c,F):-                    % sum(int(a,b),t)
        closed_intv(I,A,B),
        A =< B,!,  
        simple_integer_expr(T),     
        solve_int(T is ((B*(B+1))-(A*(A-1)))/2,IntC),
        append(IntC,R1,R3),
        sat_step(R3,R2,_,F).
sat_sum([sum(S,T)|R1],R2,c,F):-                    % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_sum(S,T),                 
        sat_step(R1,R2,_,F).
sat_sum([sum(S,T)|R1],[sum(S,T)|R2],Stop,nf):-     % sum(S,k), k int. const, S var.
        var(S), integer(T),!,                      % delayed until final_sat is called
        sat_step(R1,R2,Stop,nf).                   % (--> Level 3)
sat_sum([sum(S,T)|R1],[solved(sum(S,T),var(S),1,f)|R2],Stop,f):-        
        var(S), integer(T),                        % LEVEL 3: sum(S,k), k int. const, S var.
        nolabel,!,                                 % if nolabel --> irreducible form
        sat_step(R1,R2,Stop,f).
sat_sum([sum(S,T)|R1],R2,c,f):-                    % LEVEL 3: sum(S,k), k int. const, S var.
        var(S), integer(T),!, 
        solve_int(T >= 0,IntC1),
        sum_all(S,T,int(0,T),[],IntC2),
        append(IntC1,IntC2,IntC),
        append(IntC,R1,R3),           
        sat_step(R3,R2,_,f). 
sat_sum([sum(R with X,T)|R1],
        [solved(sum(R with X,T),true,1,nf)|R2],c,nf):-   %  
        integer(T),!,                              % sum({...},k)
        solve_int(T >= 0,IntC1),                    % delayed until final_sat is called
        add_elem_domain(R with X,T,IntC2),        
        append(IntC1,IntC2,IntC),                
        append(IntC,R1,R3),                
        sat_step(R3,R2,_,nf). 
sat_sum([sum(R with X,T)|R1],[sum(R with X,T)|R2],Stop,nf):- !,  
%        var(T),!,                                 % sum({...},N)
        sat_step(R1,R2,Stop,nf).                   % delayed until final_sat is called 
sat_sum([sum(R with X,T)|R1],R2,c,f):-              
        simple_integer_expr(T),                    % LEVEL 3: sum({...},t)  
        simple_integer_expr(X),     
        solve_int(T >= 0,IntC1),            
        solve_int(X >= 0,IntC2),            
        solve_int(T is M+X,IntC3),
        append(IntC1,IntC2,IntC12),
        append(IntC12,IntC3,IntC),
        append(IntC,R1,R3),
        (sat_step([integer(X),X nin R,set(R),sum(R,M)|R3],R2,_,f) 
        ; 
        sat_step([integer(X),R=N with X,X nin N,set(N),sum(N,M)|R3],R2,_,f) ). 

sum_all({},0,_,_,[]).
sum_all(R with X,N,L,G,IntC) :-
        solve_int(X in L,IntC1), 
        in_order_list(X,G,IntC2),
        append(IntC1,IntC2,IntC12),
        solve_int(N is X + M,IntC3),
        append(IntC12,IntC3,IntC123),           
        sum_all(R,M,L,[X|G],IntC4),
        labeling(X),
        append(IntC123,IntC4,IntC).           

in_order_list(_A,[],[]) :- !.
in_order_list(A,[B|_R],IntC) :-  
        solve_int(A > B,IntC).

add_elem_domain(R,_,_):-     
       var(R),!.
add_elem_domain(T,_,_) :-
       is_empty(T),!.
add_elem_domain(R with A,N,IntC):-                
       solve_int(A in int(0,N),IntC1),   
       add_elem_domain(R,N,IntC2),
       append(IntC1,IntC2,IntC).


%%%%%%%% Under development - to be completed and tested

%%%%%%%%%%%%%%%%%%%%%%  min  (min/2)   %%%%%%%%%%%        
% find the minimum of a set S of non-negative integers.    

sat_min([smin(S,N)|R1],
        [solved(smin(S,N),(var(S),var(N)),1,f)|R2],c,F):-   
        var(S),var(N),!,               % smin(S,N) (irreducible form)
        solve_int(N >= 0,IntC),  
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_min([smin(S,_)|_],_,c,_):-         % smin({},t) or smin(int(a,b),t) with a>b 
        nonvar(S),is_empty(S),!,
        fail.                       
sat_min([smin(S,T)|R1],R2,c,F):-       % smin({X},T)                       
        nonvar(S),S=R with X,
        nonvar(R),is_empty(R),!,
        T = X,
        simple_integer_expr(T),
        solve_int(T >= 0,IntC),  
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).  
sat_min([smin(I,T)|R1],R2,c,F):-       % smin(int(a,b),t) t=a
        closed_intv(I,A,_B),!,
        T = A,
        solve_int(T >= 0,IntC),
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_min([smin(S,T)|R1],R2,c,F):-       % ground case 
        ground(S),!,                
        simple_integer_expr(T),     
        g_min(S,T,IntC),
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_min([smin(S,T)|R1],[smin(S,T)|R2],Stop,nf):-  % smin(S,t), S var., t nonvar
        var(S),!,                     % delayed until final_sat is called
        sat_step(R1,R2,Stop,nf).      % (--> Level 3)
sat_min([smin(S,T)|R1],R2,R,f):-      % LEVEL 3: smin(S,k) S var., k nonvar      
        var(S),!,                     % (k integer constant)          
        integer(T),        
        solve_int(T >= 0,IntC),
        append(IntC,R1,R3),                    
        (sat_step([S=N with X,set(N),integer(X),X nin N,X = T,smin(N,M),M > T|R3],R2,R,f)
         ;
         sat_step([S={} with X,integer(X),X = T|R3],R2,R,f)). 
sat_min([smin(R with X,T)|R1],[smin(R with X,T)|R2],Stop,nf):- 
        bounded(R with X),!,          % smin(s,t), s bounded
        simple_integer_expr(X),
        solve_int(T >= 0,IntC1),    
        minim(R with X,T,IntC2), 
        append(IntC1,IntC2,IntC),                    
        append(IntC,R1,R3),      
        sat_step(R3,R2,Stop,nf).  
sat_min([smin(R with X,T)|R1],[smin(R with X,T)|R2],Stop,nf):-!,  % smin({...|R},t)
        sat_step(R1,R2,Stop,nf).                % delayed until final_sat is called
sat_min([smin({} with X,T)|R1],R2,c,f):-        % LEVEL 3: smin({...},t)           
        simple_integer_expr(X),
        solve_int(T >= 0,IntC), 
        append(IntC,R1,R3),                    
        sat_step([integer(X),X = T|R3],R2,_,f). 
sat_min([smin(R with X,T)|R1],R2,c,f):-         % LEVEL 3: smin({...},t)           
        simple_integer_expr(T),
        simple_integer_expr(X),
        solve_int(T >= 0,IntC), 
        append(IntC,R1,R3),                    
        (sat_step([integer(X),set(R),X = T,smin(R,M),M >= T|R3],R2,_,f)
         ; 
         sat_step([integer(X),set(R),X > T,smin(R,T)|R3],R2,_,f)
        ). 

minim({},_,[]). 
minim(int(A,_),A,[]).                 
minim(R with A,N,IntC):- 
        simple_integer_expr(A),               
        solve_int(A >= N,IntC1),  
        minim(R,N,IntC2),
        append(IntC1,IntC2,IntC).

g_min(L,X,IntC) :-
        L = _R with A,
        integer(A),A>=0,
        gg_min(L,A,X,IntC).
  
gg_min({},P,M,IntC):-
        solve_int(M is P,IntC).
gg_min(int(A,_),P,M,IntC) :-
        int_min(A,P,M,IntC).
gg_min(R with A,P,M,IntC) :-
        integer(A), A>=0,
        int_min(A,P,G,IntC1),
        gg_min(R,G,M,IntC2),
        append(IntC1,IntC2,IntC).
   
int_min(X,Y,J,IntC) :-
        solve_int(X > Y,IntC1),
        solve_int(J is Y,IntC2),
        append(IntC1,IntC2,IntC). 
int_min(X,Y,J,IntC) :-
        solve_int(X =< Y,IntC1),
        solve_int(J is X,IntC2),
        append(IntC1,IntC2,IntC). 

%%%%%%%%%%%%%%%%%%%%%% max (max/2)  %%%%%%%%%          

sat_max([smax(S,N)|R1],
        [solved(smax(S,N),(var(S),var(N)),1,f)|R2],c,F):-   %   
        var(S),var(N),!,                % smax(S,N) (irreducible form)
        solve_int(N >= 0,IntC),           
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_max([smax(S,_)|_],_,c,_) :-         % smax({},t) or smax(int(a,b),t) with a>b 
        nonvar(S),is_empty(S),!,
        fail.                       
sat_max([smax(S,T)|R1],R2,c,F):-        % smax({X},t)                       
        nonvar(S),S=R with X,
        nonvar(R),is_empty(R),!,
        T = X,
        simple_integer_expr(T),
        solve_int(T >= 0,IntC),
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).       
sat_max([smax(I,T)|R1],R2,c,F):-        % smax(int(a,b),t) t=b
        closed_intv(I,_A,B),!,
        T = B,
        solve_int(T >= 0,IntC),
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_max([smax(S,T)|R1],R2,c,F):-        % ground case
        ground(S),!,                
        simple_integer_expr(T),     
        g_max(S,T,IntC),
        append(IntC,R1,R3),                    
        sat_step(R3,R2,_,F).
sat_max([smax(S,T)|R1],[smax(S,T)|R2],Stop,nf) :-  % smax(S,t), S var., t nonvar
        var(S),!,                       % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf).        % (--> Level 3)    
sat_max([smax(S,T)|R1],R2,R,f):-        % LEVEL 3: smax(S,k) S var., k nonvar      
        var(S),!,                       % (k integer constant)          
        integer(T),     
        solve_int(T >= 0,IntC),
        append(IntC,R1,R3),                    
        (sat_step([S=N with X,set(N),integer(X),X nin N,X = T,smax(N,M),M < T|R3],R2,R,f)
         ;
         sat_step([S={} with X,integer(X),X = T|R3],R2,R,f)). 
sat_max([smax(R with X,T)|R1],[smax(R with X,T)|R2],Stop,nf):- 
        bounded(R with X),!, 
        simple_integer_expr(X),         % smax(s,t), s bounded
        solve_int(T >= 0,IntC1),  
        mass(R with X,T,IntC2),       
        append(IntC1,IntC2,IntC),                    
        append(IntC,R1,R3),                    
        sat_step(R3,R2,Stop,nf).  
sat_max([smax(R with X,T)|R1],[smax(R with X,T)|R2],Stop,nf):-!,  % smax({...|R},t)
        sat_step(R1,R2,Stop,nf).                % delayed until final_sat is called
sat_max([smax({} with X,T)|R1],R2,_,f) :-       % LEVEL 3: smax({...},t)  
        simple_integer_expr(X),
        solve_int(T >= 0,IntC), 
        append(IntC,R1,R3),                    
        sat_step([integer(X),X = T|R3],R2,_,f). 
sat_max([smax(R with X,T)|R1],R2,_,f) :-        % LEVEL 3: smax({...},t)  
        simple_integer_expr(T),
        simple_integer_expr(X),
        solve_int(T >= 0,IntC), 
        append(IntC,R1,R3),                    
        (sat_step([set(R),integer(X),X = T,smax(R,M),M =< T|R3],R2,_,f)
        ; 
         sat_step([set(R),integer(X),X < T,smax(R,T)|R3],R2,_,f)). 

mass({},_,[]).
mass(int(_,B),B,[]).                 
mass(R with A,N,IntC):-
        simple_integer_expr(A),   
        solve_int(A >= 0,IntC1),
        solve_int(A =< N,IntC2),
        append(IntC1,IntC2,IntC12),
        mass(R,N,IntC3),
        append(IntC12,IntC3,IntC).

g_max(L,X,IntC) :-
        gg_max(L,0,X,IntC).

gg_max({},P,M,IntC):- 
        solve_int(M is P,IntC).
gg_max(int(_,B),P,M,IntC) :-
        int_max(B,P,M,IntC).
gg_max(R with A,P,M,IntC) :-
        integer(A), A>=0,
        int_max(A,P,G,IntC1),
        gg_max(R,G,M,IntC2),
        append(IntC1,IntC2,IntC).
   
int_max(X,Y,X,IntC) :-
        solve_int(X >= Y,IntC). 
int_max(X,Y,Y,IntC) :-
        solve_int(X < Y,IntC).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%% implementation of ground cases %%%%%%%%%%%%%%%%%%%              

g_neq(T1,T2) :- 
         \+g_equal(T1,T2).

% deterministic membership (for intervals/sets/multisets/lists): 
% g_member(T,A) is true if A contains T (T, A non-variable terms)
g_member(X,I):-                
        closed_intv(I,A,B),integer(X),!, 
        X >= A, X =< B.
g_member(X,S):-
        aggr_comps(S,Y,_R),
        g_equal(X,Y),!.
g_member(X,S):-
        aggr_comps(S,_Y,R),
        g_member(X,R),!.
g_member(X,S):-                
        X=[Y1,Y2],S = cp(A,B),!, 
        g_member(Y1,A),g_member(Y2,B).

g_subset(T,_) :-
        is_empty(T).
g_subset(I,S) :-
        closed_intv(I,A,A),!,
        g_member(A,S).
g_subset(I,S) :-
        closed_intv(I,A,B),!,
        g_member(A,S),
        A1 is A + 1,
        g_subset(int(A1,B),S).
g_subset(R with X,S2) :-
        g_member(X,S2),
        g_subset(R,S2).

g_equal(T1,T2) :- 
        is_empty(T1), is_empty(T2),!.
g_equal(T1,T2) :-
        T1 = T2,!.
g_equal(T1,T2) :-
        g_subset(T1,T2),
        g_subset(T2,T1).

g_union(T,S,S) :-
        is_empty(T),!.              
g_union(S1 with X,S2,S3 with X) :-
        g_union(S1,S2,S3).

g_inters(T,_S,{}) :- 
        is_empty(T),!.
g_inters(_S,T,{}) :- 
        is_empty(T),!.
g_inters(S1 with X,S2,S3 with X) :-
        g_member(X,S2),!,
        g_inters(S1,S2,S3).
g_inters(S1 with _X,S2,S3) :-
        g_inters(S1,S2,S3).

g_size(T,0) :-
        is_empty(T),!.            
g_size(int(A,B),N) :- !, 
        N is B-A+1.            
g_size(R with A,N):-
        g_member(A,R),!,
        g_size(R,N).
g_size(R with _A,N):-
        solve_int(N is M+1,_),    %<====== QUI
        g_size(R,M).
 
g_sum(T,0) :-
        is_empty(T),!. 
g_sum(R with A,N):-
        integer(A), A >= 0,         
        g_member(A,R),!,
        g_sum(R,N).
g_sum(R with A,N):-          
        integer(A), A >= 0,            
        solve_int(N is M+A,_),     %<====== QUI 
        g_sum(R,M).

g_greater(X,Y,X) :- X >= Y,!.
g_greater(_X,Y,Y).

g_smaller(X,Y,X) :- X =< Y,!.
g_smaller(_X,Y,Y).


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for type constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% set (set/1)

sat_set([set(X)|R1],[set(X)|R2],Stop,F):-        % set(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_set([set(X)|R1],R2,c,F):-                    % set({}) 
        X == {}, !,
        sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F):-                    % set({...}) 
        X = _S with _A, !,
        sat_step(R1,R2,_,F).
sat_set([set(X)|R1],R2,c,F):-                    % set(int(...))    
        X = int(A,B),!, 
        sat_step([integer(A),integer(B)|R1],R2,_,F).    
sat_set([set(X)|R1],R2,c,F) :-                   % set(ris(...))
        is_ris(X,_),!,                 
        sat_step(R1,R2,_,F).  
sat_set([set(X)|R1],R2,c,F) :-                   % set(cp(...))
        X = cp(_A,_B),!,                 
%        sat_step([set(A),set(B)|R1],R2,_,F).      
        sat_step(R1,R2,_,F).      

%%%%%%%%%%%%%%%%%%%%%% bag (bag/1)

sat_bag([bag(X)|R1],[bag(X)|R2],Stop,F):-        % bag(X) (irreducible form)
        var(X),!, 
        sat_step(R1,R2,Stop,F).
sat_bag([bag(X)|R1],R2,c,F):- 
        X == {}, !,
        sat_step(R1,R2,_,F).
sat_bag([bag(X)|R1],R2,c,F):-                    
        X = _S mwith _A,
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% list (list/1)

sat_list([list(X)|R1],[list(X)|R2],Stop,F):-     % list(X) (irreducible form)
        var(X),!, 
        sat_step(R1,R2,Stop,F).
sat_list([list(X)|R1],R2,c,F):- 
        X == [], !,
        sat_step(R1,R2,_,F).
sat_list([list(X)|R1],R2,c,F):-                    
        X = [_A|_S],
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% integer (integer/1)

sat_integer([integer(X)|R1],[integer(X)|R2],Stop,F):-  % integer(X) (irreducible form)
        var(X),!,    
        sat_step(R1,R2,Stop,F).
sat_integer([integer(T)|R1],R2,c,F):-                  % integer(t), t is an integer constant            
        integer(T),
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not set (nset/1)

sat_nset([nset(X)|R1],[nset(X)|R2],Stop,F):-         % nset(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_nset([nset(X)|_R1],_R2,c,_F):-                   % nset({}) 
        is_empty(X), !,
        fail.
%sat_nset([nset(X)|R1],R2,c,F):-                     % nset({...}) 
%        X = _S with _A, !,
%        fail.
sat_nset([nset(X)|R1],R2,c,F):-                      % nset(int(...))    
        X = int(A,B),!, 
        (sat_step([ninteger(A)|R1],R2,_,F)
         ;  
         sat_step([ninteger(B)|R1],R2,_,F)
        ). 
sat_nset([nset(X)|R1],R2,c,F) :- 
        X = cp(A,B),!,                 
        (sat_step([nset(A)|R1],R2,_,F)
         ;  
         sat_step([nset(B)|R1],R2,_,F)
        ). 
sat_nset([nset(X)|R1],R2,c,F) :- 
        (X = ris(_,_,_),! ; X = ris(_,_,_,_),! ; X = ris(_,_,_,_,_)),
        \+is_ris(X,_),!,     
        sat_step(R1,R2,_,F).  
sat_nset([nset(X)|R1],R2,c,F):-                      % nset(f(...)) 
        functor(X,Funct,N), 
        (Funct \== with, ! ; N \== 2),
        sat_step(R1,R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not integer (ninteger/1)

sat_ninteger([ninteger(X)|R1],[ninteger(X)|R2],Stop,F) :-  % ninteger(X) (irreducible form)
       var(X), !,    
       sat_step(R1,R2,Stop,F).
sat_ninteger([ninteger(X)|R1],R2,c,F) :-
       \+integer(X),
       sat_step(R1,R2,_,F).

%%%%%%%%%%%%
%%%%%% Rewriting rules for primitive constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% binary relation (rel/1)  

sat_rel([rel(X)|R1],[rel(X)|R2],Stop,F):-          % rel(X) (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_rel([rel(X)|R1],R2,c,F):-                      % rel({}) or or rel(int(a,b)) with a>b
        nonvar(X),is_empty(X),!,
        sat_step(R1,R2,_,F).
sat_rel([rel(X)|R1],R2,c,F):-                      % rel({[t1,t2],...,[t1,t2],...})   
        X = S with [_A1,_A2],!, 
        sat_step([rel(S)|R1],R2,_,F).  
sat_rel([rel(X)|R1],R2,c,F) :-                     % rel(ris(...))
        is_ris(X,ris(_,_,_,[_A1,_A2],_)),!,               
        sat_step(R1,R2,_,F).    
sat_rel([rel(X)|R1],R2,c,F) :-                     % rel(cp(...))
        X = cp(_A,_B),!,               
%        sat_step([set(A),set(B)|R1],R2,_,F).      
        sat_step(R1,R2,_,F).      

%%%%%%%%%%%%%%%%%%%%%% partial function (pfun/1)

sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({}) or or pfun(int(a,b)) with a>b
        nonvar(X),is_empty(X),!,
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],[pfun(X)|R2],Stop,F):-       % pfun(X) (irreducible form)
        var_st(X),!,      
        sat_step(R1,R2,Stop,F).
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun(F), with F closed set and dom(F) ground
        dom_all_known(X),!,
        is_pfun(X),
        sat_step(R1,R2,_,F).
sat_pfun([pfun(X)|R1],R2,c,F) :- 
        is_ris(X,ris(_,_,_,[_A1,_A2],_)),!,                 
        sat_step(R1,R2,_,F).    
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({[...],[...],...})
        X = S with [A1,_A2],
        not_occur(A1,S,C),
        append(C,R1,R3),
        sat_step([pfun(S)|R3],R2,_,F).   
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun({[t1,t2],...,[t1,t2],...})   
        X = S with [A1,A2], 
        sunify(S,R with [A1,A2],C1),                
        not_occur(A1,R,C),
        append(C1,C,C1_C), append(C1_C,R1,R3),  
        sat_step([pfun(R)|R3],R2,_,F).  
%       sat_step([[A1,A2] nin R,pfun(R)|R3],R2,_,F).  
sat_pfun([pfun(X)|R1],R2,c,F):-                    % pfun(cp({...},{...}))  
        nonvar(X), X = cp(_A,B),!,
        sunify(B,{} with _,C),
        append(C,R1,R3),
%        sat_step([set(A)|R3],R2,_,F). 
        sat_step(R3,R2,_,F). 

not_occur(A,S,[dompf(S,D),A nin D,set(D)]) :-     % not_occur(A,R,C): true if A does not occur in the domain of R   
        var(S),!.
not_occur(A,S,[A nin S1]) :-       
        nonvar(S), S = cp(S1,_S2),!.    
not_occur(_A,{},[]) :- !.
not_occur(A,R with [A1,_A2],[A neq A1|CR]) :-
        not_occur(A,R,CR).

is_pfun({}) :- !.
is_pfun(PFun with P) :- 
    is_pfun_cont(PFun,P), 
    is_pfun(PFun).

is_pfun_cont({},_P1) :- !.
is_pfun_cont(F1 with P2,P1) :- 
    nofork(P1,P2), 
    is_pfun_cont(F1,P1).

nofork([X1,_Y1],[X2,_Y2]) :- 
    X1 \== X2,!.
nofork([X1,Y1],[X2,Y2]) :- 
    X1 = X2, Y1 = Y2.

dom_all_known(R) :-                           
    nonvar(R), R={}, !.
dom_all_known(R with [X,_]) :- 
    ground(X),
    dom_all_known(R).

%%%%%%%%%%%%%%%%%%%%%% pair (pair/1)

sat_pair([pair(X)|R1],R2,c,F):-                % pair([X,Y]) 
        X=[_,_],!,
        sat_step(R1,R2,_,F).


%%%%%%%%%%%%%%%%%%%%%% domain of a binary relation (dom/2)  

sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-     % dom(S,D) (irreducible form) 
        var(S),var(D),S\==D,!,                           
        sat_step(R1,R2,Stop,F).
sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-     % dom(S,D) (irreducible form)  (D = int(A,B) open interval --> irreducible) 
        nonvar(D), open_intv(D),!,                  
        sat_step(R1,R2,Stop,F).

sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom({},d) or dom(int(a,b),d) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(s,{}) or dom(s,int(a,b)) with a>b
        nonvar(D),is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).   
sat_dom([dom(S,D)|_R1],_R2,c,_F):-                % dom(t,t), nonvar t; e.g. dom({Y/R},{Y/R}) (special case)
        nonvar(S),nonvar(D),S==D,!, 
        fail.
sat_dom([dom(S,D)|R1],R2,R,F):-                   % dom(cp(...),D) or dom(S,cp(...))
        (nonvar(S), is_cp(S,_,_),!
         ;
         nonvar(D), is_cp(D,_,_)
        ),!, 
        sat_dom_cp([dom(S,D)|R1],R2,R,F).    
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(X,X) or dom({.../R},{.../R}) (special case)
        tail(S,TS),tail(D,TD),
        samevar(TS,TD),!, 
        TS = {},                          
        sat_step([dom(S,D)|R1],R2,_,F).    
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom({...},D) or dom({...},{...}) or dom({...},int(...))   
        nonvar(S), S = SR with [A1,_A2], !,     
        sunify(D,DR with A1,C),
        append(C,R1,R3),
        sat_step([dom(SR,DR),rel(SR),set(DR)|R3],R2,_,F).
sat_dom([dom(S,D)|R1],R2,c,F):-                   % dom(S,{t})  or dom(S,int(a,a))
        var(S), 
        nonvar(D), singleton(D,A), !,                              
        sat_step([comp({} with [A,A],R,R),S = R with [A,Z],[A,Z] nin R,rel(R)|R1],R2,_,F).
sat_dom([dom(S,D)|R1],[dom(S,D)|R2],Stop,nf) :-   % dom(S,D), S var.
        var(S),!,                                 % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf).                  % (--> Level 3)    
sat_dom([dom(S,D)|R1],R2,c,f):-                   % dom(S,{t1,...,tn}), n > 1 or dom(S,{t1/R}) or dom(S,int(a,b)) 
        var(S), nonvar(D),  first_rest(D,A,_DR,_) ,!,    
        sunify(D,DR with A,C), 
        append(C,R1,R3),                       
        sat_step([A nin DR,dom(S1,{} with A),dom(S2,DR),
                  delay(un(S1,S2,S),false),set(DR),rel(S1),rel(S2)|R3],R2,_,f).

sat_dom_cp([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-  % dom(S,D) (irreducible form) 
        var_st(S), var_st(D),!,   
        sat_step(R1,R2,Stop,F).
%sat_dom_cp([dom(S,D)|_R1],_R2,c,_F):-             % dom(t,cp(t,B)) or dom(t,cp(A,t)), nonvar t (special case)
%        nonvar(S),                                % not necessary 
%        nonvar(D),D = cp(A,B),
%        (nonvar(A),S==A,! ; nonvar(B),S==B),!,
%        fail.
sat_dom_cp([dom(S,D)|R1],R2,c,F):-                % dom(X,cp(X,B)) or dom({.../R},cp({.../R},B)) 
        nonvar(D),D = cp(A,B),                    % or dom({.../R},cp(A,{.../R})) (special case)
        tail(S,TS),
%        (tail(A,TA),samevar(TS,TA),!
%         ;
%         tail(B,TB),samevar(TS,TB)
%        ),!,
        same_tail(A,B,TS),!,
        TS = {},                          
        sat_step([dom(S,D)|R1],R2,_,F).
sat_dom_cp([dom(S,D)|R1],[dom(S,D)|R2],Stop,F):-  % dom(S,D) (irreducible form) 
        var_st(S), var_st(D),!,   
        sat_step(R1,R2,Stop,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F):-                % dom(cp({},_),d) or dom(cp(_,{}),d)
        nonvar(S), S = cp(A,B), 
        is_empty(A,B),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F). 
sat_dom_cp([dom(S,D)|R1],R2,c,F):-                % dom(s,cp({},_)) or dom(s,cp(_,{}))
        nonvar(D), D = cp(A,B), 
        nonvar(A), nonvar(B), is_empty(A,B),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                   
sat_dom_cp([dom(S,D)|R1],R2,c,F):-                % dom(s,cp(...)) 
        nonvar(D), D = cp(A,B),
        A = A1 with Ea, B = B1 with Eb,!,
        sat_step([dom(S,N with [Ea,Eb]), 
                  un(cp({} with Ea,B1),cp(A1,B1 with Eb),N),
                  set(N),set(A1),set(B1) |R1],R2,_,F).
sat_dom_cp([dom(S,D)|R1],R2,c,F):-                % dom(cp(...),d)
        nonvar(S), S = cp(A,B),
        sunify(A,D,C),
        append(C,R1,R3),
        sat_step([B neq {} | R3],R2,_,F).                    

is_empty(A,B) :-   
        (nonvar(A),is_empty(A),!
         ;
         nonvar(B),is_empty(B)
        ).

singleton(S,A) :-    
        S = E with A, nonvar(E), is_empty(E), !.
singleton(S,A) :-
        S = int(A,A), integer(A).

%%%%%%%%%%%%%%%%%%%%%% inverse of a binary relation (inv/2)

sat_inv([inv(R,S)|R1],[inv(R,S)|R2],Stop,F):-     % inv(X,Y) (irreducible form) 
        var(R),var(S),!,                           
        sat_step(R1,R2,Stop,F).
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv({},S) [rule inv_2]
        nonvar(R),is_empty(R),!,    
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv(R,{}) [rule inv_1]
        nonvar(S),is_empty(S),!,    
        sunify(R,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         

sat_inv([inv(R,S)|R1],R2,c,F) :-                  % inv(cp(...),S) or inv(cp(...),{...}) or inv(cp(...),cp(...))
        nonvar(R), R = cp(A,B),!,
        sat_step([S = cp(B,A) |R1],R2,_,F).
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv(R,cp(...)) or inv({...},cp(...))
        nonvar(S), S = cp(A,B),!,
        sat_step([R = cp(B,A) |R1],R2,_,F).                                    

sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv({.../R},R) or inv(R,{.../R}) or inv({.../R},{.../R})      
        tail(R,TR),                               % [rule inv_3, inv_4, inv_5]
        tail(S,TS),samevar(TR,TS),!,
        sat_inv_same_tail([inv(R,S)|R1],R2,c,F,TS).  
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv({...},S) or inv({...},{...}) [rule inv_7]    
        nonvar(R), R = _ with [X,Y], !,
        sunify(R,RR with [X,Y],C1), append(C1,R1,C1R1),
        sunify(S,SR with [Y,X],C2), append(C1R1,C2,R3),
        sat_step([[X,Y] nin RR,[Y,X] nin SR,inv(RR,SR),rel(RR),rel(SR)|R3],R2,_,F). 
sat_inv([inv(R,S)|R1],R2,c,F):-                   % inv(R,{...}), var R [rule inv_6]
        var(R), 
        nonvar(S), S = _ with [X,Y], !,
        sunify(S,SR with [X,Y],C1), append(C1,R1,R3),
%        R = RR with [Y,X],
        sunify(R,RR with [Y,X],_),
        sat_step([[X,Y] nin SR,inv(RR,SR),rel(RR),rel(SR)|R3],R2,_,F).    
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,S) :-      % inv({.../R},R), var R [rule inv_3]
        var(S),!,
        R = RR with [X1,Y1],
        replace_tail(RR,N,RRnew),
        S = N with [X1,Y1] with [Y1,X1],
        sat_step([inv(RRnew,N)|R1],R2,_,F).
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,R) :-      % inv(R,{.../R}), var R [rule inv_4]
        var(R),!,
        S = SS with [X1,Y1],
        replace_tail(SS,N,SSnew),
        R = N with [X1,Y1] with [Y1,X1],
        sat_step([inv(SSnew,N)|R1],R2,_,F).
sat_inv_same_tail([inv(R,S)|R1],R2,c,F,T) :-      % inv({.../R},{.../R}), var R [rule inv_5]
        S = _ with [_,_],
        R = RR with [X1,Y1],
        replace_tail(S,{},Selems),
        (sunify(N1 with [Y1,X1],Selems,C),
         append(C,R1,R3),
         sat_step([[Y1,X1] nin N1, %%??
                   un(T,N1,N2),inv(RR,N2)|R3],R2,_,F)
        ;
         T = N with [X1,Y1] with [Y1,X1],
         replace_tail(R,{},Relems),
         replace_tail(RR,N,RRnew),
         replace_tail(S,N,SSnew),
         sat_step([[Y1,X1] nin Selems,[X1,Y1] nin Selems,
                   [Y1,X1] nin Relems,inv(RRnew,SSnew)|R1],R2,_,F)
        ;
         T = N with [X1,Y1] with [Y1,X1],
         replace_tail(S,N,SSnew),
         replace_tail(R,{},Relems),  
         sunify(N3 with [Y1,X1],Relems,C),
%         replace_tail(RR,{},RRelems),
%         sunify(N3 with [Y1,X1],RRelems,C),
         append(C,R1,R3),
         sat_step([[Y1,X1] nin Selems,[X1,Y1] nin Selems,
                   [Y1,X1] nin N3, 
                   un(N,N3,N4),inv(N4,SSnew)|R3],R2,_,F)
        ;
         sunify(N5 with [X1,Y1],Selems,C),
         append(C,R1,R3),
         T = N with [Y1,X1],
         replace_tail(RR,N,RRnew),
         sat_step([
                   %% [X1,Y1] nin N5, %% ??
                   [Y1,X1] nin Selems,un(N,N5,N6),inv(RRnew,N6)|R3],R2,_,F)
        ).

            
%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

sat_ran([ran(X,Y)|R1],R2,c,F):-                   % ran(X,X)
        var(X),var(Y),X==Y,!, X = {},                          
        sat_step(R1,R2,_,F).
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F):-     % ran(S,R) (irreducible form) 
        var(S),var(D),!,                           
        sat_step(R1,R2,Stop,F).                                                
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({},r) or ran(int(a,b),r) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran(S,{}) or ran(S,int(a,b)) with a>b
        nonvar(D), is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).  
sat_ran([ran(S,D)|R1],R2,R,F):-                   % ran(cp(...),D) or ran(S,cp(...)) 
        (nonvar(S),S = cp(_,_),!
         ;
         nonvar(D),D = cp(_,_)
        ),!,
        sat_ran_cp([ran(S,D)|R1],R2,R,F).        
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,F):-     % ran(S,R) or ran(S,r) - irreducible when noran_elim 
        var(S), noran_elim,!,                           
        sat_step(R1,R2,Stop,F).
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({[...],...},R) or ran({[...],...},{...}) or ran({[...],...},int(t1,t2))
        nonvar(S), S = SR with [_A1,A2], noran_elim,!,
        sunify(D,DR with A2,C),
        append(C,R1,R3),
        (var(SR),nonvar(DR), DR=_ with _,!,                      
         sat_step([solved(ran(SR,DR),var(SR),[],f),rel(SR),set(DR)|R3],R2,_,F)
         ;
         sat_step([ran(SR,DR),rel(SR),set(DR)|R3],R2,_,F)                 
        ).
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran(S,{t}) 
        var(S), nonvar(D), D = E with A, nonvar(E), is_empty(E), !,                          
        sat_step([comp(R,{} with [A,A],R),S = R with [Z,A],[Z,A] nin R,rel(R)|R1],R2,_,F).  
sat_ran([ran(S,D)|R1],[ran(S,D)|R2],Stop,nf) :-   % ran(S,D), S var.
        var(S),!,                                 % delayed until final_sat is called 
        sat_step(R1,R2,Stop,nf).                  % (--> Level 3)    
sat_ran([ran(S,D)|R1],R2,c,f):-                   % ran(S,{t1,...,tn}), n > 1 or ran(S,{t1/R}),
        var(S), nonvar(D), D = _DR with A,!, 
        sunify(D,DR with A,C), 
        append(C,R1,R3),                       
        sat_step([A nin DR,ran(S1,{} with A),ran(S2,DR),
                  delay(un(S1,S2,S),false),rel(S1),rel(S2),set(DR)|R3],R2,_,f).  
sat_ran([ran(S,D)|R1],R2,c,F):-                   % ran({[...],...},R) or ran({[...],...},{...}) or ran({[...],...},int(t1,t2))
        nonvar(S), S = SR with [_A1,A2], !,      
        sunify(D,DR with A2,C),
        append(C,R1,R3),
        sat_step([ran(SR,DR),rel(SR),set(DR)|R3],R2,_,F).

sat_ran_cp([ran(S,D)|R1],R2,c,F) :-    
        sat_step([inv(S,SInv),dom(SInv,D)|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% composition of binary relations (comp/3)  

sat_comp([comp(R,_S,T)|R1],R2,c,F):-     % comp({},s,t) or comp(int(a,b),s,t) with a>b
        nonvar(R),is_empty(R),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).
sat_comp([comp(_R,S,T)|R1],R2,c,F):-     % comp(r,{},t) or comp(r,int(a,b),t) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).

sat_comp([comp(R,S,T)|R1],[comp(R,S,T)|R2],Stop,F):-  
        (var_st(R),var_or_empty(T),!     % comp(R,s,T) or comp(r,S,T), r and s not empty set,                  
        ;                                % irreducible forms
         var_st(S),var_or_empty(T)                       
        ),!,         
        sat_step(R1,R2,Stop,F).

sat_comp([comp(S1,S2,T)|R1],R2,R,F) :-   % comp(r,s,t) and either r or s or t are not-variable CP 
         (nonvar(S1), is_cp(S1,_,_),!
          ;
          nonvar(S2), is_cp(S2,_,_),!
          ;
          nonvar(T), is_cp(T,_,_)
         ),!,
         cp_to_set(S1,SS1), cp_to_set(S2,SS2), cp_to_set(T,TT),
         sat_comp_cp([comp(SS1,SS2,TT)|R1],R2,R,F).    

sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({[X,Y]/R},{[A,B]/S},{})    
        nonvar(R), R = RR with [X,Y], 
        nonvar(S), S = SS with [A,B], 
        nonvar(T), is_empty(T), !,
        sat_step([A neq Y,
                  comp({} with [X,Y],SS,{}),
                  comp(RR,{} with [A,B],{}),
                  comp(RR,SS,{}) | R1],R2,_,F).
sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({[X,Y]},{[Z,V]},T) - R,S singleton relations     
        nonvar(R), R = RR with [X,Y1], nonvar(RR), is_empty(RR),
        nonvar(S), S = SS with [Y2,Z], nonvar(SS), is_empty(SS), !,
        (sat_step([Y1 = Y2, T = {} with [X,Z]|R1],R2,_,F)    
         ;
         sat_step([Y1 neq Y2, T = {}|R1],R2,_,F)
        ). 
sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({[X,X]},{[X,Z]/S},{[X,Z]/S}) - R singleton relation
        nonvar(R), R = RR with [X,X], nonvar(RR), is_empty(RR),
        nonvar(S), S = SS with [X,Z],
        nonvar(T), T = TT with [X,Z], TT == SS, !,
        sat_step([comp({} with [X,X],SS,SS) |R1],R2,_,F). 
sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({[X,Y]/S},{[Y,Y]},{[X,Y]/S}) - s singleton relation
        nonvar(R), R = RR with [X,Y],
        nonvar(S), S = SS with [Y,Y], nonvar(SS), is_empty(SS),
        nonvar(T), T = TT with [X,Y], TT == RR, !,
        sat_step([comp(RR,{} with [Y,Y],RR) |R1],R2,_,F).         
  
sat_comp([comp(R,S,T)|R1],[comp(R,S,T)|R2],Stop,F):-      % special cases - irreducible when nocomp_elim
        nocomp_elim,
        tail(R,TR),tail(S,TS),tail(T,TT),      
        samevar3(TR,TS,TT),!,   
        sat_step(R1,R2,Stop,F).
                              
sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({[X,Y]/R},{[Y,Z]/S},{[X,Z]/T})
         nonvar(T), T = _TT with [X,Z], !,
         sunify(T,TT with [X,Z],C),
         append(C,R1,R3),
         sat_step([[X,Z] nin TT,
                  un(Rx,Rt,R),un(Sz,St,S),
                  Rx = RR with [X,Y], Sz = SS with [Y,Z],
                  [X,Y] nin RR, [Y,Z] nin SS,
                  comp({} with [X,X],RR,RR),
                  comp(SS,{} with [Z,Z],SS),
                  comp({} with [X,X],Rt,{}),        
                  comp(St,{} with [Z,Z],{}),        
                  comp(Rx,St,N1),
                  comp(Rt,S,N2),                    
                  un(N1,N2,TT) | R3],R2,_,F).
sat_comp([comp(R,S,T)|R1],R2,c,F):-      % comp({...},{...},T), T var.    
         var(T),
         nonvar(R), R = _ with [_,_],
         nonvar(S), S = _ with [_,_],!,
         comp_distribute(R,S,C,{},T),
         append(C,R1,R3),
         sat_step(R3,R2,_,F).

comp_distribute(R,S,C,T0,T) :-
         var(R),!,
         comp_distribute_first(R,S,C,T0,T).
comp_distribute({},_S,[],T,T) :- !.
comp_distribute(R,S,C,T0,T) :-
         R = RR with [X,Y1],
         comp_distribute_first([X,Y1],S,C1,T0,T1),
         comp_distribute(RR,S,C2,T1,T),
         append(C1,C2,C).

comp_distribute_first(P,S,C,T0,T2) :-
         nonvar(P),P = [_,_],var(S),!,
         C = [comp({} with P,S,T1),un(T0,T1,T2)].
comp_distribute_first(_P,{},[],T,T) :- !.
comp_distribute_first(P1,S,C,T0,T) :-
         var(P1),!,
         C = [comp(P1,S,T1),un(T0,T1,T)].
comp_distribute_first(P1,S,C,T0,T) :-
         S = SR with [Y2,Z],
         C = [comp({} with P1,{} with [Y2,Z],T1),un(T0,T1,T2) | CR],
         comp_distribute_first(P1,SR,CR,T2,T).

sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F) :-           % special cases                 
         special_cp3(X,Y,Z,TZ,A,B),!,  
         %write('special_comp'),nl,                               
         (TZ={} ; A={} ; B={}),
         sat_step([comp(X,Y,Z)|R1],R2,_,F).
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F):-            % comp(X,Y,Z) (not_cp(X), not_cp(Y), not_cp(Z))  
         not_cp(X), not_cp(Y), not_cp(Z),!,
         sat_comp([comp(X,Y,Z)|R1],R2,_,F).                         
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F):-            % comp(cp(A,B),cp(C,D),S)            
         nonvar(X), X = cp(A,B), nonvar(Y), Y = cp(C,D),!,
         (sat_step([inters(B,C,N1), N1 = {}, Z = {}|R1],R2,_,F)
          ; 
          sat_step([inters(B,C,N1), N1 neq {}, Z = cp(A,D), set(N1)|R1],R2,_,F)
         ).  
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F):-            % comp(cp(A,B),R,S)                 
         nonvar(X), X = cp(A,B),!,
         sat_step([dres(B,Y,N1), ran(N1,N2), Z = cp(A,N2), rel(N1),set(N2)|R1],R2,_,F).    
sat_comp_cp([comp(X,Y,Z)|R1],R2,c,F):-            % comp(R,cp(A,B),S)                 
         nonvar(Y), Y = cp(A,B),!,
         sat_step([rres(X,A,N1), dom(N1,N2), Z = cp(N2,B), rel(N1),set(N2)|R1],R2,_,F).    

%%%%%%%%%%%%%%%%%%%%%% domain of partial function (dompf/2) 

sat_dompf([dompf(X,Y)|R1],R2,c,F):-                   % dom(X,X)
        var(X),var(Y),X==Y,!, X = {},                          
        sat_step(R1,R2,_,F).
sat_dompf([dompf(S,D)|R1],[dompf(S,D)|R2],Stop,F):-   % dom(S,D), var(S), var(D) (irreducible form) 
        var(S),var(D),!,            
        sat_step(R1,R2,Stop,F).
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom({},d) or dom(int(a,b),d) with a>b
        nonvar(S),is_empty(S),!, 
        sunify(D,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(s,{}) or dom(s,int(a,b)) with a>b
        nonvar(D),is_empty(D),!, 
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                      
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom({[...],...},D) or dom({[...],...},{...}) or dom({[...],...},int(t1,t2))      
        nonvar(S), S = SR with [A1,_A2], !,
        sunify(D,DR with A1,C),
        append(C,R1,R3),
        sat_step([dompf(SR,DR)|R3],R2,_,F).                      
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,int(a,a)), var(S)
        var(S), closed_intv(D,A,B), A==B,!,
        S = {} with [A,_],
        sat_step(R1,R2,_,F).                         
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,int(a,b)), var(S)
        var(S), closed_intv(D,A,B), A<B,!,
        S = SR with [A,_],
        A1 is A + 1,
        sat_step([dompf(SR,int(A1,B))|R1],R2,_,F).                           
sat_dompf([dompf(S,D)|R1],R2,c,F):-                   % dom(S,{...}) or dom(S,int(A,B)), var(S)
        var(S), nonvar(D),
        sunify(D,DR with A1,C),!,
%        S = SR with [A1,_A2],
        sunify(S,SR with [A1,_A2],_),
        append(C,R1,R3),
        sat_step([dompf(SR,DR)|R3],R2,_,F).  
%        sat_step([A1 nin DR,dompf(SR,DR)|R3],R2,_,F). 

%%%%%%%%%%%%%%%%%%%%%% composition of partial functions (comppf/3) 

                                         % comppf({},s,t) or comppf(int(a,b),s,t) with a>b
sat_comppf([comppf(R,_S,T)|R1],R2,c,F):-
        nonvar(R),is_empty(R),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).
                                         % comppf(r,{},t) or comppf(r,int(a,b),t) with a>b
sat_comppf([comppf(_R,S,T)|R1],R2,c,F):-
        nonvar(S),is_empty(S),!, 
        sunify(T,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).
                                         % comppf(R,s,T) or comppf(r,S,T), r and s not empty set,        
                                         % irreducible forms                        
sat_comppf([comppf(R,S,T)|R1],[comppf(R,S,T)|R2],Stop,F):-  
        (var(R),var_or_empty(T),! 
        ; 
         var(S),var_or_empty(T)
        ),!,         
        sat_step(R1,R2,Stop,F).
                                         % comppf({[X,Y]/R},{[A,B]/S},{})
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-      
        nonvar(R), R = RR with [X,Y], 
        nonvar(S), S = SS with [A,B], 
        nonvar(T),is_empty(T), !,
        sat_step([A neq Y,
                  comppf({} with [X,Y],SS,{}),
                  comppf(RR,{} with [A,B],{}),
                  comppf(RR,SS,{}) | R1],R2,_,F).
                                         % comppf({[X,Y]},{[Z,V]},T)                                   
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-      
        nonvar(R), R = RR with [X,Y1], nonvar(RR), is_empty(RR),
        nonvar(S), S = SS with [Y2,Z], nonvar(SS), is_empty(SS), !,
        (sat_step([Y1 = Y2, T = {} with [X,Z] | R1],R2,_,F)    
         ;
         sat_step([Y1 neq Y2, T = {} |R1],R2,_,F)
        ). 
                                         % comppf({[X,Y]/R},{[Y,Z]/S},{[X,Z]/T})
sat_comppf([comppf(R,S,T)|R1],R2,c,F):- 
        nonvar(T), T = TT with [X,Z], !,
        sat_step([R = RR with [X,Y], S = SS with [Y,Z],
                  [X,Y] nin RR, [Y,Z] nin SS,
                  comppf(RR,{} with [Y,Z],N1),comppf(RR,SS,N2),
                  un(N1,N2,TT) | R1],R2,_,F).
                                         % comppf({[X,Y],...},{...},T), T var.  
sat_comppf([comppf(R,S,T)|R1],R2,c,F):-     
        var(T),
        nonvar(R), R = RR with [X,Y],!, 
       (
         sunify(S,SS with [Y,Z],C2),     % Y in dom S
         append(C2,R1,R3),
         sat_step([[Y,Z] nin SS,
                  comppf(RR,{} with [Y,Z],N1),
                  comppf(RR,SS,N2),
                  un(N1,N2,TT),
                  T = TT with [X,Z] | R3],R2,_,F)
       ;
        sat_step([comppf({[Y,Y]},S,{}),  % Y nin dom S
                  comppf(RR,S,T) | R1],R2,_,F)
       ).


%%%%%%%%%%%%%%%%%%%%%% identity for partial functions (id/2)  

sat_id([id(A,S)|R1],R2,c,F):-                  % id(X,X)
        var(A),var(S), samevar(A,S),!,
        A = {},
        sat_step(R1,R2,_,F).       
sat_id([id(A,S)|R1],[id(A,S)|R2],Stop,F):-     % id(X,Y) (irreducible form) 
        var(A),var(S),!,                           
        sat_step(R1,R2,Stop,F).
sat_id([id(A,S)|R1],R2,c,F):-                  % id({},S) or id(int(a,b),S) with a>b
        nonvar(A),is_empty(A),!,    
        sunify(S,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_id([id(A,S)|R1],R2,c,F):-                  % id(R,{}) 
        nonvar(S),is_empty(S),!,   
        sunify(A,{},C),
        append(C,R1,R3),
        sat_step(R3,R2,_,F).                         
sat_id([id(A,S)|R1],R2,c,F):-                  % id(int(a,b),S) or id(int(a,b),{...})      
        nonvar(A), closed_intv(A,X,Y), !,   
        sunify(S,SR with [X,X],C1), append(C1,R1,R3),
        X1 is X+1,
        sat_step([[X,X] nin SR,id(int(X1,Y),SR),rel(SR)|R3],R2,_,F).   
sat_id([id(A,S)|R1],R2,R,F):-                   % id(cp(...),S) or id(S,cp(...))
        (nonvar(A), is_cp(A,_,_),!
         ;
         nonvar(S), is_cp(S,_,_)
        ),!,
        sat_id_cp([id(A,S)|R1],R2,R,F).      
sat_id([id(A,S)|_R1],_R2,c,_F) :-              % id({.../R},R), var R (special case)
        nonvar(A), var(S),
        tail(A,TA), samevar(TA,S),!,
        fail.
sat_id([id(A,S)|_R1],_R2,c,_F) :-              % id(R,{.../R}), var R (special case)
        nonvar(S), var(A), 
        tail(S,TS), samevar(TS,A),!,
        fail.                               
sat_id([id(A,S)|R1],R2,c,F) :-                 % id({.../R},{.../R}), var R (special case)
        nonvar(A),  tail(A,TA), var(TA),
        nonvar(S),  tail(S,TS), var(TS),
        samevar(TA,TS),!,
        TA = {},
        sat_step([id(A,S)|R1],R2,_,F).                                                                    
sat_id([id(A,S)|R1],R2,c,F):-                  % id({...},S) or id({...},{...})      
        nonvar(A), A = _ with X, !,
        sunify(A,AR with X,C1), append(C1,R1,C1R1),
        sunify(S,SR with [X,X],C2), append(C1R1,C2,R3),
        sat_step([X nin AR,[X,X] nin SR,id(AR,SR),set(AR),rel(SR)|R3],R2,_,F).                                          
sat_id([id(A,S)|R1],R2,c,F):-                     % id(A,{...}), var(A)     
        var(A), nonvar(S), S = _ with [X,X], !,
        sunify(S,SR with [X,X],C1), append(C1,R1,R3),
        sunify(A,AR with X,C2), append(C2,R3,R4),
%        A = AR with X,
        sat_step([X nin AR,[X,X] nin SR,id(AR,SR),set(AR),rel(SR)|R4],R2,_,F).

sat_id_cp([id(A,S)|R1],[id(A,S)|R2],Stop,F):-     % id(A,S) (irreducible form) 
        var_st(A), var_st(S),!,  
        %write('irreducible form CP'),nl,
        sat_step(R1,R2,Stop,F).             

sat_id_cp([id(A,S)|R1],R2,c,F) :-                 % id(A*B,A) (special case)
        nonvar(A), A = cp(_,_), 
        tail_cp(S,TS), 
        tail_cp(A,TA), samevar(TA,TS),!,
        %write(sat_un_cp_special),nl, 
        TS = {},                          
        sat_step([id(A,S)|R1],R2,_,F).          

sat_id_cp([id(A,S)|R1],R2,c,F):-                  % id(cp(...),s)
        nonvar(A), A = cp(S1,S2),
        S1 = Xr with X, S2 = Yr with Y,!,
        %write('id(cp(...),s)'),nl,
        sunify(S,N1 with [[X,Y],[X,Y]],C),
        append(C,R1,R3),
        sat_step([id(N2,N1), 
                  un(cp({} with X,Yr),cp(Xr,Yr with Y),N2),
                  rel(N1),set(N2) |R3],R2,_,F).
sat_id_cp([id(A,S)|R1],R2,c,F):-                  % id(s,cp(...)) 
        nonvar(S), S = cp(Xr,Yr),!,
        %write('id(s,cp(...))'),nl,
        (sat_step([A={}, Xr={} | R1],R2,_,F)
         ;
         sat_step([A={}, Yr={} | R1],R2,_,F)
         ;
         sat_step([A={} with _N, Xr=A, Yr=A | R1],R2,_,F)
        ).


%%%%%%%%%%%%
%%%%%% Rewriting rules for defined constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%% range of a binary relation (ran/2)

%sat_ran([ran(R,A)|R1],R2,c,F) :-    % replaced by ad-hoc implementation (see above) for efficiency reasons           
%        sat_step([inv(R,S),dom(S,A)|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% domain restriction (dres/3)
                        
sat_dres([dres(A,R,S)|R1],R2,Stop,nf) :-         % dres(A,R,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
%        sat_step([delay(dres(A,R,S),novar3(A,R,S)) | R1],R2,Stop,nf).   
        sat_step([delay(dres(A,R,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).   
sat_dres([dres(A,R,S)|R1],R2,c,F):-              % dres(A,R,S)
        sat_step([un(S,T,R),rel(T),dom(S,B),set(B),subset(B,A),dom(T,C),set(C),disj(A,C)
        |R1],R2,_,F).   

sat_drespf([drespf(A,R,S)|R1],R2,c,F):-          % drespf(A,R,S) -  only for partial functions
        sat_step([dom(R,DR),set(DR),inters(A,DR,I),subset(S,R),dom(S,I)|R1],R2,_,F).                          

novar3(A,_R,_S) :- nonvar(A),!.
novar3(_A,R,_S) :- nonvar(R),!.
novar3(_A,_R,S) :- nonvar(S).

%%%%%%%%%%%%%%%%%%%%%% range restriction (rres/3)

sat_rres([rres(R,A,S)|R1],R2,Stop,nf) :-         % rres(R,A,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
%        sat_step([delay(rres(R,A,S),novar3(A,R,S)) | R1],R2,Stop,nf).   
        sat_step([delay(rres(R,A,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).   
sat_rres([rres(R,A,S)|R1],R2,c,F):-              % rres(R,A,S)
        sat_step([un(S,T,R),rel(T),ran(S,B),set(B),subset(B,A),ran(T,C),set(C),disj(A,C)
        |R1],R2,_,F).  

%%%%%%%%%%%%%%%%%%%%%% domain anti-restriction (dares/3)

sat_dares([dares(A,R,S)|R1],R2,Stop,nf) :-       % dares(A,R,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
%        sat_step([delay(dares(A,R,S),novar3(A,R,S)) | R1],R2,Stop,nf).                         
        sat_step([delay(dares(A,R,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).                         
sat_dares([dares(A,R,S)|R1],R2,c,F) :-           % dares(A,R,S)
        sat_step([un(S,T,R),rel(T),dom(S,B),set(B),dom(T,C),set(C),subset(C,A),disj(A,B)
        |R1],R2,_,F).                         

%%%%%%%%%%%%%%%%%%%%%% range anti-restriction (rares/3)

sat_rares([rares(R,A,S)|R1],R2,Stop,nf) :-       % rares(R,A,S), A,R,S variables: delayed
        var(A), var(R), var(S), !,
%        sat_step([delay(rares(R,A,S),novar3(A,R,S)) | R1],R2,Stop,nf).   
        sat_step([delay(rares(R,A,S),prolog_call(novar3(A,R,S))) | R1],R2,Stop,nf).   
sat_rares([rares(R,A,S)|R1],R2,c,F):-            % rares(R,A,S)
        sat_step([un(S,T,R),rel(T),ran(S,B),set(B),ran(T,C),set(C),subset(C,A),disj(A,B)
        |R1],R2,_,F).   

%%%%%%%%%%%%%%%%%%%%%% partial function application (apply/3)

sat_apply([apply(S,X,Y)|R1],R2,c,F):-            % apply(F,X,Y)
        sat_step([[X,Y] in S|R1],R2,_,F).  

%%%%%%%%%%%%%%%%%%%%%% overriding (oplus/3)

sat_oplus([oplus(R,S,T)|R1],R2,c,F):-            % oplus(R,S,T)
        sat_step([dom(S,N1),dares(N1,R,N2),un(N2,S,T),set(N1),rel(N2)|R1],R2,_,F).  

%%%%%%%%%%%%
%%%%%% Rewriting rules for NEGATIVE constraints over binary relations and partial functions %%%%%%
%%%%%%%%%%%%
                       
%%%%%%%%%%%%%%%%%%%%%% not binary relation (nrel/1)

sat_nrel([nrel(X)|R1],R2,c,F):-                  % nrel(X)
        sat_step([set(X), N in X, npair(N) |R1],R2,_,F).  

%%%%%%%%%%%%%%%%%%%%%% not partial function (npfun/1)

sat_npfun([npfun(X)|R1],R2,c,F):-                % npfun(X)
        (sat_step([set(X), [N1,N2] in X, [N1,N3] in X, N2 neq N3 |R1],R2,_,F)
         ;
         sat_step([set(X), nrel(X) |R1],R2,_,F)    
        ).   

%%%%%%%%%%%%%%%%%%%%%% not pair (npair/1)

sat_npair([npair(X)|R1],[npair(X)|R2],Stop,F):-  % npair(X), var(X), (irreducible form)
        var(X),!,
        sat_step(R1,R2,Stop,F).
sat_npair([npair(X)|R1],R2,c,F):-                % npair(f(a,b)) 
        functor(X,Funct,Arity),
        (Funct \== '[|]',! ; Arity \== 2),!,
        sat_step(R1,R2,_,F).
sat_npair([npair(X)|R1],R2,c,F):-                % npair([a]) 
        X = [_],
        sat_step(R1,R2,_,F).
sat_npair([npair(X)|R1],R2,c,F):-                % npair([a,b,c,...])
        X = [_A|R], R = [_|S],
        sat_step([S neq []|R1],R2,_,F).

%%%%%%%%%%%%%%%%%%%%%% not domain (ndom/2)

sat_ndom([ndom(R,A)|R1],R2,c,F):-                % ndom(R,A)
        (sat_step([[N1,_N2] in R, N1 nin A |R1],R2,_,F)
         ;
%         sat_step([N1 in A, dom(R,D), N1 nin D, set(D)|R1],R2,_,F)    
         sat_step([N1 in A, comp({} with [N1,N1],R,{}) |R1],R2,_,F)  
         ;
         sat_step([nrel(R)|R1],R2,_,F)    
        ).   

%%%%%%%%%%%%%%%%%%%%%% not inverse (ninv/2)

sat_ninv([ninv(R,S)|R1],R2,c,F):-                % ninv(R,S)
        (sat_step([[N1,N2] in R, [N2,N1] nin S|R1],R2,_,F)
         ;
         sat_step([[N1,N2] nin R, [N2,N1] in S|R1],R2,_,F)    
         ;
         sat_step([nrel(R)|R1],R2,_,F)    
         ;
         sat_step([nrel(S)|R1],R2,_,F)    
        ).   

%%%%%%%%%%%%%%%%%%%%%% not composition (ncomp/3)

% NEW MAXI 2017
sat_ncomp([ncomp(R,S,T)|R1],R2,c,F):-            % ncomp(R,S,T)
        (sat_step([[X,Y] in R, [Y,Z] in S, [X,Z] nin T|R1],R2,_,F)
         ;
         sat_step([[X,Z] in T,
                   comp({} with [X,X],R,N1),
                   comp(S,{} with [Z,Z],N2),
                   comp(N1,N2,{}) |R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
         ;
         sat_step([nrel(T)|R1],R2,_,F)
         ). 

%%%%%%%%%%%%%%%%%%%%%% not range (nran/2)

sat_nran([nran(R,A)|R1],R2,c,F):-                % nran(R,A)
        (sat_step([[_N1,N2] in R, N2 nin A|R1],R2,_,F)
         ;
%         sat_step([ran(R,RR), N2 nin RR, N2 in A, set(RR) |R1],R2,_,F)    
         sat_step([N1 in A, comp(R,{} with [N1,N1],{})|R1],R2,_,F)    
         ;
         sat_step([nrel(R)|R1],R2,_,F)    
        ).   

%%%%%%%%%%%%%%%%%%%%%% not domain restriction (ndres/3)

sat_ndres([ndres(A,R,S)|R1],R2,c,F):-               
        (sat_step([[N1,_N2] in S,N1 nin A|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in R,N1 in A,[N1,N2] nin S|R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
        ). 

%%%%%%%%%%%%%%%%%%%%%% not domain anti-restriction (ndares/3)

sat_ndares([ndares(A,R,S)|R1],R2,c,F):-               
        (sat_step([[N1,_N2] in S,N1 in A|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in R,N1 nin A,[N1,N2] nin S|R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
        ).   
  
%%%%%%%%%%%%%%%%%%%%%% not range restriction (nrres/3)

sat_nrres([nrres(R,A,S)|R1],R2,c,F):-               
        (sat_step([[_N1,N2] in S,N2 nin A|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in S,[N1,N2] nin R|R1],R2,_,F)
         ;
         sat_step([[N1,N2] in R,N2 in A,[N1,N2] nin S|R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
        ). 

%%%%%%%%%%%%%%%%%%%%%% not range anti-restriction (nrares/3)

sat_nrares([nrares(R,A,S)|R1],R2,c,F):-               
        (sat_step([[_N1,N2] in S,N2 in A |R1],R2,_,F)
         ;
         sat_step([[N1,N2] in S,[N1,N2] nin R |R1],R2,_,F)
         ;
         sat_step([[N1,N2] in R,N2 nin A,[N1,N2] nin S |R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
        ). 

%%%%%%%%%%%%%%%%%%%%%% not function application (napply/3)

sat_napply([napply(S,X,Y)|R1],R2,c,F):-                      
         (sat_step([[X,Y] nin S|R1],R2,_,F)
          ;
          sat_step([delay(npfun(S),false)|R1],R2,_,F)).


%%%%%%%%%%%%%%%%%%%%%% not relational image (nrimg/3)

sat_nrimg([nrimg(R,A,B)|R1],R2,c,F):-               
         (sat_step([N0 nin B,dres(A,R,N1),[N3,N0] in N1,N3 in A,rel(N1)|R1],R2,_,F)
          ;
          sat_step([N0 in B,dres(A,R,N1),ran(N1,N2),N0 nin N2,rel(N1),set(N2)|R1],R2,_,F)
          ;
          sat_step([nrel(R)|R1],R2,_,F)
         ).

%%%%%%%%%%%%%%%%%%%%%% not overriding (noplus/3)

sat_noplus([noplus(R,S,T)|R1],R2,c,F):-               
        (sat_step([[N1,N2] in T,[N1,N2] nin S,[N1,N2] nin R |R1],R2,_,F)
         ;
         sat_step([[N1,N2] nin T, [N1,N2] in S |R1],R2,_,F)
         ;
         sat_step([[N2,N3] in T,[N2,N3] nin S,dom(S,N1),N2 in N1,set(N1) |R1],R2,_,F)
         ;
         sat_step([[N2,N3] nin T,[N2,N3] in R,dom(S,N1),N2 nin N1,set(N1) |R1],R2,_,F)
         ;
         sat_step([nrel(R)|R1],R2,_,F)
         ;
         sat_step([nrel(S)|R1],R2,_,F)
         ;
         sat_step([nrel(T)|R1],R2,_,F)
        ). 

%%%%%%%%%%%%%%%%%%%%%% not identity (nid/2)

sat_nid([nid(A,S)|R1],R2,c,F):-               
        (sat_step([N1 in A, [N1,N1] nin S |R1],R2,_,F)
         ;
         sat_step([N1 neq N2, [N1,N2] in S |R1],R2,_,F)
         ;
         sat_step([N1 nin A, [N1,N1] in S |R1],R2,_,F)
         ;
%         sat_step([npfun(S) |R1],R2,_,F)    
        sat_step([P in S, npair(P) |R1],R2,_,F)    
        ). 


%%%%%%%%%%%%
%%%%%%%%%%%% Rewriting rules for control constraints %%%%%%%%%%%%
%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%% delay mechanism               

sat_delay([delay(irreducible(A) & true,G)|R1],R2,c,f) :- 
        final,                         
        solve_goal(G,C1),!,
        solve_goal(A,C2),
        append(C1,C2,C3),
        append(C3,R1,R3),
        sat_step(R3,R2,_,f).
sat_delay([delay(irreducible(A) & true,G)|R1],[delay(irreducible(A) & true,G)|R2],Stop,f) :- 
        final,!,
        sat_step(R1,R2,Stop,f).

sat_delay([delay(A,_G)|R1],R2,c,f) :- 
        final,!, 
        solve_goal_nodel(A,C2),
        append(C2,R1,R3),
        sat_step(R3,R2,_,f).

sat_delay([delay(A,G)|R1],R2,c,F) :- 
        solve_goal(G,C1),!,
        sat_delay_atom(A,A1),    
        solve_goal(A1,C2),
        append(C1,C2,C3),
        append(C3,R1,R3),
        sat_step(R3,R2,_,F).
sat_delay([X|R1],[X|R2],Stop,F):-
        sat_step(R1,R2,Stop,F).

sat_delay_atom(irreducible(A) & true,A) :- !.
sat_delay_atom(A,A).


%%%Solve goal G without generating any new delay
solve_goal_nodel(G,ClistNew) :-
       constrlist(G,GClist,GAlist),
       solve_goal_nodel(GClist,GAlist,ClistNew). 

solve_goal_nodel(Clist,[],CListCan):- !, 
       sat(Clist,CListCan,f). 
solve_goal_nodel(Clist,[true],CListCan):- !, 
       sat(Clist,CListCan,f). 
solve_goal_nodel(Clist,[A|B],CListOut):-
       sat(Clist,ClistSolved,f),
       sat_or_solve(A,ClistSolved,ClistNew,AlistCl,f),
       append(AlistCl,B,AlistNew),
       solve_goal_nodel(ClistNew,AlistNew,CListOut).


%%%%%%%%%%%%%%%%%%%%%%% solved mechanism              

% solved(C,G,Lev,Mode): constraint C is considered solved (i.e. not 
% further processed) at solver level Lev, while goal G is true;
% in final mode, if Mode is 'nf', the constraint C is anyway
% considered no longer solved

sat_solved([solved(C,G,Lev,Mode)|R1],R2,R,F):-
       call(G),!, 
       test_final([solved(C,G,Lev,Mode)|R1],R2,R,F).
sat_solved([solved(C,_,_,_)|R1],R2,c,F):-     
       sat_step([C|R1],R2,_,F).

test_final([solved(C,G,Lev,Mode)|R1],[solved(C,G,Lev,Mode)|R2],Stop,nf) :- !,
       sat_step(R1,R2,Stop,nf).
test_final([solved(C,G,Lev,Mode)|R1],[solved(C,G,Lev,Mode)|R2],Stop,f) :- 
       Mode == f,!,                            % final sat: G is true and in final mode
       sat_step(R1,R2,Stop,f).                 %  --> mantain solved
test_final([solved(C,_,_,_)|R1],R2,c,f) :-     % final sat: G is true and not in final mode
       sat_step([C|R1],R2,_,f).                %  --> remove solved

      
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%      Level 2     %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%  Check pairs of constraints   %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     
global_check1([],_,[],_) :- !.
global_check1([glb_state(Rel)|RC],GC,[glb_state(Rel)|NewC],F) :- !,
    global_check1(RC,GC,NewC,F).  

%%%%%%%%%%%%%%%%%%%%%%%%%%%% type clashes

global_check1([C|RC],GC,[C|NewC],F) :-   % type clashes --> fail  
    type_constr(C),!,
    no_type_error_all(C,RC),   
    global_check1(RC,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% neq elimination: X neq t, X set variable (only in final mode)

global_check1([C|RC],GC,NewC,f) :-       % neq: W neq T and W or T set variables 
    \+noneq_elim, 
    is_neq(C,1,W,T),
    var(W), var(T),
    find_setconstraint(W,T,GC,X,Y),!,
    trace_irules('setvar-neq_var'),
    mk_new_constr(X,Y,OutC),
    append(OutC,CC,NewC),
    global_check1(RC,GC,CC,f).
global_check1([C|RC],GC,NewC,f) :-       % neq: W neq {...} and W a set variable
    \+noneq_elim, 
    is_neq(C,1,W,T),
    var(W), nonvar(T), is_set(T),
    find_setconstraint(W,GC),!,
    trace_irules('setvar-neq_set'),
    mk_new_constr2(W,T,OutC),
    append(OutC,CC,NewC),
    global_check1(RC,GC,CC,f).

global_check1([C|RC],GC,[size(R,M),X nin R,M>=0|NewC],f) :-       
    \+noneq_elim, 
    is_size(C,_,S,N),
    get_domain(N,N in ..(A,_)),
    nonvar(A),A > 0,!,
    trace_irules('size-neq'),
    S = R with X,
    solve_int(M is N-1,_IntC),  
    global_check1(RC,GC,NewC,f).

global_check1([C|RC],GC,[C|NewC],F):-!,  % all other constraints - nothing to do
    global_check1(RC,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% inference rules

global_check2([],_,[],_) :- !.
global_check2([glb_state(Rel)|RC],GC,[glb_state(Rel)|NewC],F) :- !,
    global_check2(RC,GC,NewC,F).              
global_check2([X neq Y|RC],GC,[X neq Y|NewC],F) :- !,
    global_check2(RC,GC,NewC,F).  
global_check2([C|RC],GC,[C|NewC],F) :- 
    type_constr(C),!,
    global_check2(RC,GC,NewC,F).  
global_check2([solved(C,Cond,Lvl,Mode)|RC],GC,NewC,F) :- !,    
    global_check2(C,[solved(C,Cond,Lvl,Mode)|RC],GC,NewC,F).   
global_check2([C|RC],GC,NewC,F) :- 
    global_check2(C,[C|RC],GC,NewC,F).   

%%%%%%%%%% unicity property 

global_check2(dom(_,_),[C|RC],GC,NewC,F) :-       % dom-dom: dom(X,N) & dom(X,M) --> dom(X,M) & N=M
    is_dom_l(C,_,X,N,_),
    var(X),
    find_dom(X,RC,M),!,
    trace_irules('dom-dom'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(dompf(_,_),[C|RC],GC,NewC,F) :-     % dompf-dompf: dompf(X,N) & dompf(X,M) --> dompf(X,M) & N=M
    is_dom_l(C,_,X,N,_),                          %GFR - fattorizzare
    var(X),
    find_dom(X,RC,M),!,
    trace_irules('dom-dom'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(ran(_,_),[C|RC],GC,NewC,F) :-       % ran-ran: ran(X,N) & ran(X,M) --> ran(X,M) & N=M
    is_ran_l(C,_,X,N),
    var(X),
    find_ran(X,RC,M),!,
    trace_irules('ran-ran'),
    sunify(N,M,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(un(_,_,_),[C|RC],GC,NewC,F) :-       % un-un: un(X,Y,Z1) & un(Y,X,Z2) --> un(X,Y,Z1) & Z1 = Z2
    is_un_l(C,_,X,Y,Z1),
    var(X),var(Y),var(Z1),
    find_un2(X,Y,RC,Z2), !,
    trace_irules('un-un'),
    sunify(Z1,Z2,CEq),
    append(CEq,NewC1,NewC),
    global_check2(RC,GC,NewC1,F).
global_check2(size(_,_),[C|RC],GC,NewC,F) :-       % size-size: size(S,N) & size(S,M) ---> size(S,M) & N=M
    is_size(C,1,X,N), 
    var(X),                                              
    find_size(X,RC,M),!,
    trace_irules('size-size'),
    N = M,
    global_check2(RC,GC,NewC,F).
global_check2(delay((size(_,_) & true),_),C,GC,NewC,F) :-      
    global_check2(size(_,_),C,GC,NewC,F).       
global_check2(min(_,_),[C|RC],GC,NewC,F) :-       % min-min: min(S,N) & min(S,M) ---> min(S,M) & N=M
    is_min(C,1,X,N),                   
    var(X), 
    find_min(X,RC,M),!,
    trace_irules('min-min'),
    N = M,
    global_check2(RC,GC,NewC,F).
global_check2(max(_,_),[C|RC],GC,NewC,F) :-       % max-max: max(S,N) & max(S,M) ---> max(S,M) & N=M
    is_max(C,1,X,N),                 
    var(X),                        
    find_max(X,RC,M),!,
    trace_irules('max-max'),
    N = M,
    global_check2(RC,GC,NewC,F).
global_check2(sum(_,_),[C|RC],GC,NewC,F) :-       % sum-sum: sum(S,N) & sum(S,M) ---> sum(S,M) & N=M
    is_sum(C,1,X,N),
    var(X),
    find_sum(X,RC,M),!,
    trace_irules('sum-sum'),
    N = M,
    global_check2(RC,GC,NewC,F).

%%%%%%%%%%  list constraints             % in-nin: T in X & T1 nin X (X is a list) --> T neq T1
                                         % in-in: T in X & X in T1 (X is a list) --> T neq T1      
global_check2(_ in _,[solved(T in X,G,3,f)|RC],GC,                        
             [solved(T in X,G,2,f),T neq T1|NewC],F) :- % called only after executing level 3 rules
    (find_nin(X,GC,T1) 
     ;   
     find_in(X,GC,T1)   
    ),!,
    global_check2(RC,GC,NewC,F). 

%%%%%%%%%% suppress inference rules 

global_check2(_,[C|RC],GC,[C|NewC],F) :-  
    noirules,!,
    global_check2(RC,GC,NewC,F).

%%%%%%%%%% other inference rules
                                     
global_check2(dom(_,_),C,GC,AddedC,F) :- 
    global_check2_dom(C,GC,AddedC,F),!.

global_check2(dompf(_,_),C,GC,AddedC,F) :- 
    global_check2_dompf(C,GC,AddedC,F),!.

global_check2(ran(_,_),C,GC,AddedC,F) :- 
    global_check2_ran(C,GC,AddedC,F),!.
                                        % int-not empty: int(A,B)={} & int(A,B) neq {} (A,B var) --> fail 
global_check2(_ = _,[T1 = T2|RC],GC,[T1 = T2|NewC],F) :-   
    nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2), !,
    \+find_neq(int(A,B),GC),
    global_check2(RC,GC,NewC,F).

global_check2(un(_,_,_),C,GC,AddedC,F) :- 
    global_check2_un(C,GC,AddedC,F),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%% all other constraints - nothing to do

global_check2(_,[C|RC],GC,[C|NewC],F) :-
    global_check2(RC,GC,NewC,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

%%%%%%%%%% not emptiness and size  
                                        % dom-neq: dom(S,D) & D neq {} --> dom(S,D) & D neq {} & S neq {}
global_check2_dom([C|RC],GC,AddedC,F) :-      
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(D,GC),!,   
    trace_irules('dom-neq_dom'),
    add_dom_neq(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
                                        % dom-neq: dom(S,D) & S neq {} --> dom(S,D) & D neq {} & S neq {}
global_check2_dom([C|RC],GC,AddedC,F) :-    
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(S,GC),!,    
    trace_irules('dom-neq_rel'),
    add_dom_neqd(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
                                        % dompf-neq: dompf(S,D) & D neq {} --> dompf(S,D) & D neq {} & S neq {}
global_check2_dompf([C|RC],GC,AddedC,F) :-     
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(D,GC),!,   
    trace_irules('dom-neq_dom'),
    add_dom_neq(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
                                        % dompf-neq: dompf(S,D) & S neq {} --> dompf(S,D) & D neq {} & S neq {}
global_check2_dompf([C|RC],GC,AddedC,F) :-    
    is_dom_l(C,L,S,D,RorF), 
    var(S),var(D),\+member(1,L),           
    find_neq(S,GC),!,    
    trace_irules('dom-neq_rel'),
    add_dom_neqd(RorF,S,D,AddedC,L,NewC),
    global_check2(RC,GC,NewC,F).
                                        % dompf-size: e.g., dompf(S,D) & size(S,N) -+-> size(D,N)
global_check2_dompf([C|RC],GC,[solved(dompf(S,D),(var(S),var(D)),[2|L],f),   
                        size(S,N),size(D,N),integer(N)|NewC],F) :-    
    is_dom_l(C,L,S,D,pfun),  
    var(S),var(D),\+member(2,L),          
    find_size2(S,D,GC,N),!,
    trace_irules('dompf-size'),
    global_check2(RC,GC,NewC,F).

                                        % ran-neq: ran(S,D) & D neq {} --> ran(S,D) & D neq {} & S neq {}
global_check2_ran([C|RC],GC,[solved(ran(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC],F) :-    
    is_ran_l(C,L,S,D), 
    var(S),var(D),\+member(1,L),
    find_neq(D,GC),!,          
    trace_irules('ran_var-neq_ran'),
    global_check2(RC,GC,NewC,F).
                                        % ran-neq: ran(S,{...}) --> ran(S,{...}) & S neq {}
global_check2_ran([C|RC],GC,[solved(ran(S,D),var(S),[],f),S neq {}|NewC],F) :-   
    C = ran(S,D),
    var(S), nonvar(D), noran_elim,!,          
    trace_irules('ran_nonvar-neq_ran'),
    global_check2(RC,GC,NewC,F).
                                        % ran-neq: ran(S,D) & S neq {} --> ran(S,D) & D neq {} & S neq {}
global_check2_ran([C|RC],GC,[solved(ran(S,D),var(S),[1|L],f),D neq {}|NewC],F) :-    
    is_ran_l(C,L,S,D), 
    var(S),var(D),\+member(1,L),           
    find_neq(S,GC),!,    
    trace_irules('ran-neq_rel'),
    global_check2(RC,GC,NewC,F).
                                        % ran-size: e.g., ran(S,R) & size(S,N) -+-> size(R,M) & M =< N
global_check2_ran([C|RC],GC,AddedC,F) :-    
    is_ran_l(C,L,S,R),
    var(S),var(R),\+member(2,L),            
    find_size2(S,R,GC,_),!,
    trace_irules('ran-size'),
    solve_int(M =< N,IntC),
    add_ran_size(S,R,M,N,AddedC,L,NewC1),
    append(IntC,NewC2,NewC1),
    global_check2(RC,GC,NewC2,F).
                                        % un-size:  e.g., un(X,Y,Z) & size(Z,N) -+-> 
                                        %                 size(X,NX) & size(Y,NY) & size(Z,NZ) & 
                                        %                 NX =< NZ & NY =< NZ &NX + NY >= NZ
global_check2_un([C|RC],GC,[solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[1|L],f),   
                        size(X,NX),size(Y,NY),size(Z,NZ),
                        integer(NX),integer(NY),integer(NZ)|NewC],F) :-    
    is_un_l(C,L,X,Y,Z),                  
    var(X), var(Y), var(Z),            
    \+member(1,L), find_size3(X,Y,Z,GC,_),!,
    trace_irules('un-size'),
    solve_int(NX =< NZ,IntC1),
    solve_int(NY =< NZ,IntC2),
    solve_int(NX + NY >= NZ,IntC3),
    append(IntC1,IntC2,IntC12), append(IntC12,IntC3,IntC),
    append(IntC,RC,R3),
    global_check2(R3,GC,NewC,F).

%%%%%%%%%% union and relational constraints  
                                         % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --> ...
global_check2_un([C|RC],GC,AddedC,f) :-    
    is_un_l(C,L,X,Y,Z), 
    var(X), var(Y), var(Z),            
    \+member(2,L), find_rel_pfun(Z,GC,RorF),   
    !,
    trace_irules('un-pfun-dom'),
    add_dom_un(RorF,X,Y,Z,AddedC,L,NewC),
    global_check2(RC,GC,NewC,f).
                                         % un-rel/pfun: un(X,Y,Z) & rel(Z)/pfun(Z) --> ...
global_check2_un([C|RC],GC,AddedC,f) :-    
   is_un_l(C,L,X,Y,Z),                  
   var(X), var(Y), var(Z),            
   \+member(3,L), find_rel_pfun(Z,GC,RorF),    
   !,
   trace_irules('un-pfun-ran'),
   add_ran_un(RorF,X,Y,Z,AddedC,L,NewC),
   global_check2(RC,GC,NewC,f).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%% auxiliary predicates for global_check/3

is_uncp_l(un(X,Y,Z),[],A,B) :- 
      (nonvar(X), X = cp(A,B)
       ;
       nonvar(Y), Y = cp(A,B)
       ;
       nonvar(Z), Z = cp(A,B)
      ).
is_un(un(X,Y,Z),_,X,Y,Z) :- !.              
is_un(solved(un(X,Y,Z),_,Lev,_),Lev,X,Y,Z).              
is_un_l(un(X,Y,Z),[],X,Y,Z) :- !.                            
is_un_l(solved(un(X,Y,Z),_,L,_),L,X,Y,Z).              

is_size(size(X,N),_,X,N) :- !.   
is_size(solved(size(X,N),_,Lev,_),Lev,X,N) :- !.   
is_size(delay( (size(X,N) & true), _),_,X,N).   
%is_size(delay( (irreducible(size(X,N)) & true), _),_,X,N) :- 

is_sub(subset(X,Y),_,X,Y) :- !.     

is_inters(inters(X,Y,Z),_,X,Y,Z) :- !.              

is_sum(sum(X,N),_,X,N) :- !.     
is_sum(solved(sum(X,N),_,Lev,_),Lev,X,N).     

is_min(smin(X,N),_,X,N) :- !.          
is_min(solved(smin(X,N),_,Lev,_),Lev,X,N).     

is_max(smax(X,N),_,X,N) :- !.          
is_max(solved(smax(X,N),_,Lev,_),Lev,X,N).     

is_neq(X neq Y,_,X,Y) :- !.            
is_neq(solved(X neq Y,_,Lev,_),Lev,X,Y).        

is_nin(X nin Y,_,X,Y) :- !.          

is_in(X in Y,_,X,Y) :- !.                   
is_in(solved(X in Y,_,Lev,_),Lev,X,Y) :- !.   

is_domcp_l(dom(X,N),[],A,B) :-  
     (nonvar(X),X = cp(A,B)
      ;
      nonvar(N),N = cp(A,B)
     ).
is_dom_l(dom(X,N),[],X,N,rel) :- !.       
is_dom_l(solved(dom(X,N),_,L,_),L,X,N,rel) :- !.
is_dom_l(dompf(X,N),[],X,N,pfun) :- !.     
is_dom_l(solved(dompf(X,N),_,L,_),L,X,N,pfun).

is_ran_l(ran(X,N),[],X,N) :- !.         
is_ran_l(solved(ran(X,N),_,L,_),L,X,N).

is_inv(inv(X,Y),_,X,Y) :- !.          
    
is_compcp(comp(X,Y,Z),[],A,B) :- 
      (nonvar(X), X = cp(A,B)
       ;
       nonvar(Y), Y = cp(A,B)
       ;
       nonvar(Z), Z = cp(A,B)
      ).
is_comp(comp(X,Y,Z),_,X,Y,Z) :- !.                                  
is_comp(comppf(X,Y,Z),_,X,Y,Z) :- !.                
 
is_id(id(X,Y),_,X,Y) :- !.          

is_rel(rel(X),_,X) :- !.     

is_pfun(pfun(X),_,X) :- !.     

has_ris(RIS = E,_,D) :- 
      nonvar(RIS), is_ris(RIS,ris(_ in D,_,_,_,_)), var(D), 
      nonvar(E), is_empty(E),!.             
has_ris(_ nin RIS,_,D) :- 
      nonvar(RIS), is_ris(RIS,ris(_ in D,_,_,_,_)), var(D),!.             
has_ris2(RIS1 = RIS2,_,D1,D2) :- 
      nonvar(RIS1), is_ris(RIS1,ris(_ in D1,_,_,_,_)), var(D1), 
      nonvar(RIS2), is_ris(RIS2,ris(_ in D2,_,_,_,_)), var(D2),!.             

%%%%%% searching constraints in the entire CS

find_neq(Int,cs([I neq E|_],_)) :-             
       nonvar(E), is_empty(E), I == Int,!.
find_neq(Int,cs([_|R],Others)) :- 
       find_neq(Int,cs(R,Others)).

find_setconstraint(X,cs(_,[C|_])) :-  
       is_uncp_l(C,_,S1a,S1b),               
       (X == S1a,! ; X == S1b),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_un_l(C,_,S1,S2,S3),                % un(X,_Y,_Z) or un(_Y,X,_Z) or un(_Y,_Z,X) is in the CS
       var_st(S1), var_st(S2), var_st(S3),     %GFR - test inutile?
       (X == S1,! ; X == S2,! ; X == S3),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_sub(C,_,S1,_S2),                   % subset(X,_Y) is in the CS    
       var(S1),                                   %GFR - test inutile?
       X == S1,!.
find_setconstraint(X,cs(_,[C|_])) :-                   
       is_inters(C,_,S1,S2,S3),              % inters(X,Y,Z) is in the CS   
%       var(S3),(var(S1),! ; var(S2)),            %GFR - test inutile?
       (X == S1,! ; X == S2,! ; X == S3),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_domcp_l(C,_,S1,S2),                
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_dom_l(C,_,S1,S2,_),                % dom(X,_Y) or dom(_Y,X) is in the CS
       var_st(S1), var_st(S2),                    %GFR - test inutile?
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_ran_l(C,_,S1,S2),                  % ran(X,_Y) or ran(_Y,X) is in the CS
       var(S1), %var(S2),
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_inv(C,_,S1,S2),                    % inv(X,_Y) or inv(_Y,X) is in the CS    
       var(S1), var(S2),                           %GFR - test inutile?
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                             
       is_compcp(C,_,S1a,S1b),               
       (X == S1a,! ; X == S1b),!.
find_setconstraint(X,cs(_,[C|_])) :- 
       is_comp(C,_,S1,S2,S3),                % comp(X,_Y,_Z) or comp(_Y,X,_Z) or comp(_Y,_Z,X) is in the CS
       (X == S1,! ; X == S2,! ; X == S3),!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       is_id(C,_,S1,S2),                     % id(X,_Y) or id(_Y,X) is in the CS    
       var(S1), var(S2),                        %GFR - test inutile?
       (X == S1,! ; X == S2),!.
find_setconstraint(X,cs(_,[C|_])) :-                   
       has_ris(C,_,D),                       % ris(_,D,_,_,_) = {} or T nin ris(_,D,_,_,_), D var., is in the CS 
       X == D,!.
find_setconstraint(X,cs(_,[C|_])) :-                    
       has_ris2(C,_,D1,D2),                  % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS 
       (X == D1,! ; X == D2),!.
find_setconstraint(X,cs(Neqs,[_|R])) :- 
       find_setconstraint(X,cs(Neqs,R)).

find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-                               
       is_uncp_l(C,_,S1a,S1b),               
       one_of2(X,Y,S1a,S1b,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_un(C,_,S1,S2,S3),                  % un(X,Y,Z) or un(Y,X,Z) or un(Y,Z,X) is in the CS?
       var_st(S1), var_st(S2), var_st(S3),                  %GFR - test inutile?
       one_of3(X,Y,S1,S2,S3,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_sub(C,_,S1,_S2),                   % subset(X,Y) or subset(Y,X) is in the CS?  
       var(S1),                                         %GFR - test inutile?
       one_of1(X,Y,S1,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-                  
       is_inters(C,_,S1,S2,S3),              % inters(X,Y,Z) or inters(Y,X,Z) or inters(Y,Z,X) is in the CS?
%       var(S3),(var(S1),! ; var(S2)),                 %GFR - test inutile?
       one_of3(X,Y,S1,S2,S3,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-                              
       is_domcp_l(C,_,S1,S2),                
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_dom_l(C,_,S1,S2,_),                % dom(X,Y) or dompf(Y,X) is in the CS?
       var_st(S1), var_st(S2),                            %GFR - test inutile?
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_ran_l(C,_,S1,S2),                  % ran(X,Y) or ran(Y,X) is in the CS?
       var(S1), %var(S2),                                 
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_inv(C,_,S1,S2),                    % inv(X,Y) or inv(Y,X) is in the CS?  
       var(S1), var(S2),                            %GFR - test inutile?
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-      
       is_compcp(C,_,S1a,S1b),               
       one_of2(X,Y,S1a,S1b,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_comp(C,_,S1,S2,S3),                % comp(X,Y,Z) or comp(Y,X,Z) or comp(Y,Z,X) is in the CS?
       one_of3(X,Y,S1,S2,S3,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       is_id(C,_,S1,S2),                     % id(X,Y) or id(Y,X) is in the CS?  
       var(S1), var(S2),                               %GFR - test inutile?
       one_of2(X,Y,S1,S2,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       has_ris(C,_,D),                       % ris(_,D,_,_,_) = {} or T nin ris(_,D,_,_,_), D var., is in the CS  
       one_of1(X,Y,D,Z1,Z2),!.
find_setconstraint(X,Y,cs(_,[C|_]),Z1,Z2) :-     
       has_ris2(C,_,D1,D2),                  % ris(_,D1,_,_,_) = ris(_,D2,_,_,_), D1, D2 var., is in the CS  
       one_of2(X,Y,D1,D2,Z1,Z2),!.
find_setconstraint(X,Y,cs(Neqs,[_|R]),Z1,Z2) :- 
       find_setconstraint(X,Y,cs(Neqs,R),Z1,Z2).

one_of3(X,Y,S1,_,_,X,Y) :- X == S1,!.
one_of3(X,Y,_,S2,_,X,Y) :- X == S2,!.
one_of3(X,Y,_,_,S3,X,Y) :- X == S3,!.
one_of3(X,Y,S1,_,_,Y,X) :- Y == S1,!.
one_of3(X,Y,_,S2,_,Y,X) :- Y == S2,!.
one_of3(X,Y,_,_,S3,Y,X) :- Y == S3.

one_of2(X,Y,S1,_,X,Y) :- X == S1,!.
one_of2(X,Y,_,S2,X,Y) :- X == S2,!.
one_of2(X,Y,S1,_,Y,X) :- Y == S1,!.
one_of2(X,Y,_,S2,Y,X) :- Y == S2.

one_of1(X,Y,S1,X,Y) :- X == S1,!.
one_of1(X,Y,S1,Y,X) :- Y == S1.

find_nin(X,cs(_,[C|_]),T) :-        % T nin X is in the CS
       is_nin(C,_,T,Y),     
       X == Y,!.
find_nin(X,cs(Neqs,[_|R]),T) :-
       find_nin(X,cs(Neqs,R),T).

find_in(X,cs(_,[C|_]),T) :-        % T in X is in the CS   
       is_in(C,_,T,Y),     
       X == Y,!.
find_in(X,cs(Neqs,[_|R]),T) :-  
       find_in(X,cs(Neqs,R),T).

find_size2(X,Y,cs(_,[C|_]),N) :-    % size(X,N) or size(Y,N) is in the CS
       is_size(C,_,S,N),
       (X == S,! ; Y == S),!.
find_size2(X,Y,cs(Neqs,[_|R]),M) :- 
       find_size2(X,Y,cs(Neqs,R),M).

find_size3(X,Y,Z,cs(_,[C|_]),N) :-  % size(X,N) or size(Y,N) or size(Z,N) is in the CS
       is_size(C,_,S,N),
       (X == S,! ; Y == S,! ; Z == S),!.
find_size3(X,Y,Z,cs(Neqs,[_|R]),M) :- 
       find_size3(X,Y,Z,cs(Neqs,R),M).

find_rel(X,cs(_,[C|_])) :-          % rel(X) is in the CS  
       is_rel(C,_,Y),
       X == Y,!.
find_rel(X,cs(Neqs,[_|R])) :- 
       find_rel(X,cs(Neqs,R)).

find_pfun(X,cs([C|_],_)) :-         % pfun(X) is in the CS  
       is_pfun(C,_,Y),
       X == Y,!.
find_pfun(X,cs([_|R],Others)) :- 
       find_pfun(X,cs(R,Others)).

find_rel_pfun(X,CS,RorF) :-         % either rel(X) or pfun(X) is in the CS  
       (find_rel(X,CS),!, RorF=rel ; find_pfun(X,CS), RorF=pfun).

%%%%%% searching constraints in the rest of the CS

find_un2(X,Y,[C|_],S3) :-           % un(X,Y,_Z) or un(Y,X,_Z) is in the CS
       is_un_l(C,_,S1,S2,S3), 
       (X == S1, Y == S2,! ; X == S2, Y == S1),!.
find_un2(X,Y,[_|R],S3) :- 
       find_un2(X,Y,R,S3).

find_size(X,[C|_],N) :-             % size(X,N) is in the CS
       is_size(C,_,S,N),
       X == S,!.
find_size(X,[_|R],M) :- 
       find_size(X,R,M).

find_sum(X,[C|_],N) :-              % sum(X,N) is in the CS
       is_sum(C,_,S,N),
       X == S,!.
find_sum(X,[_|R],M) :- 
       find_sum(X,R,M).

find_min(X,[C|_],N) :-              % smin(X,N) is in the CS  
       is_min(C,_,S,N),
       X == S,!.
find_min(X,[_|R],M) :- 
       find_min(X,R,M).

find_max(X,[C|_],N) :-              % smax(X,N) is in the CS 
       is_max(C,_,S,N),
       X == S,!.
find_max(X,[_|R],M) :- 
       find_max(X,R,M).

find_dom(X,[C|_],N) :-              % dom(X,N) is in the CS  
       is_dom_l(C,_,S,N,_),
       X == S,!.
find_dom(X,[_|R],M) :- 
       find_dom(X,R,M).

find_ran(X,[C|_],N) :-              % ran(X,N) is in the CS  
       is_ran_l(C,_,S,N),
       X == S,!.
find_ran(X,[_|R],M) :- 
       find_ran(X,R,M).

%%%%%% type checking 

type_constr(C) :-
       (p_type_constr(C),! ; n_type_constr(C)).

p_type_constr(set(_)).                     % positive type constraints
p_type_constr(bag(_)).
p_type_constr(list(_)).
p_type_constr(integer(_)).  
p_type_constr(rel(_)).   
p_type_constr(pfun(_)). 
p_type_constr(pair(_)). 
   
n_type_constr(nset(_)).                     % negative type constraints
n_type_constr(ninteger(_)).  
n_type_constr(nrel(_)).   
n_type_constr(npfun(_)). 
n_type_constr(npair(_)). 

no_type_error_all(_C,[]) :- !.
no_type_error_all(C,[B|R]) :- 
       C =.. [F1,X], B =.. [F2,Y], 
       X == Y, F1 \== F2, !,
       \+type_error(F1,F2),
       no_type_error_all(C,R).    
no_type_error_all(C,[_B|R]) :- 
       no_type_error_all(C,R).
 
type_error(F1,F2) :-
       incompatible(F1,LInc),
       member(F2,LInc).

incompatible(set,[nset,integer,bag,list]).
incompatible(rel,[nset,integer,bag,list]).
incompatible(pfun,[nset,integer,bag,list]).
%incompatible(pair,[npair,set,rel,pfun,integer,bag,list]).
incompatible(integer,[ninteger,set,rel,pfun,bag,list]).
incompatible(bag,[set,rel,pfun,integer,list]).
incompatible(list,[set,rel,pfun,integer,bag]).

incompatible(nset,[set,rel,pfun]).
%incompatible(nrel,[rel,pfun]).
%incompatible(npfun,[pfun]).
%incompatible(npair,[pair]).
incompatible(ninteger,[integer]).

%%%%%% replacing constraints neq

mk_new_constr(W,T,OutC):-
       W = M with N, OutC = [N nin T,set(M)].
mk_new_constr(W,T,OutC):-
       T = _M with N, OutC = [N nin W,set(T)].
mk_new_constr(W,T,OutC):-
       W = {}, OutC = [T neq {}].  

mk_new_constr2(W,T,OutC):-
       nonvar(T), is_empty(T),!,
       W = M with _N, OutC = [set(M)].
mk_new_constr2(W,T,OutC):-
       W = M with N, OutC = [N nin T,set(M)].
mk_new_constr2(W,T,OutC):-
       T = _M with N, OutC = [N nin W].

%%%%%% adding dom and ran for relations/partial functions

add_dom_un(rel,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L],f),   
                        rel(X),rel(Y),dom(X,DX),dom(Y,DY),dom(Z,DZ),
                        un(DX,DY,DZ)|NewC].
add_dom_un(pfun,X,Y,Z,AddedC,L,NewC) :-
    AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[2|L],f),   
                        pfun(X),pfun(Y),dompf(X,DX),dompf(Y,DY),dompf(Z,DZ),
                        un(DX,DY,DZ)|NewC].

add_ran_un(rel,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L],f),   
                        rel(X),rel(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].
add_ran_un(pfun,X,Y,Z,AddedC,L,NewC) :-
   AddedC = [solved(un(X,Y,Z),(var(X),var(Y),var(Z)),[3|L],f),   
                        pfun(X),pfun(Y),ran(X,RX),ran(Y,RY),ran(Z,RZ),
                        un(RX,RY,RZ)|NewC].

add_dom_neq(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC].
add_dom_neq(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L],f),S neq {}|NewC].

add_dom_neqd(rel,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dom(S,D),(var(S),var(D)),[1|L],f),D neq {}|NewC].
add_dom_neqd(pfun,S,D,AddedC,L,NewC) :-
    AddedC = [solved(dompf(S,D),(var(S),var(D)),[1|L],f),D neq {}|NewC].

add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    noran_elim,!,
    AddedC = [solved(ran(S,R),(var(S),var(R);var(S),nonvar(R),\+(is_empty(R))),[2|L],f),   
               size(S,N),size(R,M),integer(N),integer(M)|NewC].
add_ran_size(S,R,M,N,AddedC,L,NewC) :-
    AddedC = [solved(ran(S,R),(var(S),var(R)),[2|L],f),   
               size(S,N),size(R,M),integer(N),integer(M)|NewC].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%           Level 3           %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%  Labeling and final check   %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
final_sat(C,SFC):- 
      trace_in(C,3),
      final_sat1(C,SFC0), 
      final_sat2(SFC0,SFC),
      trace_out(SFC,3).  

final_sat1([],[]) :-!.
final_sat1(C,SFC):- 
      sat_empty_intv(C,CC), 
      %write(CC),nl,     
      finalize_int_constr(CC),           %finalize integer constraint processing  
      sat(CC,RevC,f),                    %call the constraint solver (in 'final' mode); 
      final_sat_cont(RevC,CC,SFC).

final_sat_cont(RevC,C,RevC) :-
      RevC == C,!.
final_sat_cont(RevC,_C,SFC) :-           %RevC is the resulting constraint; 
      final_sat1(RevC,SFC).              %otherwise, call 'final_sat' again
 
final_sat2([],[]) :-!.
final_sat2(C,SFC):- 
      finalize_int_constr(C),            %finalize integer constraint processing
      set_final, 
      sat(C,RevC,f),                     %call the constraint solver (in 'final' mode); 
      final_sat_cont2(RevC,C,SFC).

final_sat_cont2(RevC,C,RevC) :-
      RevC == C,!,
      cond_retract(final).
final_sat_cont2(RevC,_C,SFC) :-          %RevC is the resulting constraint; 
      final_sat2(RevC,SFC).              %otherwise, call 'final_sat' again
                      
sat_empty_intv([],[]) :- !.              
sat_empty_intv([T1 = T2|R1],[integer(A),integer(B)|R2]) :- 
      nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2),!,
      solve_int(A > B,IntC),
      append(IntC,R1,R3),
      sat_empty_intv(R3,R2).
sat_empty_intv([T1 neq T2|R1],[integer(A),integer(B)|R2]) :- 
      nonvar(T1), T1 = int(A,B), nonvar(T2), is_empty(T2),!,
      solve_int(A =< B,IntC),
      append(IntC,R1,R3),
      sat_empty_intv(R3,R2).
sat_empty_intv([C|R1],[C|R2]) :- 
      sat_empty_intv(R1,R2).

set_final :-             
        final,!.  
set_final :-  
        assert(final).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Integer constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve_int(Constr,NewC) :-        % solve the integer constraint 'Constr' using  
       int_solver(clpfd),!,      % either the clp(FD) solver
       solve_FD(Constr,NewC).         
solve_int(Constr,NewC) :-        % or the clp(q) solver 
       int_solver(clpq),
       solve_Q(Constr,NewC).

add_intv_w(Constr,ConstrAll,Warning) :-   %(clp(FD)) add interval constraints X in D, if any
       int_solver(clpfd),!,               % Warning is 'not_finite_domain' if at least one is found, 
       add_FDc(Constr,ConstrAll,Warning), % and labelling is on; otherwise Warning is unbound
       fd_warning(Warning).               % (clp(FD)) if Warning is on, print a warning msg
add_intv_w(Constr,Constr,_).

add_intv(Constr,ConstrAll,Warning) :-     % same as add_intv_w but without printing
       int_solver(clpfd),!,               
       add_FDc(Constr,ConstrAll,Warning). 
add_intv(Constr,Constr,_).

labeling(X) :-
       int_solver(clpfd),!,
       labeling_FD([X]).                
labeling(X) :-
       int_solver(clpq),!,
       labeling_Q(X).                

test_integer_expr(E) :-    % true if E is an integer expression; otherwise fail       
       int_solver(clpfd),!,
       on_exception(_Error,fd_expr(_X,E),fail).
test_integer_expr(E) :-         
       on_exception(_Error,q_expr(_X,E),fail).

integer_expr(E) :-         % true if E is an integer expression; otherwise print message and fail       
       int_solver(clpfd),!,
       on_exception(_Error,fd_expr(_X,E),(write('Problem in arithmetic expression'),nl,fail)).
integer_expr(E) :-                
       on_exception(_Error,q_expr(_X,E),(write('Problem in arithmetic expression'),nl,fail)).

is_int_var(X) :-
       int_solver(clpfd),!,
       is_fd_var(X).
is_int_var(X) :-
%       var(X).
        attvar(X).

check_int_constr(X,Y) :-   
       int_solver(clpfd),!,
       check_fd_constr(X,Y).
check_int_constr(X,Y) :-   
       check_q_constr(X,Y).

finalize_int_constr(C) :-   
       int_solver(clpfd),!,
       check_domain(C,L),
       labeling_FD(L).
finalize_int_constr(C) :-
       %int_solver(clpq),
       check_int_solutions(C). 
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     clp(FD) constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpfd)). 

solve_FD(Constr,NewC) :-        % Solve the constraint 'Constr' using the CLP(FD) solver   
       %%%write(solve_FD(Constr)),nl,
       tau(Constr,FD_Constr,NewC),
       call(FD_Constr).

fd_expr(X,E) :-
       X #= E.
       
tau(X is E,X #= E,[glb_state(X is E)]).   % The translation function: from SET constraints to FD    
tau(X =< Y,X #=< Y,[glb_state(X =< Y)]).  % constraints, and vice versa
tau(X >= Y,X #>= Y,[glb_state(X >= Y)]).             
tau(X < Y,X #< Y,[glb_state(X < Y)]).              
tau(X > Y,X #> Y,[glb_state(X > Y)]).              
tau(X neq T,X #\= T,[]).
tau(T in int(A,B),T in A..B,[]) :- !.
tau(T in D,T in D,[]).

is_fd_var(X) :-
       clpfd:fd_var(X).

get_domain(X,(X in D)) :-          % get_domain(X,FDc): true if X is a variable and 
       var(X),                     % FDc is the interval membership constraint for X
       clpfd:fd_dom(X,D).

%labeling_FD(_) :-                     % if nolabel, do nothing        
%       nolabel,!.                     
%labeling_FD(X) :-                     % if the variable X has a closed domain associated 
%       get_domain(X,X in D),!,     % with it, then X is (non-deterministically) instantiated 
%       labeling1(X,D).             % to every value belonging to the domain.             
%labeling_FD(_).                       % Otherwise, the predicate is true and X remains unchanghed

labeling_FD(L) :-
       labeling_FD(L,R),
       fd_labeling_strategy(Str),
       clpfd:labeling(Str,R).

labeling_FD(_,[]) :-               % if nolabel, do nothing        
       nolabel,!.                     
labeling_FD([],[]) :- !.           % if no var., do nothing        
labeling_FD([X|L],R) :-            % if the variable X has a closed domain associated with it, 
       get_domain(X,X in D),!,     % then X is added to variables that must be instantiated 
       labeling1(X,D,R1),          
       labeling_FD(L,R2),
       append(R1,R2,R).     
labeling_FD([_X|L],R) :-
       labeling_FD(L,R).           % otherwise, X is ignored

labeling1(_X,inf.._B,[]) :- !.     % e.g., X in inf..1  --> no labeling
labeling1(_X,_A..sup,[]) :- !.     % e.g., X in 1..sup  --> no labeling
labeling1(X,(I) \/ (A..sup),R) :-  % e.g., X in (inf..2)\/(4..5)\/(7..9)\/(11..sup)
        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
       (X in J, R=[X]       
        ;
        X in (inf..B), R=[]
        ;
        X in (A..sup), R=[]).
labeling1(X,(I) \/ (A..sup),R) :- !, % e.g., X in (1..2)\/(4..5)\/(7..sup)
       (X in I, R=[X]                % --> labeling on the bounded part
        ;
        X in (A..sup), R=[]).
labeling1(X,(I) \/ (In),R) :-      % e.g., X in (inf..2)\/(4..5)\/(7..9)
        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
       (X in (J) \/ (In), R=[X]
        ;
        X in (inf..B), R=[]).
labeling1(X,_D,[X]).               % e.g., X in (1..2)\/(4..5)\/(7..9)

%labeling1(_X,inf.._B) :- !.        % e.g., X in inf..1  --> no labeling
%labeling1(_X,_A..sup) :- !.        % e.g., X in 1..sup  --> no labeling
%labeling1(X,(I) \/ (A..sup)) :-    % e.g., X in (inf..2)\/(4..5)\/(7..9)\/(11..sup)
%        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
%       (X in J,
%        clpfd:indomain(X)
%        ;
%        X in (inf..B)
%        ;
%        X in (A..sup)).
%labeling1(X,(I) \/ (A..sup)) :- !, % e.g., X in (1..2)\/(4..5)\/(7..sup)
%       (X in I,                    % --> labeling on the bounded part
%        clpfd:indomain(X)
%        ;
%        X in (A..sup)).
%labeling1(X,(I) \/ (In)) :-        % e.g., X in (inf..2)\/(4..5)\/(7..9)
%        first_int(I,inf..B,J),!,   % --> labeling on the bounded part
%       (X in (J) \/ (In),
%        clpfd:indomain(X)
%        ;
%        X in (inf..B)).
%labeling1(X,_D) :-                 % e.g., X in (1..2)\/(4..5)\/(7..9)
%        clpfd:indomain(X). 
%%DBG%   clpfd:labeling([ff,down,enum],[X]).


first_int((A .. B),(A .. B),(1 .. 0)) :- !.      % first_int(+Int,?Rest,?First) 
first_int((I) \/ (In),I0,(IRest) \/ (In)) :-     % 'Int' is a disj. of intervals and
       first_int(I,I0,IRest).                    % 'First' is the first disjunct
                                                 % 'Rest' the remaining part

%add_FDc(SETc,SETFDc,R)       
%SETFDc is the list of contraints obtained from the list of constraints SETc
%by replacing all integer constraints integer(X) with the domain constraint
% X in D, where D is the FD domain of X (unless D is int(inf,sup)).
%R is either 'not_finite_domain' if at least one such integer constraint is found
%and labeling is on; otherwise, R is uninitialized

add_FDc([],[],_) :- !.                                          
add_FDc([C|SETc],[C|FDc],Warning) :-  
       \+(C = integer(_)),!,
       add_FDc(SETc,FDc,Warning).                                           
add_FDc([integer(X)|SETc],[integer(X)|FDc],Warning) :- 
       \+is_fd_var(X),!,
       add_FDc(SETc,FDc,Warning).  
add_FDc([integer(X)|SETc],FDc,Warning) :-  
       get_domain(X,FD),
       tau(X in D,FD,_), 
       (nolabel,! ; Warning = 'not_finite_domain'),
       (D == int(inf,sup),!,FDc = [integer(X)|FDcCont]
        ;
        FDc = [(X in D)|FDcCont]
       ),
       add_FDc(SETc,FDcCont,Warning).

fd_warning(R) :- 
       var(R),!.
fd_warning(_) :- 
       print_warning('***WARNING***: non-finite domain').

check_fd_constr(X,Y) :-            % if X is an integer variable
       is_int_var(X),!,            % then Y must be a simple_integer_expr;
       simple_integer_expr(Y).  
check_fd_constr(_X,_Y).      

%check_domain(C):-                        %to force labeling (if possible) for integer         
%      memberrest(integer(X),C,CRest),!,  %variables that are still uninstantiated in 
%      labeling(X),                       %the constraint C 
%      check_domain(CRest).
%check_domain(_).

check_domain(C,[X|L]):-                  %to collect all integer variables that are       
      memberrest(integer(X),C,CRest),!,  %still uninstantiated in the constraint C
      check_domain(CRest,L).
check_domain(_,[]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     clp(Q) constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(clpq)). 

solve_Q(Constr,NewC) :-             % solve the constraint 'Constr' using the CLP(Q) solver
       %%%write(solve_Q(Constr)),nl,
       rho(Constr,Q_Constr,NewC),
       %%%write(rho(Constr,Q_Constr,NewC)),nl, 
       call(Q_Constr).             

q_expr(X,E) :-
       {X = E}.        

rho(X is E,{CLPq_constr},[]) :- !,
       CLPq_constr = (X = E).
       %write('CLPQ : '),write(CLPq_constr),nl. 
rho(X =< Y,{CLPq_constr},NewC) :- !, 
       norm(X =< Y,CLPq_constr,NewC).
       %write('CLPQ : '),write(CLPq_constr),nl.                      
rho(X >= Y,{CLPq_constr},NewC) :- !,
       norm(X >= Y,CLPq_constr,NewC).
       %write('CLPQ : '),write(CLPq_constr),nl.                       
rho(X < Y,{CLPq_constr},NewC) :- !,
       norm(X < Y,CLPq_constr,NewC).
       %write('CLPQ : '),write(CLPq_constr),nl.            
rho(X > Y,{CLPq_constr},NewC) :- !,
       norm(X > Y,CLPq_constr,NewC).
       %write('CLPQ : '),write(CLPq_constr),nl.                         
%rho(X neq Y,{X =\= Y},[]) :- !.
rho(X neq Y,{CLPq_constr1 ; CLPq_constr2},NewC) :- !,
       norm(X < Y,CLPq_constr1,NewC1),
       norm(X > Y,CLPq_constr2,NewC2),
       append(NewC1,NewC2,NewC).       
       %write('CLPQ : '),write(neq(CLPq_constr1,CLPq_constr2)),nl.                         
rho(T in int(A,B),{CLPq_constr1,CLPq_constr2},NewC) :- !,
       norm(T >= A,CLPq_constr1,NewC1),
       norm(B >= T,CLPq_constr2,NewC2),
       append(NewC1,NewC2,NewC).
       %write('CLPQ : '),write(in(CLPq_constr1,CLPq_constr2)),nl.                         
rho(T in D,T in D,[]).

norm((C1,RC),NormC,NewC) :- !,       %first clause: not used        
   single_norm(C1,NormC1,NewC1),
   norm(RC,NormRC,NewC2),
   qconstr_app(NormC1,NormRC,NormC),
   append(NewC1,NewC2,NewC).
norm((C1),NormC,NewC) :-
   single_norm(C1,NormC,NewC).

single_norm(X>Y,(X=Y+K,K>=1),[integer(K)]) :-      
   var(X),var(Y),!.
single_norm(X>N,(X=N+K,K>=1),[integer(K)]) :-      
   var(X),integer(N),!.
single_norm(X>E,(X=Z+K,K>=1,Z=E),[integer(Z),integer(K)]) :-   
   var(X),!.
single_norm(N>Y,(Y=N-K,K>=1),[integer(K)]) :-      
   var(Y),integer(N),!.
single_norm(E>Y,(Y=Z-K,K>=1,Z=E),[integer(Z),integer(K)]) :-   
   var(Y),!.
single_norm(E1>E2,(Z1=Z2+K,K>=1,Z1=E1,Z2=E2),[integer(Z1),integer(Z2),integer(K)]) :-!.  
%
single_norm(X>=Y,(X=Y+K,K>=0),[integer(K)]) :-
   var(X),var(Y),!.
single_norm(X>=N,(X=N+K,K>=0),[integer(K)]) :-
   var(X),integer(N),!.
single_norm(X>=E,(X=Z+K,K>=0,Z=E),[integer(Z),integer(K)]) :-
   var(X),!.
single_norm(N>=Y,(Y=N-K,K>=0),[integer(K)]) :-      
   var(Y),integer(N),!.
single_norm(E>=Y,(Y=Z-K,K>=0,Z=E),[integer(Z),integer(K)]) :-
   var(Y),!.
single_norm(E1>=E2,(Z1=Z2+K,K>=0,Z1=E1,Z2=E2),[integer(Z1),integer(Z2),integer(K)]) :- !.
%
single_norm(E1<E2,NormC,NewC) :- !,
   single_norm(E2>E1,NormC,NewC).  
single_norm(E1=<E2,NormC,NewC) :- !,
   single_norm(E2>=E1,NormC,NewC).  

qconstr_app((C1,R1),B,(C1,R3)) :- !,        
   qconstr_app(R1,B,R3).
qconstr_app((C1),B,(C1,B)).

check_int_solutions(C) :-
%   write('ha soluzioni razionali'),nl,   %TEMP   
   collect_integer(C,LIntVars), 
%   write(LIntVars),nl,     %TEMP   
   bb_inf_all(LIntVars,LIntVars).  

collect_integer(C,LIntVars):-             %to collect in LIntVars all attributed variables         
      memberrest(integer(X),C,CRest),!,   %that are constrained to be of sort integer
      collect_integer_test(X,LIntVars1,LIntVars),
      collect_integer(CRest,LIntVars1).
collect_integer(_,[]).
collect_integer_test(X,LIntVars,[X|LIntVars]) :-
      attvar(X),!.
collect_integer_test(_X,LIntVars,LIntVars).

bb_inf_all([],_) :- !.
%bb_inf_all(L,[X|_R]) :-
%   bb_inf(L,X,_,_),!.
bb_inf_all(L,[X|_R]) :-
   bb_inf_single(L,X),!.
bb_inf_all(L,[_X|R]) :-
   bb_inf_all(L,R).

bb_inf_single(L,X) :-
   {X>=0},bb_inf(L,X,_,_).
bb_inf_single(L,X) :-
   {X<0},bb_inf(L,-X,_,_).

labeling_Q(_) :-                     % if nolabel, do nothing        
       nolabel,!.                     
labeling_Q(X) :-                     % if the variable X has a closed domain associated 
       bb_inf([X],X,Min,_V1), 
       bb_inf([X],-X,NMax,_V2), Max is -NMax,!, 
       all_int(X,Min,Max).                          
labeling_Q(_).  

all_int(M,M,M) :- !.
all_int(Min,Min,_Max). 
all_int(X,Min,Max) :-
       Min1 is Min+1,
       all_int(X,Min1,Max).

check_q_constr(X,Y) :-            % if X is an integer variable
       attvar(X),!,              % then Y must be a simple_integer_expr;
       simple_integer_expr(Y).  
check_q_constr(_X,_Y).      


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Program defined constraints 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

isetlog((true :- true),sys) :-!.
isetlog((less(A,X,C) :- 
         A = C with X & set(C) & X nin C & true),sys) :-!.
isetlog((nsubset(A,B) :- 
         set(A) & set(B) & X in A & X nin B & true),sys) :-!.
isetlog((ninters(A,B,C) :- 
         set(A) & set(B) & set(C) & 
         (X in C & X nin A & true or 
          X in C & X nin B & true or
          X in A & X in B & X nin C) & true),sys) :-!.
isetlog((diff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         subset(C,A) & un(B,C,D) & subset(A,D) & disj(B,C) & true),sys) :-!.
isetlog((ndiff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         diff(A,B,D) & D neq C & true),sys) :-!.
isetlog((sdiff(A,B,C) :- 
         set(A) & set(B) & set(C) &
         diff(A,B,D) & diff(B,A,E) & un(D,E,C) & true),sys) :-!.

isetlog((A =:= B :- 
         X is A & Y is B & X = Y & true),sys) :-!.
isetlog((A =\= B :- 
         X is A & Y is B & X neq Y & true),sys) :-!. 

isetlog((rimg(R,A,B) :-   
         set(A) & set(B) & rel(R) & dres(A,R,RA) & ran(RA,B) & true),sys)  :-!.
%isetlog((oplus(R,S,T) :-  
%         rel(R) & rel(S) & rel(T) & un(RS,S,T) & dares(DS,R,RS) & dom(S,DS) & true),sys).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     Pre / post-processor     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             preproc_goal/2,
%             preproc/3,
%             postproc/2,
%             transform_goal/2,
%             transform_clause/2,
%             is_ker/1,
%             is_sf/3 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Preprocessing 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) preprocessor: 
%%%%%%%%%%%%% from {...} (*({...})) to 'with' ('mwith') notation  

preproc_goal(G,PGext) :-
        preproc(G,PG,TypeCL), 
        norep_in_list(TypeCL,TypeCLRid),   
        list_to_conj(TypeCC,TypeCLRid),
        conj_append(PG,TypeCC,PGext).

preproc_clause(Cl,(PA :- PBext)) :-
        preproc(Cl,(PA :- PB),TypeCL), 
        norep_in_list(TypeCL,TypeCLRid),   
        list_to_conj(TypeCC,TypeCLRid),
        conj_append(PB,TypeCC,PBext).

preproc(X,X,[]):- 
        var(X),!.      
preproc(X,X,[]):-
        atomic(X),!.
preproc(X,Y1,C):-
        is_set_ext(X),!,
        set_preproc(X,Y,C),
        norep_in_set(Y,Y1). 
preproc(X,Y,C):-   
        X = int(_,_),!,
        int_preproc(X,Y,C). 
preproc(X,Y,C):-   
        X = cp(_,_),!,
        cp_preproc(X,Y,C). 
preproc(X,Y,C):-
        is_bag_ext(X),!,
        bag_preproc(X,Y,C).
preproc([A|X],[A1|X],[type(list(X))|C]):- 
        var(X), !,
        preproc(A,A1,C).
preproc((A & B),(A1 & B1),C):-
        !, preproc(A,A1,C1), preproc(B,B1,C2),
        append(C1,C2,C).
preproc((A :- B ),(A1 :- B1 ),C) :-
        !, preproc(A,A1,C1), preproc(B,B1,C2),
        append(C1,C2,C).

preproc(prolog_call(G),prolog_call(G),[]) :- !.    
preproc(naf A,naf(A1),[]) :-     
        !, preproc_goal(A,A1).
preproc(call(A),call(A1),[]) :-     
        !, preproc_goal(A,A1).
preproc(call(A,C),call(A1,C),[]) :-    
        !, preproc_goal(A,A1).
preproc(solve(A),solve(A1),[]) :-    
        !, preproc_goal(A,A1).
preproc((A)!,(A1)!,[]) :-        
        !, preproc_goal(A,A1).
preproc(delay(A,G),delay(A1,G),[]) :-    
        !, preproc_goal(A,A1).
preproc(neg A,neg(A1),[]) :-    
        !, preproc_goal(A,A1).

preproc(X,Z,C):-
        nonvar(X), 
        functor(X,F,_A), 
        =..(X,[F|ListX]),
        preproc_all(ListX,ListZ,C1),
        =..(Z,[F|ListZ]),
        (gen_type_constrs(Z,TypeC),!,
         append(C1,TypeC,C)
        ;
         C1 = C
        ).

preproc_all([],[],[]).
preproc_all([A|L1],[B|L2],C):-
        preproc(A,B,C1),
        preproc_all(L1,L2,C2),
        append(C1,C2,C).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% set preprocessing

set_preproc({},{},[]):- !.
%set_preproc(int(A,B),int(A,B),[]):- !.  
set_preproc(X with A,X with B,[type(set(X))|Constrs]) :-
        var(X),!, preproc(A,B,Constrs).       
set_preproc(X with A,Y with B,Constrs) :- 
        is_rest_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs). 
set_preproc({}(A),B,Constrs):-
        set_preproc_elems(A,B,Constrs),!.
set_preproc(_,_,_):-
        msg_sort_error(set), 
        fail.

set_preproc_elems(A,{} with A,[]):-
        var(A), !.
set_preproc_elems((A1,B1),B2 with A2,Constrs):- !,
        preproc(A1,A2,Constrs1),
        set_preproc_elems(B1,B2,Constrs2),
        append(Constrs1,Constrs2,Constrs).
set_preproc_elems(S,WT,Constrs):- 
        aggr_comps_ext(S,_A,_X),!,
        set_preproc_set(S,WT,Constrs). 
set_preproc_elems(A1,{} with A2,Constrs):-
        preproc(A1,A2,Constrs).

set_preproc_set(S,X with B,[type(set(X))|Constrs]):-  
        aggr_comps_ext(S,A,X), 
        var(X),!, 
        preproc(A,B,Constrs).
set_preproc_set(S,Y with B,Constrs):-   
        aggr_comps_ext(S,A,X), 
        is_rest_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs).

is_rest_ext(X) :-
        is_set_ext(X),!.
is_rest_ext(X) :-
        is_int(X),!.
is_rest_ext(X) :-
        is_ris(X,_),!.
is_rest_ext(X) :-
        X = cp(_,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% int preprocessing

%int_preproc(int(A,B),int(A,B),[type(integer(A)),type(integer(B))]) :-
int_preproc(int(A,B),int(A,B),[]) :-    %GFR - to be improved
        is_int(int(A,B)),!.     
int_preproc(_,_,_):- 
        msg_sort_error(int), 
        fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% cp preprocessing

cp_preproc(cp(A,B),cp(A,B),[type(set(A)),type(set(B))]) :-
        var(A),var(B),!.     
cp_preproc(cp(A,B),cp(A,B1),[type(set(A))|Constrs]) :-
        var(A),!,  %nonvar(B)
        set_preproc(B,B1,Constrs).     
cp_preproc(cp(A,B),cp(A1,B),[type(set(B))|Constrs]) :-
        var(B),!,  %nonvar(A)
        set_preproc(A,A1,Constrs).     
cp_preproc(cp(A,B),cp(A1,B1),Constrs) :-  %nonvar(A), nonvar(B)
        set_preproc(A,A1,Constrs1),
        set_preproc(B,B1,Constrs2),
        append(Constrs1,Constrs2,Constrs).       

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% bag preprocessing

bag_preproc({},{},[]):-!.   
bag_preproc(X mwith A,X mwith B,[type(bag(X))|Constrs]) :-
        var(X),!, preproc(A,B,Constrs).       
bag_preproc(X mwith A,Y with B,Constrs) :-
        is_bag_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs). 
bag_preproc((*({}(A))),B,Constrs):- 
        bag_preproc_elems(A,B,Constrs),!.
bag_preproc(_,_,_):-
        msg_sort_error(bag), 
        fail. 

bag_preproc_elems(A, {} mwith A,[]):-
        var(A),!.
bag_preproc_elems((A1,B1),B2 mwith A2,Constrs):-
        !,preproc(A1,A2,Constrs1),
        bag_preproc_elems(B1,B2,Constrs2),
        append(Constrs1,Constrs2,Constrs).
bag_preproc_elems(M,MWT,Constrs):-         
        aggr_comps_ext(M,_A,_X),!,
        bag_preproc_bag(M,MWT,Constrs).    
bag_preproc_elems(A1,{} mwith A2,Constrs):-
        preproc(A1,A2,Constrs).

bag_preproc_bag(M,X mwith B,[type(bag(X))|Constrs]):-       
        aggr_comps_ext(M,A,X), var(X),!,
        preproc(A,B,Constrs).
bag_preproc_bag(M,Y mwith B,Constrs):-!,    
        aggr_comps_ext(M,A,X), is_bag_ext(X),!,
        preproc(A,B,Constrs1), preproc(X,Y,Constrs2),
        append(Constrs1,Constrs2,Constrs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% type constraints generation

gen_type_constrs(un(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(nun(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(disj(T1,T2),[type(set(T1)),type(set(T2))]) :- !.  
gen_type_constrs(ndisj(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(subset(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(ssubset(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(inters(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !.
gen_type_constrs(size(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.   
gen_type_constrs(sum(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.
gen_type_constrs(smin(T1,T2),[type(set(T1)),type(integer(T2))]) :- !.  
gen_type_constrs(smax(T1,T2),[type(set(T1)),type(integer(T2))]) :- !. 

gen_type_constrs(dom(T1,T2),[type(rel(T1)),type(set(T2))]) :- !.   
gen_type_constrs(ran(T1,T2),[type(rel(T1)),type(set(T2))]) :- !.   
gen_type_constrs(comp(T1,T2,T3),[type(rel(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(inv(T1,T2),[type(rel(T1)),type(rel(T2))]) :- !.   
gen_type_constrs(dompf(T1,T2),[type(pfun(T1)),type(set(T2))]) :- !. 
gen_type_constrs(comppf(T1,T2,T3),[type(pfun(T1)),type(pfun(T2)),type(pfun(T3))]) :- !. 
gen_type_constrs(dres(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(drespf(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(rres(T1,T2,T3),[type(rel(T1)),type(set(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(dares(T1,T2,T3),[type(set(T1)),type(rel(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(rares(T1,T2,T3),[type(rel(T1)),type(set(T2)),type(rel(T3))]) :- !. 
gen_type_constrs(oplus(T1,T2,T3),[type(rel(T1)),type(rel(T2)),type(rel(T3))]) :- !. 

gen_type_constrs(ndom(T1,T2),[type(set(T1)),type(set(T2))]) :- !.   
gen_type_constrs(ninv(T1,T2),[type(set(T1)),type(set(T2))]) :- !.   
gen_type_constrs(ncomp(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 

gen_type_constrs(nran(T1,T2),[type(set(T1)),type(set(T2))]) :- !.   
gen_type_constrs(ndres(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 
gen_type_constrs(nrres(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 
gen_type_constrs(ndares(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 
gen_type_constrs(nrares(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 
gen_type_constrs(nrimg(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 
gen_type_constrs(noplus(T1,T2,T3),[type(set(T1)),type(set(T2)),type(set(T3))]) :- !. 

%gen_type_constrs(id(T1,T2),[type(set(T1)),type(pfun(T2))]) :- !.   
gen_type_constrs(id(T1,T2),[type(set(T1)),type(rel(T2))]) :- !.   
gen_type_constrs(apply(F,_,_),[type(pfun(F))]) :- var(F),!.
gen_type_constrs(apply(F,_,_),[type(pfun(F))]) :- nonvar(F), F \== this.

gen_type_constrs(nid(T1,T2),[type(set(T1)),type(set(T2))]) :- !.
gen_type_constrs(napply(F,_,_),[type(set(F))]) :- !.


%%%%%%%%%%%%% Auxiliary predicates for set/multiset preprocessing

is_set_ext(X):- functor(X,{},_),!.
is_set_ext(_ with _).

is_bag_ext({}):-!.
is_bag_ext(X):- X = *A, functor(A,{},_), !.
is_bag_ext(_ mwith _).

aggr_comps_ext((A \ R),A,R) :-!. 
aggr_comps_ext((A / R),A,R).          %for compatibility with previous releases

is_ker(T) :-
        nonvar(T), functor(T,F,N),
        (F \== with,! ; N \== 2).

msg_sort_error(set) :- 
       write(' wrong set term '), nl.
msg_sort_error(int) :- 
       write(' wrong interval term '), nl.
msg_sort_error(bag) :- 
       write(' wrong multiset term '), nl.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%   Intensional set preprocessing        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
sf_in_clause((H :- B),(H1 :- B1)):-
    !,sf_in_literal(H,[H1|List1]),
    sf_in_goal(B,List2),
    append(List1,List2,List),
    list_to_conj(B1,List).      
sf_in_clause(A,(H :- B)):-
    sf_in_hliteral(A,[H|List]),
    list_to_conj(B,List).

sf_in_goal(A,[A]):-
    var(A),!.    
sf_in_goal(true,[]):-!.                   
sf_in_goal(A & B,NewL):-    
    !, sf_in_literal(A,A1),
    sf_in_goal(B,B1),
    append(A1,B1,NewL).
sf_in_goal(A,NewL):-
    !, sf_in_literal(A,NewL).    

sf_in_literal(A,[A]):-                    
    var(A),!.
sf_in_literal(A or B,[A1 or B1]):-
    !, sf_in_goal(A,L1),
    sf_in_goal(B,L2),
    list_to_conj(A1,L1),
    list_to_conj(B1,L2).
sf_in_literal(prolog_call(A),[prolog_call(A)]):-!. 
sf_in_literal(neg A,[neg A1]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(naf A,[naf A1]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A),[call(A1)]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(call(A,C),[call(A1,C)]):-   
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(solve(A),[solve(A1)]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(assert(Cl),[assert(Cl1)]):-
    !, sf_in_clause(Cl,Cl1).
sf_in_literal((A)!,[(A1)!]):-
    !, sf_in_goal(A,L1),
    list_to_conj(A1,L1).
sf_in_literal(delay(A,G),[delay(A1,G1)]):-
    !, sf_in_goal(A,L1),
    sf_in_goal(G,L2),
    list_to_conj(A1,L1),
    list_to_conj(G1,L2).
sf_in_literal(forall(X in S,exists(V,A)),L):-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,exists(V,A1))],L).
sf_in_literal(forall(X in S,A),L):-
    !, sf_find([S],[S1],L1),
    sf_in_goal(A,L2),
    list_to_conj(A1,L2),
    append(L1,[forall(X in S1,A1)],L).
sf_in_literal(A,NewA):-   
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1],
    append(NewL,[B],NewA).
        
sf_in_hliteral(A,[B|NewL]):-                                      
    A =.. [Pname|Args],
    sf_find(Args,Args1,NewL),
    B =.. [Pname|Args1].
        
sf_find([],[],[]).
sf_find([Int|R],[Var|S],List):-
    is_sf(Int,X,G),!,
    extract_vars(G,Vars),
    remove_var(X,Vars,Finalvars),
    check_control_var1(Vars,Finalvars),
    sf_translate(Int,Var,L1,Finalvars),
    sf_find(R,S,L2),
    append(L1,L2,List).    
sf_find([A|R],[B|S],List):-
    nonvar(A),
    A =.. [Fname|Rest],
    Rest \== [],!,
    sf_find(Rest,Newrest,List1),
    B =.. [Fname|Newrest],
    sf_find(R,S,List2),
    append(List1,List2,List).
sf_find([A|R],[A|S],List):-
    sf_find(R,S,List).

check_control_var1(Vars,Finalvars) :-
    Vars == Finalvars, !,
    write('ERROR - Formula of a set former must'),
    write(' contain the set former control variable'), nl, 
    fail.
check_control_var1(_Vars,_Finalvars).

sf_translate(SF,Y,[Pred],Vars):-
    (SF={X:exists(_Var,Goal)},! ; SF={X : Goal}),
    length([_|Vars],N),    
    newpred(Aux,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),    % "setlogSF_"
    Aux=..[AuxName,Y|Vars],
    newpred(Aux1,N,[115, 101, 116, 108, 111, 103, 83, 70, 95]),   
    Aux1 =.. [Aux1Name,X|Vars],
    Pred = sf_call(Y,Aux1Name,AuxName,Vars),
    setassert((Aux1 :- Goal)),
    setassert((Aux :- X nin Y & Aux1)). 
        
is_sf(Int,X,Phi) :-
    nonvar(Int), Int = {SExpr}, 
    nonvar(SExpr), SExpr = (X : Phi),
    check_control_var2(X).

check_control_var2(X) :-
    nonvar(X), !,
    write('ERROR - Control variable in a set former'),
    write(' must be a variable term!'), nl,  
    fail.
check_control_var2(_X).
              

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%    R.U.Q. preprocessing  %%%%%%%%%%%           
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                      
ruq_in_clause((H :- B),(H :- NewB)) :-    
    ruq_in_goal(B,NewB,B,no),!.
ruq_in_clause(H,H).

ruq_in_goal(Goal,NewGoal) :-
    rewrite_goal(Goal,NewGoal).
%DBG%     write('***NEW GOAL:***'), write(NewGoal), nl.   % only for debugging

rewrite_goal(G,NewG) :-
    filter_on,!,
    normalize(G,G1),           
    ruq_in_goal(G1,G2,G1,infer_rules),    
    ruq_in_goal(G2,NewG,G2,fail_rules).    
rewrite_goal(G,NewG) :-
    ruq_in_goal(G,NewG,G,no).    

ruq_in_goal(A,A,_,_):-
    var(A),!.    
ruq_in_goal(A & B,GExt,G,RR):-
    !, ruq_in_goal(A,A1,G,RR), ruq_in_goal(B,B1,G,RR),
    conj_append(A1,B1,GExt).    
ruq_in_goal((A or B),((A1) or (B1)),_,RR):-
    !, ruq_in_goal(A,A1,A,RR), ruq_in_goal(B,B1,B,RR). 

ruq_in_goal(prolog_call(A),prolog_call(A),_,_):-!. 
ruq_in_goal(neg A,neg(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(naf A,naf(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(call(A),call(A1),_,no):-
    !, rewrite_goal(A,A1).
ruq_in_goal(call(A),call(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).
ruq_in_goal(call(A,C),call(A1,C),_,RR):-    
    !, ruq_in_goal(A,A1,A,RR).   
ruq_in_goal(solve(A),solve(A1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal((A)!,(A1)!,_,RR):-
    !, ruq_in_goal(A,A1,A,RR).    
ruq_in_goal(delay(A,G),delay(A1,G1),_,RR):-
    !, ruq_in_goal(A,A1,A,RR),
    ruq_in_goal(G,G1,G,RR).   
 
ruq_in_goal(forall(X in _S,_Y),_,_,_):- 
    nonvar(X), !, 
    write('ERROR - Control variable in a R.U.Q. must be a variable term!'), nl, 
    fail.
ruq_in_goal(forall(X in S,G),NewG,_,_):-
    !, extract_vars(G,V),
    remove_var(X,V,Vars),
    check_control_var_RUQ(V,Vars), 
    length(V,N),
    newpred(Gpred,N,[115, 101, 116, 108, 111, 103, 82, 85, 81, 95]),       %"setlogRUQ_"
    Gpred =.. [_,X|Vars],
    tmp_switch_ctxt(OldCtxt),
    ( G = exists(_Var,B),!,       
      setassert((Gpred :- B))     
     ;
      setassert((Gpred :- G)) ),  
    switch_ctxt(OldCtxt,_),
    functor(Gpred,F,N),
    NewG = ruq_call(S,F,Vars).

ruq_in_goal(true,true,_,_) :- !. 
ruq_in_goal(A,NewG,G,RR) :-      % try to call filtering rules
    RR \== no,
    user_def_rules(A,NewG,G,RR),!.
ruq_in_goal(A,A,_,_).
    %% N.B. no check for 'forall(X in {...,t[X],...})'
    %% add 'occur_check(X,S)' to enforce it

check_control_var_RUQ(Vars,Finalvars) :-
    Vars == Finalvars, !,
    write('ERROR - Formula of a R.U.Q. must'),
    write(' contain the R.U.Q. control variable'), nl, 
    fail.
check_control_var_RUQ(_Vars,_Finalvars).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% User-defined rewriting rules %%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load_rwrules_lib :-                           
    rw_rules(Lib),
    mk_file_name(Lib,FullName),
    (exists_file(FullName),!,consult(FullName) 
     ; 
     rw_rules(Filtering_rules_file),
     write('No filtering rules loaded (file '''), 
     write(Filtering_rules_file), write(''')'), nl).      

normalize(Goal,NewGoal) :-   
    ruq_in_goal(Goal,NewGoal1,Goal,replace_rules),    
    (Goal == NewGoal1,!,NewGoal=NewGoal1
    ;
     normalize(NewGoal1,NewGoal)
    ).   

user_def_rules(A,NewC,G,replace_rules) :- !,
    replace_rule(_RuleName,C,C_Conds,D,D_Conds,AddC),       
    check_atom(C,A,R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,[]),
    apply_equiv(R,AddC,NewC).                                 

user_def_rules(A,NewC,G,infer_rules) :- !,
    inference_rule(RuleName,C,C_Conds,D,D_Conds,E,AddC),  
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_firules(RuleName),
    conj_append(AddC,A,NewC). 
 
user_def_rules(A,NewC,G,fail_rules) :- !,
    fail_rule(RuleName,C,C_Conds,D,D_Conds,E),   
    check_atom(C,A,_R),
    list_call(C_Conds),
    conj_member_strong(D,D_Conds,G,E),
    trace_ffrules(RuleName),
    conj_append((a = b),A,NewC).

conj_member_strong([],_,_,_):- !.
conj_member_strong([T],D_Conds,G,E):-    
    conj_member_strong1(T,D_Conds,G,E),
    list_call(D_Conds),!.
conj_member_strong([T|R],D_Conds,G,E):- 
    R \== [],
    conj_member_strong1(T,D_Conds,G,E),
    conj_member_strong(R,D_Conds,G,E),!.

conj_member_strong1(T,_D_Conds,(A & _Cj),E) :- 
    check_atom(T,A,_R),
    list_ex(E,T). 
conj_member_strong1(T,D_Conds,(_Y & RCj),E):- 
    conj_member_strong1(T,D_Conds,RCj,E).
 
check_atom(T,A,no) :-    
    A=T,!.
check_atom(T,A,RuleId) :-  
    equiv_rule(RuleId,T,T1),!,  
    A=T1.

list_call([]) :- !.
list_call([G|R]) :-
    call(G), 
    list_call(R).

list_ex([],_).
list_ex([A|R],T) :-
    T \== A, list_ex(R,T).   % to exclude identical atoms

apply_equiv(no,A,A).
apply_equiv(R,A & B,A1 & B1) :-
    equiv_rule(R,A,A1),!,
    apply_equiv(R,B,B1).
apply_equiv(R,A & B,A & B1) :- !,
    apply_equiv(R,B,B1).
apply_equiv(R,A,A1) :-
    equiv_rule(R,A,A1),!.
apply_equiv(_R,A,A).
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% New predicate generation

newpred_counter(0).

newpred(P,A,T):-
    retract(newpred_counter(Y)), !,
    Z is Y + 1,
    assert(setlog:newpred_counter(Z)),
    name(Y,Ylist),
    append(T,Ylist,Plist),
    name(Pred,Plist),
    mklist(L,A),
    P =.. [Pred|L].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_goal/2 
% Transform a goal from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_goal(Goal_external,Goal_internal) :-
       sf_in_goal(Goal_external,Goal_ruqL),
       list_to_conj(Goal_ruq,Goal_ruqL),
       preproc_goal(Goal_ruq,Goal),!,
       ruq_in_goal(Goal,Goal_internal).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% transform_clause/2 
% Transform a clause from the external representation to the
% internal representation, by rewriting intensional sets,
% RUQs, set and bag terms

transform_clause(Clause_external,Clause_internal) :-
       sf_in_clause(Clause_external,ExplClause),
       preproc_clause(ExplClause,ExtClause),
       ruq_in_clause(ExtClause,Clause_internal).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Postprocessing 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%% Set (multiset) postprocessor:  
%%%%%%%%%%%%% from 'with' ('mwith') to {...} (*({...})) notation  

postproc(X,X):- 
        var(X),!.      
postproc(X,X):-
        atomic(X),!.
postproc(X,Y):-
        nonvar(X), X = _ with _,!,
        norep_in_set(X,X1),
        with_postproc(X1,Y). 
postproc(X,Y):-
        nonvar(X), X = _ mwith _,!,
        mwith_postproc(X,Z),
        mwith_out(Z,Y).
postproc(X,Z):-
        nonvar(X), 
        =..(X,[F|ListX]),
        postproc_all(ListX,ListZ),
        =..(Z,[F|ListZ]).

postproc_all([],[]).
postproc_all([A|L1],[B|L2]):-
        postproc(A,B),
        postproc_all(L1,L2).
      
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% set postprocessing 

with_postproc(A,A) :- 
        var(A),!.
with_postproc(A,B):- 
        nonvar(A),A = cp(_,_),!,
        postproc_cp(A,B).
with_postproc(K,KExt):- 
        is_ker(K), !,
        postproc(K,KExt).
with_postproc(A,{}(B)):-
        tail(A,TA), 
        nonvar(TA),TA = cp(Y1,Y2),
        ground(Y1),ground(Y2),!,
        g_cp(Y1,Y2,CP),
        replace_tail(A,CP,Awith),  
        norep_in_set(Awith,AwithRid),      
        postproc_list(AwithRid,B).
with_postproc(A,{}(B)):-
        postproc_list(A,B).

postproc_list(X with A1,(A2 / X)) :-  
        var(X),!,postproc(A1,A2).
postproc_list({} with A1,A2):- !,
        postproc(A1,A2).
postproc_list(K with A1,(A2 / KExt)) :-  
        is_ker(K),!, 
        postproc(K,KExt), postproc(A1,A2).
postproc_list(B1 with A1,(A2,B2)):-
        postproc(A1,A2),postproc_list(B1,B2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% bag postprocessing

mwith_out({}(X),*({}(X))).

mwith_postproc(A,A) :- var(A),!.
mwith_postproc({},{}):- !.
mwith_postproc(A,{}(B)):-
    bag_postproc_list(A,B).

%bag_postproc_list(X mwith A1,(A2 \ X)) :-   
bag_postproc_list(X mwith A1,(A2 / X)) :-   
    var(X),!,postproc(A1,A2).
bag_postproc_list({} mwith A, A):-
    var(A),!.
bag_postproc_list({} mwith A1,A2):-!,
    postproc(A1,A2).
bag_postproc_list(B1 mwith A1,(A2,B2)):-
    postproc(A1,A2), bag_postproc_list(B1,B2).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%     Auxiliary predicates     %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%               
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Exported predicates:
%
%             list_to_conj/2,
%             conj_append/3,
%             list_term/1,
%             mklist/2,
%%             member/2,
%             memberrest/3,
%             memberall/4,
%             member_strong/2,
%%             append/3,
%             listunion/3,
%             subset_strong/2,
%             norep_in_list/2,
%             remove_list/3,
%             list_to_set/3,
%             set_term/1,
%             tail/2,
%             replace_tail/3,
%             split/3,
%             bounded/1
%             set_length/2,
%             set_member/3,
%             is_empty/1,
%             int_term/1,
%             is_int/3,
%             int_to_set/2,
%             int_length/2,
%             norep_in_set/2,
%             bag_term/1,
%             bag_tail/2,
%             de_tail/2,
%             empty_aggr/1,
%             aggr_comps/3,
%             alldist/1,
%             extract_vars/2,
%             remove_var/3,
%             samevar/2,
%             occurs/2,
%             occur_check/2
%             chvar/6,
%             simple_integer_expr/1,
%             simple_arithm_expr/1,
%             integer_expr/1,
%             arithm_expr/1


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     List manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_term(T) :- 
        nonvar(T), 
        (T=[],! ; T=[_ | _]).  

mklist([],0):- !.
mklist([_|R],N):-
        M is N-1,
        mklist(R,M).

%member(X,[X|_R]).
%member(X,[_|R]):-member(X,R).

memberrest(X,[X|R],R) :- !.
memberrest(X,[_|R],L):-
        memberrest(X,R,L).

memberall(A,B,[A|_R],[B|_S]).
memberall(A,B,[_|R],[_|S]):- 
        memberall(A,B,R,S).

%append([],L,L).                                     
%append([X|L1],L2,[X|L3]):-
%       append(L1,L2,L3).

member_strong(A,[B|_R]):- 
         A == B, !.
member_strong(A,[_|R]):- 
        member_strong(A,R).

notin(_,[]).       % not member strong
notin(A,[B|R]):-
        A \== B, notin(A,R).

listunion([],L,L).   
listunion([A|R],X,[A|S]):- 
        notin(A,X),!,
        listunion(R,X,S).
listunion([_A|R],X,S):-
        listunion(R,X,S).

subset_strong([],_L):-!.
subset_strong([X|L1],L2) :-
        member_strong(X,L2),
        subset_strong(L1,L2).

norep_in_list([],[]):-!.
norep_in_list([A|R],S):-
        member_strong(A,R),!,
        norep_in_list(R,S).
norep_in_list([A|R],[A|S]):-
        norep_in_list(R,S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Set manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

set_term(T) :- 
       nonvar(T), 
       (T={},! ; T=_ with _).    

cp_term(T) :-
       nonvar(T), T = cp(_,_).

ris_term(T) :-  
       nonvar(T), T = ris(_,_,_,_,_).

is_set(S) :- set_term(S),!.  
is_set(S) :- is_int(S),!.  
is_set(S) :- is_ris(S,_),!.   
is_set(S) :- cp_term(S). 

is_cp(T,A,B) :-    
        nonvar(T), T = cp(A,B),
        (set_term(A),! ; var(A)),  
        (set_term(B),! ; var(B)).        

tail(R,R) :- var(R),!.                   %attn. tail({},T), tail(int(a,b),T), tail(cp(...),T) --> false
tail(R with _,R) :- var(R),!.
tail(R,RR) :- 
    is_ris(R,ris(_ in D,_,_,_,_)),!,     %ris: returns the tail of the RIS domain   
    tail(D,RR).
tail({} with _,{}) :- !.
tail(int(_A,_B) with _,{}) :- !.
tail(R  with _,RR) :- 
    is_ris(R,ris(_ in D,_,_,_,_)),!,     
    (tail(D,RR),! ; RR={}).
tail(R with _,R) :-                  
    R = cp(_,_),!.
tail(R with _,T) :- !,
    tail(R,T). 

tail2(R,R) :- var(R),!.
tail2(R with _,R) :- var(R),!.
tail2({} with _,{}) :- !.
tail2(int(_A,_B) with _,{}) :- !.
tail2(R with _,RR) :- 
    is_ris(R,RR),!.                      %ris: returns the RIS itself
tail2(R with _,R) :- 
    R = cp(_,_),!.                       %cp: returns the CP itself
tail2(R with _,T) :- !,
    tail2(R,T).

bounded(T) :- 
       var(T),!,fail.
bounded({}) :- !.
bounded(R with _) :- 
       bounded(R).

replace_tail(R,N,N) :- var(R),!.
replace_tail({},N,N) :- !.
replace_tail(R,N,ris(X in Dnew,V,F,P,PP)) :- 
       is_ris(R,ris(X in D,V,F,P,PP)),!, 
       replace_tail(D,N,Dnew).
replace_tail(R,N,N) :-
       R = cp(_,_),!.
replace_tail(R1 with X,N,R2 with X) :- 
       replace_tail(R1,N,R2).

%%%% split(S,N,L) true if S is a set term of the form N with tn with ... with t1
%%%% (n >= 0) and L is the list [t1,...,tn]
split(N,N,[]):-
       var(N),!.
split(S with T, N, [T|R]):-
       split(S,N,R).

norep_in_set(X,X):- var(X),!.
norep_in_set(K,K) :- is_ker(K), !.
norep_in_set(R with A,S):-
       set_member_strong(A,R),!,
       norep_in_set(R,S).
norep_in_set(R with A,S with A):-
       norep_in_set(R,S).        

set_length(S,N) :-
       set_length(S,0,N).
set_length(X,_,_) :-
       var(X), !, fail.
set_length(S,N,N) :-
       is_empty(S), !.
set_length(int(A,B),N,M) :- !,
       M is N + (B - A) + 1.
set_length(R with _X,N,M):-
       N1 is N + 1,
       set_length(R,N1,M).

set_member(X,_R with Y,C):-
       sunify(X,Y,C).
set_member(X,R with _Y,C):-
       set_member(X,R,C).

set_member_strong(A,B):-
       nonvar(B),
       B = _ with X, 
       A == X,!.
set_member_strong(A,B):-
       nonvar(B), 
       B = Y with _,
       set_member_strong(A,Y).

%set_member_rest(_X,R,_C,_R):-    % not used
%       var(R), !, fail.
%set_member_rest(X,R with Y,C,R):-
%       sunify(X,Y,C).
%set_member_rest(X,R with Y,C,RR with Y):-
%       set_member_rest(X,R,C,RR).

list_to_set(L,S,[]) :-            % list_to_set(+list,?set,-constraint)
       var(S),!, 
       mk_set(L,S).             
list_to_set(L,S,C) :-            
       mk_test_set(L,S,C).   
          
mk_set([],{}) :- !.             
mk_set([X|L],R with X) :-
       mk_set(L,R).

mk_test_set([],{},[]) :- !.
mk_test_set([X|L],S,Cout) :-
       sunify(S,R with X,C1),
       list_to_set(L,R,C2),
       append(C1,C2,Cout).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Interval manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int_term(T) :-                      %GFR - non usato
       nonvar(T), T = int(_,_).

is_int(T) :-                         % is_int(I) is true if I is a term that denotes an interval
       nonvar(T), 
       T=int(A,B), 
       (var(A),! ; integer(A)),
       (var(B),! ; integer(B)). 

closed_intv(T,A,B) :-                   % closed_intv(I,A,B) is true if I is a term that 
       nonvar(T),                    % denotes the closed interval int(A,B)
       T=int(A,B),                   
       integer(A), integer(B),!.     

open_intv(S) :-
    nonvar(S), S = int(A,B),
    (var(A),! ; var(B)).

nonopen_intv(S) :-
    open_intv(S),!,  
    write('ERROR - Interval bounds are not sufficiently instantiated'),nl,
    fail.
nonopen_intv(_S). 

int_to_set(int(A,A),{} with A) :- !. % int_to_set(+I,?S) is true if S denotes the set
int_to_set(int(A,B),S with A) :-     % of all elements of the interval I 
       A < B,
       A1 is A + 1,
       int_to_set(int(A1,B),S).

int_to_set(int(A,A),R with A,R) :- !.% int_to_set(+I,?S) is true if S contains the set
int_to_set(int(A,B),S with A,R) :-   % of all elements of the interval I 
       A < B,
       A1 is A + 1,
       int_to_set(int(A1,B),S,R).

int_length(int(A,B),L) :-
       N is B - A + 1,
      (N < 0,!, L = 0           
       ;
       L = N
       ).       


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%     Bag manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bag_term(T) :- 
       nonvar(T), 
       (T={},! ; T=_ mwith _).  

bag_tail(R mwith _ ,R) :- var(R),!.
bag_tail({} mwith _ ,{}) :- !.
bag_tail(R mwith _ ,T) :- 
       bag_tail(R,T).

de_tail(R,{}) :- var(R),!.
de_tail({},{}) :- !.
de_tail(R mwith S,K mwith S) :- 
       de_tail(R,K).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%   List/Set/Bag/Interval manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

empty_aggr(A) :-                  % empty set/multiset/list
       (is_empty(A),! ; A == []).
                                  
is_empty({}) :- !.                % empty set (requires nonvar(S))
is_empty(S) :-             
       closed_intv(S,L,H),
       L > H,!.
is_empty(S) :-             
       is_ris(S,ris(_ in Dom,_,_,_,_)),
       nonvar(Dom), is_empty(Dom),!.
is_empty(cp(A,B)) :-  
       (nonvar(A),is_empty(A),! ; nonvar(B),is_empty(B)).   

nonvar_is_empty(S) :-
       nonvar(S), is_empty(S).

var_or_empty(T) :- 
        var_st(T),!.         
var_or_empty(T) :-
        is_empty(T).

aggr_comps(R with X,X,R) :- !.    % set
aggr_comps(R mwith X,X,R) :- !.   % bag
aggr_comps([X | R],X,R).          % list
   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Arithmetic expressions manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simple_integer_expr(E) :- 
      (var(E),! ; integer(E)).

simple_arithm_expr(E) :-
      (var(E),! ; number(E)).

arithm_expr(E) :-        % true if E is a ground arithmetic expression       
      on_exception(_Error,_X is E,(write('Problem in arithmetic expression'),nl,fail)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Variable manipulation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

samevar(X,Y) :- 
      var(X), var(Y), X == Y.

samevar(X,Y,Z) :-           %true if X is identical to either Y or Z
      (samevar(X,Y),! ; samevar(X,Z)).

samevar3(X,Y,Z) :-          %true if either X==Y or X==Z or Y==Z
      (samevar(X,Y),! ; samevar(X,Z),! ; samevar(Y,Z)).

one_var(X,Y) :-                        
      (var(X),! ;  var(Y)).

chvar(L1,[X|L1],X,L2,[Y|L2],Y):-
    var(X), notin(X,L1), !.
chvar(L1,L1,X,L2,L2,Y):-
    var(X), find_corr(X,Y,L1,L2),!.
chvar(L1,L1new,(H :- B),L2,L2new,(H1 :- B1)):-
    !, chvar(L1,L1a,H,L2,L2a,H1),
    chvar(L1a,L1new,B,L2a,L2new,B1).
chvar(L1,L1new,(B1 & B2),L2,L2new,(B1a & B2a)):-
    !, chvar(L1,L1a,B1,L2,L2a,B1a),
    chvar(L1a,L1new,B2,L2a,L2new,B2a).       
chvar(L1,L1,F,L2,L2,F):-
    atomic(F),!.
chvar(L1,L1new,F,L2,L2new,F1):-
    F =.. [Fname|Args],
    chvar_all(L1,L1new,Args,L2,L2new,Brgs),
    F1 =.. [Fname|Brgs].
    
chvar_all(L1,L1,[],L2,L2,[]).
chvar_all(L1,L1b,[A|R],L2,L2b,[B|S]):-
    chvar(L1,L1a,A,L2,L2a,B),
    chvar_all(L1a,L1b,R,L2a,L2b,S).
        
find_corr(X,Y,[A|_R],[Y|_S]):-
    X == A,!.    
find_corr(X,Y,[_|R],[_|S]):-
    find_corr(X,Y,R,S).   

occurs(X,Y):-   % occur(X,T): true if variable X occurs in term T
       var(Y),samevar(X,Y),!.
occurs(_X,Y):-   % occur(X,T): false if T is a RIS 
       nonvar(Y),is_ris(Y,_),!,fail.
occurs(X,Y):-
       nonvar(Y),
       Y =.. [_|R],
       occur_list(X,R).
occur_list(_X,[]):-!,fail.
occur_list(X,[A|_R]):-
       occurs(X,A),!.
occur_list(X,[_|R]):-
       occur_list(X,R).

occur_check(X,Y):-    % occur_check(X,T): true if variable X DOES NOT occur in term T
      var(Y),!,X \== Y.
occur_check(X,Y):-
      Y =.. [_|R],
      occur_check_list(X,R).
occur_check_list(_X,[]):-!.
occur_check_list(X,[A|R]):-
      occur_check(X,A),
      occur_check_list(X,R).

extract_vars(A,[A]):-
    var(A),!.                 
extract_vars(exists(V,B),Vars):-
    var(V),!,
    extract_vars(B,List),
    remove_var(V,List,Vars). 
extract_vars(exists(V,B),Vars):-
    !,extract_vars(B,List),
    remove_list(V,List,Vars).
extract_vars(forall(X in Y,B),Vars):-
    !, extract_vars(Y,L1),
    extract_vars(B,L2),
    listunion(L1,L2,L),
    remove_var(X,L,Vars).    
extract_vars(Int,Vars):-
    is_sf(Int,X,G),!,
    extract_vars(G,Vars1),
    remove_var(X,Vars1,Vars).   
extract_vars(P,Vars):-
    functor(P,_,A),
    !, findallvars(P,A,Vars).
    
findallvars(_P,0,[]):- !.   
findallvars(P,A,Vars):-
    arg(A,P,Arg),
    extract_vars(Arg,L1),
    B is A-1,
    findallvars(P,B,L2),
    listunion(L1,L2,Vars).
        
remove_var(_,[],[]).
remove_var(X,[Y|L],S):-
    X == Y,!,remove_var(X,L,S).
remove_var(X,[Y|L],[Y|S]):-
    remove_var(X,L,S).  
        
remove_list([],L,L).
remove_list([X|R],Vars,Finalvars):-
    remove_var(X,Vars,S),
    remove_list(R,S,Finalvars).   

alldist([]).
alldist([A|R]):-
    var(A), not_in_vars(A,R),
    alldist(R).
    
not_in_vars(_X,[]).
not_in_vars(X,[A|R]):-
    X \== A, not_in_vars(X,R).
   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%  Conjunction manipulation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_to_conj(A & B,[A|R]):-
    !,list_to_conj(B,R).
list_to_conj(true,[]):-!.
list_to_conj(A,[A]).

conj_append(Cj1,Cj2,(Cj1 & Cj2)) :-    
        var(Cj1),!.
conj_append(true,Cj2,Cj2) :- !.
conj_append((X & Cj1),Cj2,(X & Cj3)) :- !,
        conj_append(Cj1,Cj2,Cj3).
conj_append(X,Cj2,(X & Cj2)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%% Configuration parameters %%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

path('').                         % the default path (= the working director '.')  

rw_rules('setlog_rules.pl').      % the default library of filtering rules    

strategy(cfirst).                 % the default atom selection strategy (= "constraint first") 
%strategy(cfirst(UserPredList)).  % UserPredList is a list of user defined predicates to be 
                                  % executed just after constraint solution (before all other
                                  % user-defined predicates)
                                  % e.g., strategy(cfirst([ttf_list(_),ttf_nat(_),ttf_int(_),ttf_btype(_)])).       

fd_labeling_strategy([]).         %the default labeling strategy for the clp(FD) solver
%fd_labeling_strategy([ff]).      
%fd_labeling_strategy([bisect]).
%fd_labeling_strategy([ff,down,enum]).

default_int_solver(clpfd).        % the default solver for integer expressions  (clpfd | clpq) 
%default_int_solver(clpq).    
   
%type_constraints_to_be_shown([]).     %none  
%type_constraints_to_be_shown([set(_),integer(_),pfun(_),nset(_),ninteger(_),bag(_),list(_)]).      
type_constraints_to_be_shown([set(_),bag(_),list(_),integer(_),rel(_),pfun(_),pair(_),   %all
                              nset(_),ninteger(_),npfun(_),npair(_)]).  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Starting the {log} interpreter %%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- setlog(consult_lib,_).

:- load_rwrules_lib.     % load the library of filtering rules  

:- nl,write('Use ?- setlog_help to get help information about {log}'),nl,nl.

    

