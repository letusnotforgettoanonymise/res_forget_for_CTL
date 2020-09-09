

:- use_module(wff2cnf).



%:- op(300,fx,@). /*global*/
%:- op(400,fx,$). /*exist*/
%：- op(900,fx, *). /*next*/

:- op(300,fx,@). /*global*/
:- op(300,fx,*). /*next*/
:- op(300,fx,?). /*future*/
:- op(400,xfy,$). /*until*/
:- op(1000,fx, ^). /*exist*/
:- op(1000,fx,~). /*forall*/

:- op(500,fx,-).
%:- op(500,fx,~).
:- op(780,xfy,&).
:- op(790,xfy,\/).%/
:- op(800,xfy,->).
:- op(800,xfy,<->).


:- dynamic(prop/1).

prop(start).

%transform--------------------------------------------start-------------------------------------------
%transform a CTL formula into set of SNF_{CTL}^g clauses

gain_prop([]).
gain_prop([C|L1]) :- judgeType(C, Type),
	( Type = t, !, C = true_clause(T, H), append(T, H, L), assert_list(L);
		(Type = g, !, C= global_next_clause(T,H), append(T,H, L), assert_list(L);
			(Type = e, !, C = exist_next_clause(T, H, I), append(T,H, L), assert_list(L);
				(Type = st, !, C = start_clause(T, H), append(T, H, L), assert_list(L))
			)
		)
	),
	gain_prop(L1).

assert_list([]).
assert_list([H|T]) :- (H= -P, assert(prop(P)); assert(H)), assert_list(T).


%transform ---------------------------------------------------end-------------------------------------





%resolution ----------------------------------------------------------start--------------------
%step rules
equall(P, P) :- prop(P), !.
equall(-P, -P) :- prop(P), !.
equall(-(-P), P) :- prop(P), !.



unionC(C1, C2, P, X) :- equall(P, F1), delete(C1, F1, X1), equall(-P, F2), delete(C2, F2, X2), append(X1, X2, X3), sort(X3, X).
union(C1,C2,R) :- append(C1,C2,R1), sort(R1, R).

%SRES1
res_SRES1(C1,C2,P,R) :- C1=global_next_clause(T1, H1), C2=global_next_clause(T2, H2),
	union(T1,T2,T), unionC(H1,H2,P,H), R=global_next_clause(T,H).
	
%SRES2
res_SRES2(C1,C2,P,R) :- C1=exist_next_clause(T1, H1,I), C2=global_next_clause(T2, H2),
	union(T1,T2,T), unionC(H1,H2,P,H), R=exist_next_clause(T,H,I).
	
%SRES3
res_SRES3(C1,C2,P,R) :- C1=exist_next_clause(T1, H1,I), C2=exist_next_clause(T2, H2, I),
	union(T1,T2,T), unionC(H1,H2,P,H), R=exist_next_clause(T,H,I).
	
%SRES4
res_SRES4(C1,C2,P,R) :- C1=start_clause(T1, H1), C2=start_clause(T2, H2),
	unionC(H1,H2,P,H), R=start_clause(T1,H).
	
%SRES5
res_SRES5(C1,C2,P,R) :- C1=true_clause(T1, H1), C2=start_clause(T2, H2),
	unionC(H1,H2,P,H), R=start_clause(T2,H).
	
%SRES6
res_SRES6(C1,C2,P,R) :- C1=true_clause(T1, H1), C2=global_next_clause(T2, H2),
	unionC(H1,H2,P,H), R=global_next_clause(T2,H).
	
%SRES6
res_SRES7(C1,C2,P,R) :- C1=true_clause(T1, H1), C2=exist_next_clause(T2, H2, I),
	unionC(H1,H2,P,H), R=exist_next_clause(T2,H,I).
	
%SRES5
res_SRES8(C1,C2,P,R) :- C1=true_clause(T1, H1), C2=true_clause(T2, H2),
	unionC(H1,H2,P,H), R=true_clause(T2,H).

%resolution--------------------------------------------end-------------------------------------


%pos(P,C)-------------------------------------------start-------------------------------------------
%deciding p (that should be resolved) appearing in C positively.
posC(P, C) :- C = exist_next_clause(_, H, _), member(P, H).
posC(P, C) :- C = global_next_clause(_, H), member(P, H).
posC(P, C) :- C = true_clause(_, H), member(P,H).
posC(P, C) :- C = start_clause(_, H), member(P,H).
posC(P, C) :- C = global_future_clause(_, H), member(P, H).
posC(P, C) :- C = exist_future_clause(_, H, _), member(P, H).
%pos-------------------------------------------end-------------------------------------------


%neg-------------------------------------------start-------------------------------------------
%deciding p (that should be resolved) appearing in C negatively.
negC(P, C) :- C = exist_next_clause(_, H, _), F=(-P), member(F, H).
negC(P, C) :- C = global_next_clause(_, H), F=(-P), member(F, H).
negC(P, C) :- C = true_clause(_, H), F=(-P), member(F,H).
negC(P, C) :- C = start_clause(_, H), F=(-P), member(F,H).
negC(P, C) :- C = global_future_clause(_, H), F=(-P), member(F, H).
negC(P, C) :- C = exist_future_clause(_, H, _), F=(-P), member(F, H).
%neg-------------------------------------------end-------------------------------------------


%all_PosC(L, P, L1)-----------------------------------------start-------------------------------------------
%find all the clauses C in L that P appearing in C positively
all_PosC([], _, []).
all_PosC([H|T], P, L1) :- all_PosC(T, P, Tem), (posC(P, H), append([H], Tem, X), L1=X; L1=Tem).
%all_PosC(L, P, R) :- findall(, posC(P, 
%all_PosC-------------------------------end-------------------------------------


%all_NegC(L, P, L1)-----------------------------------------start-------------------------------------------
%find all the clauses C in L that P appearing in C negatively
all_NegC([], _, []).
all_NegC([H|T], P, L1) :- all_NegC(T, P, Tem), (negC(P, H), append([H], Tem, X), L1=X; L1=Tem).
%all_PosC-------------------------------end-------------------------------------


%judgeType(C, Type)-------------------------------start-------------------------------------------
%Judging the type of a Clause C.
judgeType(C, Type) :- C = exist_next_clause(_, _, _), Type = e.
judgeType(C, Type) :- C = global_next_clause(_, _), Type = g.
judgeType(C, Type) :- C = true_clause(_, _), Type = t.
judgeType(C, Type) :- C = start_clause(_, _), Type = st. 
judgeType(C, Type) :- C = global_future_clause(_, _), Type = gf.
judgeType(C, Type) :- C = exist_future_clause(_, _, _), Type = ef.

%judgeType------------------------------------------end------------------------------------------


/*%findType(L, T, C)-------------------------start-------------------------------------------
%Find a Clause C that type is T from L.
findType([], _, C, []) :- C=n, !.
findType([H|T], Type, C, L) :- (judgeType(H, Type), !, C=H, L = T; findType(T, Type, C, L)).

%findType-------------------------------------end------------------------------------------*/


%resolution(Lp, Ln, P, L)----------------------------start-------------------------------------------
%do all the possible step-resolutions on P. （得到的结果也都包含了Lp和Ln）
resolution([], Ln, P, Ln).
resolution(L, [], _, L).
resolution([H|Lp], Ln, P, L) :- resolution_list(H, Ln, P, L1), resolution(Lp, Ln, P, L2), append(L1, L2, R), sort(R, L).

resolution_list(C, [], _, [C]).
resolution_list(C, [H|Ln], P, L1) :- judgeType(C, Type1), judgeType(H, Type2), 
	(Type1 = g, !, (Type2=g, !, res_SRES1(C, H, P, C1); (Type2 = e, !, res_SRES2(H, C, -P, C1); (Type2=t, !, res_SRES6(H, C, -P, C1); C1=[]))); 
		(Type1= e, !, (Type2=g, !, res_SRES2(C, H, P, C1); (Type2 = e, !, res_SRES2(C, H, P, C1); (Type2=t, !, res_SRES7(H, C, -P, C1); C1=[])));
			(Type1 = t, !, (Type2=st, !, res_SRES5(C, H, P, C1); (Type2=g, !, res_SRES6(C, H, P, C1); (Type2=e, !, res_SRES7(C,H, P, C1); (Type2=t, !, res_SRES8(C,H,P, C1); C1=[]))));
				(Type1 =st, !, (Type2=st, !, res_SRES4(C,H, P, C1); (Type2=t, !, res_SRES5(H, C, -P, C1); C1=[])); C1 =[])
			)
		)
	),
	resolution_list(C, Ln, P, L2),
	(C1 =[], L1 =L2;
	append([C1], L2, L1)).
	
	

repeat_resolution([],_, []).
repeat_resolution(L, P, Res) :- sort(L, L1), all_PosC(L, P, Lp), all_NegC(L, P, Ln), resolution(Lp, Ln, P, R1), 
	( member(true_clause([true],[- z]), R1), Res=false;
		(L1 = R1, Res = R1;
			repeat_resolution(R1, P, Res)
		)%, write("\n"), write("Res="), write(Res).
	).


%findall(X, (member(X, L1), inCst(X, Q)), L2)

%原来为repeat_resolution(L, P, Res) :- sort(L, L1), all_PosC(L, P, Lp), all_NegC(L, P, Ln), resolution(Lp, Ln, P, R1), 
%		(L1 = R1, Res = R1;
%			repeat_resolution(R1, P, Res)
%		).%, write("\n"), write("Res="), write(Res).


step_resolution(L, [], L).
step_resolution([], _, []).
step_resolution(L, V, R) :- appearing_list(L, V, L1), 
	step_resolution_list(L1, V, Rf),  
	(Rf=false, !, R=false;
		((Rf =L, R1 = Rf; step_resolution(Rf, V, R1)),
			( R1 = false, R = false; append(L, R1, X1), sort(X1, R))
		)
	).
	/*(Rf =L, R1 = Rf; step_resolution(Rf, V, R1)),
	append(L, R1, X1), sort(X1, R).*/
	%trans(X, Y1), tranI2CTL_list(Y1, R), 
	%tranSt2CTL(Y2, Y3), 
	%elim(Y2, V, Y4), 
	%sort(Y2, R).
	%, snfL2CTLF(Y5, R).


step_resolution_list([], _, []).
step_resolution_list(L, [], L).
step_resolution_list(L, [P|T], R) :- appearing(L, P, L1), %write("\nl"), write("L1="), write(L1),
	repeat_resolution(L1, P, Res), 
	( Res=false, !, R = false; 
		(member(start_clause([start],[]), Res), !, R =false;
			(member(true_clause([true], []), Res), !, R=false;
				(
					append(L, Res, Res1),  %write("\nl"), write("Res1="), write(Res1),
					sort(Res1, Y), %write("\nl"), write("Y="), write(Y),
					step_resolution_list(Y, T, Res2), %write("\nl"), write("Res2="), write(Res2),
					(Res2=false, R=false; 
						append(Y, Res2, X), %write("\nl"), write("X="), write(X),
						sort(X, R), write("\nl"), write("R="), write(R)
					)
				)
			)
		)
	).
	/* append(L, Res, Res1),  write("\nl"), write("Res1="), write(Res1),
	sort(Res1, Y), write("\nl"), write("Y="), write(Y),
	step_resolution_list(Y, T, Res2), write("\nl"), write("Res2="), write(Res2),
	append(Y, Res2, X), write("\nl"), write("X="), write(X),
	sort(X, R), write("\nl"), write("R="), write(R).*/
	%trans(Res, Res1),
	%elm(Res1, R).
	
%找出L中有原子P出现的clause。
appearing([], _, []).
appearing([H|L], P, R) :- (posC(P, H), H1 = 1; (negC(P, H), H1=1; H1 =[])),
	appearing(L, P, L1),
	(H1 =[], R = L1; append([H], L1, R)).


%找出L中有V中元素出现的clause。
appearing_list([], _, []).
appearing_list(L, [], L).
appearing_list(L, [P|V], R) :- appearing(L, P, R1), appearing_list(L, V, R2), append(R1, R2, R3), sort(R3, R).
%resolution--------------------------------------------end------------------------------------------




%ctlForget(L, V, R) ------------------------------------start-----------------------------------------------
ctlForget(F, V, R) :- tran2SNF(L, 0, 0, V1, R), tran2SNFCl(R, L), append(V, V1, V2), appearing_list(L, V2, L1), split2ST(L1, SL, TL, W, 0),
	ctlForget_list(SL, TL, W,V2, L2),
	append(L2, L, L3), sort(L3, R).
	
split2ST([],[],[],[], N).
split2ST([H|L], SL, TL, W, N) :- judgeType(H, Type),
	(Type = gf, H1 =H, N1 is N +1;
		(Type = ef, H1 = H, N1 is N +1; H1 = [], N1 is N
		)
	), split2ST(L, SL1, TL1, W1, N1),
	(H1 =[], TL= TL1, append([H], SL1, SL), X=[], W = W1; 
		string_concat('w', N, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), SL=SL1, append([H], TL1, TL), append([Y1], W1, W)
	). 
	
	
	
ctlForget_list([], [],_,_, []).
ctlForget_list(SL, TL, _,[], R) :- append(SL, TL, R).
ctlForget_list([], TL, _,_, TL).
ctlForget_list(SL, [], _,V, R) :- step_resolution(SL, V, R).
ctlForget_list(SL, TL, L, V, R) :- step_resolution(SL, V, R1),  write("\n R1==="), write(R1), trace,%L是对应的Q-sometimes子句需要引入的新原子的集合，一个Q-sometimes子句对应一个新变量
	(R1 = false, R = false;
		temp_resolution(TL, L, R1, V, R2, TL1, W), %W表示已经被引入了的变量的集合（ERES1或ERES2成功）
		(TL = TL1, append(R1, TL, R); %or R2 =[]
			(append(R1, R2, R3), write("\n R3@@@@"), write(R3), append(V, W, V1), setminus(W, L, W1), ctlForget_list(R3, TL1, W1, V1, R)) 
		)
	).
	/*temp_resolution(TL, L, R1, V, R2, TL1, W), 
	(TL = TL1, append(R1, TL, R); %or R2 =[]
		(append(R1, R2, R3), write("\n R3@@@@"), write(R3), append(V, W, V1), setminus(W, L, W1), ctlForget_list(R3, TL1, W1, V1, R)) 
	).*/
	
setminus([], L, L).
setminus([H|T], L, L1) :- elimElement(H, L,L2), setminus(T, L2, L1).
	
temp_resolution([], _,_,_,[],[],[]).
temp_resolution(TL, _, [],_, [], TL, []).
temp_resolution(TL, _, _, [], [], TL, []).
temp_resolution([H|TL], [X|L], L1, [Y|V], R, TL1, W) :- temp_resolution_list(H, L1, [Y|V], R1,X), 
	temp_resolution(TL, L, L1, [Y|V], R2, TL2, W1),
	(R1 = [], append([H], TL2, TL1), W = W1, R=R2; TL1= TL2,  append([X], W1, W), append(R1, R2, R)).


temp_resolution_list(_, _, [], [], _).
temp_resolution_list(H, L, [Y|V], R,W):- judgeType(H, Type), 
	(Type = gf, (posC(Y, H), fA(H, L, - Y, R,W); (negC(Y, H),fA(H, L, Y, R,W); temp_resolution_list(H, L, V, R,W)));
		(Type = ef, (posC(Y, H), fE(H, L, - Y, R,W); (negC(Y, H),fE(H, L, Y, R,W); temp_resolution_list(H, L, V, R,W))))
	).
	
fA(C, L, Y, R,W) :- find_Asometime_loop(L, Y, F),  C= global_future_clause(Q, H),
	(F = false, R = []; snfres(F, Y, Q, R, W)).
	
snfres(true, Y,Q, R, W) :- equall(- Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), 
	R = [global_next_clause([W],[- Y]), true_clause([true], T2), true_clause([true], T3), global_next_clause([W], [P, W])].
snfres(F, Y, Q, R, W) :-  equall(- Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), cirRes(W, P, T1, F, R1),
	L1= [true_clause([true], T3), global_next_clause([W], [P, W])], append(R1, L1, R).

cirRes(_,_, _, [], []).
cirRes(W, P, Q, [F|T], L) :- negation(F, F1), append([P], F1, X1), append(Q, X1, F2), 
	C1 = global_next_clause([W], X1), C2 = true_clause([true], F2),
	cirRes(W,P,Q, T, L1),
	append([C1], L1, L2), append([C2], L2, L3), sort(L3, L).


fE(C, L, Y, R,W) :- C= exist_future_clause(Q, H, I), find_Esometime_loop(L, Y, F, I),  
	(F = false, R = []; snfresE(F, Y, Q, R, W,I)).
	
snfresE(true, Y,Q, R, W,I) :- equall(- Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), 
	R = [exist_next_clause([W],[- Y],I), true_clause([true], T2), true_clause([true], T3), exist_next_clause([W], [P, W],I)].
snfresE(F, Y, Q, R, W,I) :-  equall(- Y, P), negation(Q, T1), append(T1, [P], T2), append(T2, [W], T3), 
	cirResE(W, P, T1, F, R1,I),
	L1= [true_clause([true], T3), exist_next_clause([W], [P, W],I)], append(R1, L1, R).

cirResE(_,_, _, [], [],I).
cirResE(W, P, Q, [F|T], L,I) :- negation(F, F1), append([P], F1, X1), append(Q, X1, F2), 
	C1 = exist_next_clause([W], X1,I), C2 = true_clause([true], F2),
	cirResE(W,P,Q, T, L1,I),
	append([C1], L1, L2), append([C2], L2, L3), sort(L3, L).




%ctlForget------------------------------------------end------------------------------------------


%judgeType(C, Type)-------------------------------start-------------------------------------------
%Judging the type of a mc C.

judgeType_mc(C, Type) :- C = exist_next_mc(_, _, _), Type = me.
judgeType_mc(C, Type) :- C = global_next_mc(_, _), Type = mg.
judgeType_mc(C, Type) :- C = true_mc(_, _), Type = mt.

%judgeType------------------------------------------end------------------------------------------


%E-loop-----------------------------------------------start-------------------------------------------
%If there is E-sometime (or A-sometime) clause for P, the we should find the E-loop formula F.
%(1) E-sometime: L consists of the set of all global, A-step clauses and E-step clauses with index ind.

find_Esometime_loop(L, P, F, Ind) :- find_Esometime_clauses(L, Ind, L1), change2mc(L1, L2), all_merge_clause(L2, L3), 
	e_Eloop_H(L3, P, H0), simp_DNF(H0, H1),  %2020-2-25 加了simp_DNF(H0, H1),
	(member([true],H0), F = ture, !; circleH(L3, P,  H0, F)).  %2020-2-25 加了F = ture,
	
	
%(2) A-sometime: L consists of the set of all global, A-step clauses and E-step clauses

find_Asometime_loop(L, P, F) :- find_Asometime_clauses(L, L1), change2mc(L1, L2), all_merge_clause(L2, L3), 
	e_Eloop_H(L3, P, H0), simp_DNF(H0, X), simp_Con_list(X,X,H1), %2020-2-25 加了simp_DNF(H0, H1), 2020-2-26加了simp_Con_list(X,H1),
	(member([true],H1), F = ture, !; circleH(L3, P,  H1, F)). %2020-2-24 加了F = ture,
	

find_Asometime_clauses([], []).
find_Asometime_clauses([C|L1], L2) :- judgeType(C, Type),
	(Type=e, C1=C;
		(Type=g, C1 = C;
			(Type=t, C1 =C; C1 =[])
		)
	), find_Asometime_clauses(L1, L3),
	(C1=[], L2=L3; append([C1], L3, L2)).



e_Eloop_H([],_,[]).
e_Eloop_H([H|L], P, F) :- judgeType_mc(H, Type),
	(Type = mt, !, (H = true_mc(H2, [A1]), ([P]=A1, H1=H; H1=[]); H1 = []); 
		(Type =mg, !, (H= global_next_mc(H2, [A2]), ([P]=A2, H1=H; H1=[]); H1 = []);
			(Type = me, !, (H = exist_next_mc(H2, [A3], I), ([P]=A3, H1=H; H1=[]); H1=[]))
		)
	),
	e_Eloop_H(L, P, F1),
	(H1=[], F2 = F1; append([H2], F1, F2)), sort(F2, F). 
	


circleH([H|T], P,  H0, R) :- e_Eloop_HCircle([H|T], P,  H0, F), 
	(member([true],F), !, R=true; 
		( F = [], !, R = false; (F = H0, !, R=F; circleH([H|T], P,  F, R)))
	).
	
e_Eloop_HCircle([], P, H0, []).
e_Eloop_HCircle([H|T], P,  H0, F) :- dnf2wff(H0, Wff), wff2cnf(Wff, CNF), judgeType_mc(H, Type),
	(	Type=me, !, H=exist_next_mc(X, Y, Ind), (member([P], Y), elimElement([P], Y, Y1), (cnfImpCNF(CNF, Y1), H1=H; H1=[]); H1 =[]);
		(	Type=mg, !, H=global_next_mc(X,Y), (member([P], Y), elimElement([P], Y, Y1), (cnfImpCNF(CNF, Y1), H1=H; H1 =[]); H1 =[]);
			(	Type=mt, !, H=true_mc(X,Y), (member([P], Y), elimElement([P], Y, Y1), (cnfImpCNF(CNF, Y1), H1=H; H1=[]); H1 =[]); H1=[]
			)
		)
	),
	e_Eloop_HCircle(T, P, H0, F1),
	(H1 =[], F3 = F1; append([X], F1, F2), sort(F2, F3)), simp_DNF(F3, F). %2020-2-25 “simp_Con_list(F3, F3, F)” 变为“simp_DNF(F3, F)”




%CNF2 implies CNF1: for each term t1 in CNF1, there is a term t2 in CNF2 such that t2 <= t1.
cnfImpCNF([], _). 
cnfImpCNF([H|CNF1], CNF2) :- subset_list(H, CNF2), cnfImpCNF(CNF1, CNF2). %CNF2 implies CNF1

%DNF2 implies DNF1: for each clause c2 in DNF2, there is a clause c1 in DNF1 such that c1 <= c2.
dnfImpDNF([], _).
dnfImpDNF([H|DNF2], DNF1) :- subset_list(H, DNF1), dnfImpDNF(DNF2, DNF1).



subset_list(H,[]):- !, fail.
subset_list(H, [H1|L1]) :- (subset(H1, H), !; subset_list(H, L1)).



subset([], _).
subset([H1|T], L2) :- member(H1, L2), subset(T, L2).



%E-loop-----------------------------------------------end----------------------------------------



%merge all the possible clauses-----------------------------start-----------------------------------------------------	
all_merge_clause([],[]).
all_merge_clause(L, R) :- splitL(L, L1, L2, L3), % L 为满足条件的集合
	merge_list_TT(L1, R1),
	merge_list_TE(R1, L2, R2), 
	merge_list_TG(R1, L3, R3),
	merge_list_EE(R2, R4),
	merge_list_GG(R3, R5),
	merge_list_GE(R5, R4, R6), 
	append(R1, R2, T1), append(R3, T1, T2), append(R4, T2, T3), append(R5, T3, T4), append(R6, T4, T5), sort(T5, T6),
	(T6=L, R= L; all_merge_clause(T6, R)).
	
	
change2mc([],[]).
change2mc([H|T], L2):- judgeType(H, Type),
	(	Type=t, !, H=true_clause(X1, Y1), findall(X, member(- X, Y1), L), 
		(L = [], H1 = true_mc(X1, [Y1]); extendTC(Y1, L, R), R1=  true_mc(X1, [Y1]), append([R1], R, H1)
		);
		( Type=e, !, H=exist_next_clause(X2, Y2, I), H1 = [exist_next_mc(X2, [Y2], I)];
			( Type=g, !, H=global_next_clause(X3, Y3), H1 = [global_next_mc(X3, [Y3])]; H1 =[]
			)
		)
	),
	change2mc(T, L3),
	(	H1 =[],  L2=L3; append(H1, L3, L2)).

/*change2mc([H|T], L2):- judgeType(H, Type),
	(	Type=t, !, H=true_clause(X1, Y1), H1 = true_mc(X1, [Y1]);
		( Type=e, !, H=exist_next_clause(X2, Y2, I), H1 = exist_next_mc(X2, [Y2], I);
			( Type=g, !, H=global_next_clause(X3, Y3), H1 = global_next_mc(X3, [Y3]); H1 =[]
			)
		)
	),
	change2mc(T, L3),
	(	H1 =[],  L2=L3; append([H1], L3, L2)).*/
	
extendTC(Y1, L, R)	:- findall(S, phrase(subseq(S), L), L2), setminus([[]], L2,L1),  extendTC_list(Y1, L1, R).
extendTC_list(_,[],[]).
extendTC_list(Y1, [H1|T1], [H2|T2]) :- negation(H1, H), setminus(H, Y1, Y), H2 = true_mc(H1, [Y]), extendTC_list(Y1, T1, T2).


%---------------------计算所有的子集--start---------------	
%e.g. phrase(subseq(S), [a,b,c,d]).
subseq([]) --> seq(_) .
subseq([X|Xs]) --> seq(_), [X], seq(Xs), seq(_).

% alternatively: seq(_), seq([X|Xs]), seq(_).

seq([]) --> [].
seq([X|Xs]) --> [X], seq(Xs).
%---------------------计算所有的子集---end--------------


	
%splitL: split L into three lists: set of global clauses, set of E-step clauses with the same Ind and set of A-step clauses
splitL([],[],[],[]).
splitL([H|T], L1, L2, L3):-  judgeType_mc(H, Type),
	(	Type=mt, !, H1 = H;
		(	H1=[], Type=me, !, H2 = H;
			(	H2 = [], Type=mg, !, H3 = H; H3 =[]
			)
		)
	),
	splitL(T, L4, L5, L6),
	(	H1 =[], !, L1 = L4, (H2 = [], !, L2 = L5, (H3 =[], !, L3 = L6; append([H3], L6, L3)); (append([H2], L5, L2), L3 = L6));
		(	append([H1], L4, L1), L2 = L5, L3 = L6
		)
	).
	

%merge rules:
merge_TT(C1, C2, C) :- C1 = true_mc(T1, H1), C2=true_mc(T2,H2), append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	(T1 = [true], (T2 =[true], C = true_mc(T1,H); C = true_mc(T2,H));
		(T2 =[true], C = true_mc(T1,H); append(T1, T2, T3), sort(T3, T), C = true_mc(T,H))
	).
	
/*merge_TT(C1, C2, C) :- C1 = true_mc(T1, H1), C2=true_mc(T2,H2), T=T1, append(H1, H2, H3), 
	sort(H3, H4), simp_Con_list(H4, H4, H), C = true_mc(T,H).*/

/*merge_TE(C1, C2, C) :- C1 = true_mc(T1, H1), C2=exist_next_mc(T2, H2, I), %append(T1, T2, T3), sort(T3, T),
	append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	C = exist_next_mc(T2,H,I).
merge_TG(C1, C2, C) :- C1 = true_mc(T1, H1), C2=global_next_mc(T2, H2), %append(T1, T2, T3), sort(T3, T),
	append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	C = global_next_mc(T2,H).*/
	
merge_TE(C1, C2, C) :- C1 = true_mc(T1, H1), C2=exist_next_mc(T2, H2, I), append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	(T1 = [true], C = exist_next_mc(T2,H, I);
		append(T1, T2, T3), sort(T3, T), C =exist_next_mc(T,H, I)
	).
	/*(L =[], append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H), C = global_next_mc(T2,H);
		negation(L, Y), setminus(Y, H1, H5), append(L, T2, T), append(H5, H2, H6), C =exist_next_mc(T,H6, I)
	).
	
merge_TG(C1, C2, C) :- C1 = true_mc(T1, H1), C2=global_next_mc(T2, H2), findall(X, member(- X, H1), L),%append(T1, T2, T3), sort(T3, T),
	(L =[], append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H), C = global_next_mc(T2,H);
		negation(L, Y), setminus(Y, H1, H5), append(L, T2, T), append(H5, H2, H6), C = global_next_mc(T,H6)
	).*/
	
merge_TG(C1, C2, C) :- C1 = true_mc(T1, H1), C2=global_next_mc(T2, H2), append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H), 
	(T1 = [true], C = global_next_mc(T2,H);
		append(T1, T2, T3), sort(T3, T), C = global_next_mc(T,H)
	).
	
merge_EE(C1, C2, C) :- C1=exist_next_mc(T1, H1, I1), C2=exist_next_mc(T2, H2, I2), 
	(I1=I2, append(T1, T2, T3), 
	sort(T3, T4), simp_conSet(T4,  T),
	append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	C = exist_next_mc(T,H,I1); C =[]).
merge_GG(C1, C2, C) :- C1 = global_next_mc(T1, H1), C2=global_next_mc(T2, H2), append(T1, T2, T3), 
	sort(T3, T4), simp_conSet(T4, T),
	append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	C = global_next_mc(T,H).
	
merge_GE(C1, C2, C) :- C1= global_next_mc(T1, H1), C2=exist_next_mc(T2, H2, I), append(T1, T2, T3), 
	sort(T3, T4), simp_conSet(T4, T),
	append(H1, H2, H3), sort(H3, H4), simp_Con_list(H4, H4, H),
	C = exist_next_mc(T, H, I).

%[L1,L2]：expressing the conjunction of L1 and L2.


%merge_list:
merge_list_TT([], []).
merge_list_TT([H|T], R) :- X=[H|T], tt_merge_list(H, T, R1), append(X, R1, R2), sort(R2, R3), sort(X,Y),
	(\+(R3 = Y), merge_list_TT(R3, R); R = R3).


tt_merge_list(_, [], []).
tt_merge_list(C1, [H|T], R) :- merge_TT(C1, H, C), tt_merge_list(C1, T, R1), append([C], R1, R2), sort(R2, R).

merge_list_TE([],L, L).
merge_list_TE(L, [],[]).
merge_list_TE([H1|T1],L2,R) :- X=[H1|T1], te_merge_list(H1, L2, R1), merge_list_TE(T1, L2, R2), 
	append(R1, R2, R3),  sort(R3, R5), sort(X,Y),
	(\+(R5 = L2), merge_list_TE(X, R5, R); R = R5).

te_merge_list(_, [], []).
te_merge_list(C1, [H|T], R) :- merge_TE(C1, H, C), te_merge_list(C1, T, R1), append([C], R1, R2), sort(R2, R).


merge_list_TG([],L, L).
merge_list_TG(L, [],[]).
merge_list_TG([H1|T1],L2,R) :- X=[H1|T1], tg_merge_list(H1, L2, R1), merge_list_TG(T1, L2, R2), 
	append(R1, R2, R3),  sort(R3, R5), sort(X,Y),
	(\+(R5 = L2), merge_list_TG(X, R5, R); R = R5).

tg_merge_list(_, [], []).
tg_merge_list(C1, [H|T], R) :- merge_TG(C1, H, C), tg_merge_list(C1, T, R1), append([C], R1, R2), sort(R2, R).


merge_list_EE([], []).
merge_list_EE([H|T], R) :- X=[H|T], ee_merge_list(H, T, R1), append(X, R1, R2), sort(R2, R3), sort(X,Y),
	(\+(R3 = Y), merge_list_EE(R3, R); R = R3).


ee_merge_list(_, [], []).
ee_merge_list(C1, [H|T], R) :- merge_EE(C1, H, C), ee_merge_list(C1, T, R1), (C=[], R = R1; append([C], R1, R2), sort(R2, R)).



merge_list_GG([], []).
merge_list_GG([H|T], R) :- X=[H|T], gg_merge_list(H, T, R1), append(X, R1, R2), sort(R2, R3), sort(X,Y),
	(\+(R3 = Y), merge_list_GG(R3, R); R = R3).


gg_merge_list(_, [], []).
gg_merge_list(C1, [H|T], R) :- merge_GG(C1, H, C), gg_merge_list(C1, T, R1), append([C], R1, R2), sort(R2, R).

merge_list_GE([],L, L).
merge_list_GE(L, [],[]).
merge_list_GE([H1|T1],L2,R) :- X=[H1|T1], ge_merge_list(H1, L2, R1), merge_list_GE(T1, L2, R2), 
	append(R1, R2, R3),  sort(R3, R5), sort(X,Y),
	(\+(R5 = L2), merge_list_GE(X, R5, R); R = R5).

ge_merge_list(_, [], []).
ge_merge_list(C1, [H|T], R) :- merge_GE(C1, H, C), ge_merge_list(C1, T, R1), append([C], R1, R2), sort(R2, R).

%merge----------------------------------end-------------------------------------------------



%find E-sometime set of clauses-----------------------------start-----------------------
%find the set of all global, A-step clauses and E-step clauses with index Ind. （因为对于E-sometime来说，这条路径必须与E-sometime的Ind一致（看参考文献2000））
find_Esometime_clauses([], Ind, []).
find_Esometime_clauses([H|T], Ind, R) :- judgeType(H, Type), 
	(Type = t, !, H = H1; 
		(Type =g, !, H= H1;
			(Type = e, !, (H =exist_next_clause(_,_, Ind), H1 = H; H1=[]); H1=[])
		)
	),
	find_Esometime_clauses(T, Ind, T1),
	(H1=[], R = T1; append([H1], T1, R)).

%find E-sometime set of clauses-----------------------------end-----------------------


	
%find A-sometime set of clauses-----------------------------start-----------------------
%find the set of all global, A-step clauses and E-step clauses. （因为对于A-sometime来说，只要存在一条路径又该性质即可，不在乎是哪条路劲（看参考文献2000））
find_Asometime_clauses([], []).
find_Asometime_clauses([H|T], R) :- judgeType(H, Type), 
	(Type = t, !, H = H1; 
		(Type =g, !, H= H1;
			(Type = e, !, H1 = H; H1=[])
		)
	),
	find_Asometime_clauses(T, T1),
	(H1=[], R = T1; append([H1], T1, R)).	
%find A-sometime set of clauses-----------------------------end-----------------------	
	
	

	
%tran2CTL---------------------------------------------start-------------------------------------------

%tranI2CTL_list: Transform a set of clauses into a set of clauses with no index （先计算传递性，再去掉index）
tranI2CTL_list([],[]).
tranI2CTL_list([H|T], L1) :- tranI2CTL(H, H1),
	tranI2CTL_list(T, L2),
	append([H1], L2, L3), sort(L3, L1).
	
tranI2CTL(C, C1) :- judgeType(C, Type),
	(Type = e, C = exist_next_clause(T, H, I), C1 = exist_next_clause(T,H); C1 = C).
	
%Eliminate all the start in the set of clauses by Proposition 13
tranSt2CTL([], []).
tranSt2CTL([H|T], R) :- 
	(H=start_clause(X, Y), H1 = Y;
		(H=global_next_clause(X, Y), (member(start, X), elimElement(start, X, X1), (X1 =[], H1 = Y; H1=n_global_next_clause(X1, Y)); H1 = H);
			(H=exist_next_clause(X, Y), (member(start, X), elimElement(start, X, X1), (X1 =[], H1 = Y; H1=n_exist_next_clause(X1, Y)); H1 =H);
				H1=H
			)
		)
	),
	tranSt2CTL(T, R1), 
	append([H1], R1, R2), sort(R2, R).

% trans: Compute all the possible result of transitivity between two clauses in a set of clauses
% In order to convenience, we only to compute the case of transitivity that the form of clases is {Q -> li, li -> D}, then we obtain Q -> Q.
trans([],[]).
trans(L1, L) :- splitNoIL(L1, L2, L3, L4, L5), trans_list(L2, L3, L4, L5, L).


trans_list(L1, L2, L3, L4, R) :- 
		trans_tg(L1, L3, R1), %注意对R1中子句的化简
		trans_te(L1, L4, R2),
		trans_stg(L2, L3, R3),
		trans_ste(L2, L4, R4),
		append(L1, L2, L5), append(L3, L5, L6), append(L4, L6, L7), 
		append(R1, R2, R5), append(R3, R5, R6), append(R4, R6, R7), %以下可用下面的注释处替换
		append(L7, R7, Z),
		sort(Z, Z1),
		sort(L7, Z2),
		append(R1, R3, X), sort(X, X1),
		append(R2, R4, Y), sort(Y, Y1),
		(Z1 = Z2, !, R = Z1; trans_list(L1, L2, X1, Y1, R)).
		
		/*%append(R1, R3, X), sort(X, X1), 
		%append(R2, R4, Y), sort(Y, Y1),
		sort(L7, L8), append(L8, R7, R8),
		sort(R8, R).
		%(L8 = R8, !, R = R8; trans_list(L1, L2, X1, Y1, R)).*/

splitNoIL([],[],[],[],[]).
splitNoIL([H|T], L1, L2, L3, L4) :- judgeType(H, Type),
	(	Type = t, !,  H1 = H,  H2 = [], H3=[], H4=[];
		(	Type = st, !,  H2 = H,  H1=[], H3=[], H4=[];
			(   Type = g, !,  H3 = H,  H1=[],H2=[], H4=[]; 
				(   Type = e, !, H4 = H;  H1=[], H2=[], H3=[])
			)
		)
	), splitNoIL(T, L5, L6, L7, L8),
	(	H1 =[], !, L1 = L5, 
			(H2 = [], !, L2 = L6, 
				(H3 =[], !, L3 = L7, (H4 = [], L4=L8 ; append([H4], L8, L4)); 
					(append([H3], L7, L3), L4 = L8)
				); 
				(append([H2], L6, L2), L3 = L7, L4=L8)
			);
		(append([H1], L5, L1), L2 = L6, L3 = L7, L4 = L8)
	).

%对列表中的元素取反合取：也即是将求子句C的否定\neg C
negation([],[]).
negation([H|T], [H1|T1]) :- 
	equall(- H, H1), 
	negation(T, T1).
 
trans_tg([], L, L). %结果中保留了L的原来的子句。
trans_tg(L, [], []).
trans_tg([H1|L1], L3, R) :- trans_tg_list(H1, L3, R1),
	trans_tg(L1, L3, R2), append(R1, R2, R3), sort(R3, R).
	
trans_tg_list(C, [], []).
trans_tg_list(C, [H|T], L) :- C = true_clause(X1, Y1), H = global_next_clause(X2, Y2),
	(member(P, Y1), member(P, X2), elimElement(P, Y1, T1), elimElement(P, X2, T2), (T1 = []; negation(T1, NT)),
	append(NT, X1, T3), append(T3, T2, T4), C1 = global_next_clause(T4, Y2), simp_GC(C1, C2);
	C2 = []),
	trans_tg_list(C, T, L1),
	(C2 = [], L=L1; append([C2], L1, L2), sort(L2, L)).


trans_te([], L, L).
trans_te(L, [], []).
trans_te([H1|L1], L3, R) :- trans_te_list(H1, L3, R1),
	trans_te(L1, L3, R2), append(R1, R2, R3), sort(R3, R).
	
trans_te_list(C, [], []).
trans_te_list(C, [H|T], L) :- C = true_clause(X1, Y1), H = exist_next_clause(X2, Y2,I),
	(member(P, Y1), member(P, X2), elimElement(P, Y1, T1), elimElement(P, X2, T2), (T1 = []; negation(T1, NT)), 
	append(NT, T2, T3), (T3 = [], T4 =[true]; T4 = T3), C1 = exist_next_clause(T4, Y2,I), simp_EC(C1, C2);
	C2 = []),
	trans_te_list(C, T, L1),
	(C2 = [], L=L1; append([C2], L1, L2), sort(L2, L)).
	
trans_stg([], L, L).
trans_stg(L, [], []).
trans_stg([H1|L1], L3, R) :- trans_stg_list(H1, L3, R1),
	trans_stg(L1, L3, R2), append(R1, R2, R3), sort(R3, R).
	
trans_stg_list(C, [], []).
trans_stg_list(C, [H|T], L) :- C = start_clause(X1, Y1), H = global_next_clause(X2, Y2),
	(member(P, Y1), member(P, X2), elimElement(P, Y1, T1), elimElement(P, X2, T2), (T1 = []; negation(T1, NT)),
	append([start], NT, T3), append(T3, T2, T4), C1 = global_next_clause(T4, Y2), simp_GC(C1, C2);
	C2 = []),
	trans_stg_list(C, T, L1),
	(C2 = [], L=L1; append([C2], L1, L2), sort(L2, L)).


trans_ste([], L, L).
trans_ste(L, [], []).
trans_ste([H1|L1], L3, R) :- trans_ste_list(H1, L3, R1),
	trans_ste(L1, L3, R2), append(R1, R2, R3), sort(R3, R).
	
trans_ste_list(C, [], []).
trans_ste_list(C, [H|T], L) :- C = start_clause(X1, Y1), H = exist_next_clause(X2, Y2,I),
	(member(P, Y1), member(P, X2), elimElement(P, Y1, T1), elimElement(P, X2, T2), (T1 = []; negation(T1, NT)),
	append([start], NT, T3), append(T3, T2, T4), C1 = exist_next_clause(T4, Y2,I), simp_EC(C1, C2);
	C2 = []),
	trans_ste_list(C, T, L1),
	(C2 = [], L=L1; append([C2], L1, L2), sort(L2, L)).
	

%Elm operator: eliminate those clauses that contian some atoms in V 
elim([], _, []).
elim(L, [], L).
elim([H|T], V, R) :- elim_one(H, V, F), elim(T, V, L),
	(F = [], R = L; append([F], L, R1), sort(R1, R)).
	
elim_one(C, V, F) :- 
	(C = true_clause(T, H), append(T,H, X), (inter(X, V), F = []; F =C);
		(C = global_next_clause(T, H), append(T,H, X), (inter(X, V), F = []; F =C);
			( C = exist_next_clause(T,H), append(T,H, X), (inter(X, V), F = []; F =C);
				( C = start_clause(T, H), append(T,H, X), (inter(X, V), F = []; F =C);
					(C = n_global_next_clause(T, H), append(T,H, X), (inter(X, V), F = []; F =C);
						(C=n_exist_next_clause(T,H), append(T,H, X), (inter(X, V), F = []; F =C);
							%(inter(C, V), F = []; F =C)
							(C=[], F = false;
								(inter(C, V), F = []; F = C)
							)
						)
					)
					%(C=[], F = false;
					%	(inter(C, V), F = []; F = C)
					%)
				)
			)
		)
	).
 
inter([],_) :- !, fail.
inter(H, []) :- !, fail.
inter(H, V) :- (member(P, H), member(P, V);
		(member(- P, H), member(P, V);
			member(P, H), member(- P, V)
		)
	).
 
%tran2CTL---------------------------------------------end-------------------------------------------



%Substitution-------------------------------------start-------------------------------------------
%subV(L1, V, V1, V2) : instantiate the atoms in V1 in L1, and obtain the V2 where each atom in V2 is really irrelevant.

subV([], _, V1, V1, []). %只差instant_formula未测试，其余都已经测试
subV(L1, V, V1, V2, L) :- change_trueC(L1, V, V1, V4), append(V, V4, Vc), chuquP(L1, V4, Vc, Vx), instant_formula(L1, L1, V, Vx, L4),
	(L4 = L1, Vx=V1, V2 = Vx, L = L4; subV(L4, V, Vx, V2, L)).


chuquP([], V1, _, V1) :- !.
chuquP([C|L], V1, Vc, V2) :-  
	((C = true_clause([P], H); C=global_next_clause([P], H); C = global_future_clause([P], H);C=start_clause([P], H)),
		(member(P, V1), (inter(H, Vc), Vx=[], chuquP(L, V1, Vc, V2); setminus([P], V1, Vx), setminus([P], Vc, Vy),chuquP(L, Vx, Vy, V2)); Vx=[], chuquP(L, V1, Vc, V2));
		((C = exist_next_clause([P], H, I); C=exist_future_clause([P], H, I)),
			(member(P, V1), (inter(H, Vc), Vx=[], chuquP(L, V1, Vc, V2); setminus([P], V1, Vx), setminus([P], Vc, Vy), chuquP(L, Vx, Vy, V2)); Vx=[], chuquP(L, V1, Vc, V2))
		)
	).


inter([],_, _) :- !, fail.
inter(H, [], _) :- !, fail.
inter(H, V, P) :- (member(P, H), member(P, V);
		(member(- P, H), member(P, V);
			member(P, H), member(- P, V)
		)
	).

%change_trueC(L1, V1, L2): (i) 将true子句标记， 当满足其中只有一个V1中的元素负出现在D中时，没将true子句转换成蕴含式
change_trueC([], _, V1, V1).
change_trueC([C|L1], V, V1, V2) :- judgeType(C, Type), 
	(Type=t, C= true_clause([true], D), 
		(inter(V, D), change_trueC(L1, V, V1, V2);
			findall(X, inter(V1, D, X), L), length(L, N),
					(N=1, L = [P], member(- P, D), elimElement(P, V1, V3), change_trueC(L1, V, V3, V2); change_trueC(L1, V, V1, V2)
					); change_trueC(L1, V, V1, V2)
		); change_trueC(L1, V, V1, V2) 
	).
	
/*%change_trueC(L1, V1, L2): (i) 将true子句标记，当满足其中只有一个V1中的元素负出现在D中时，将true子句转换成蕴含式
change_trueC([], _, V1, V1,[]).
change_trueC([C|L1], V, V1, V2, [C2|L2]) :- judgeType_NI(C, Type), 
	(Type=t, C= true_clause([true], D), 
		(inter(V, D), C2 = C, change_trueC(L1, V, V1, V2, L2);
			findall(X, inter(V1, D, X), L), length(L, N),
					(N=1, L = [P], member(- P, D), setminus([-P], D, D1), C2=true_clause([P], D1), elimElement(P, V1, V3), change_trueC(L1, V, V3, V2, L2); C2 = C, change_trueC(L1, V, V1, V2, L2)
					); C2 = C, change_trueC(L1, V, V1, V2, L2)
		); C2 = C, change_trueC(L1, V, V1, V2, L2) 
	).
*/
%



	

%instant_formula(L2, L2, V, V1, L3) : (ii)(iii) 将L2中的实例公式（不包括V 和 V1中的原子）找出，并把V1中的已经实例化的原子去掉. 每次要么增加一条子句，要么实例化一个变量。
instant_formula([], V, V1, V1, []).
instant_formula(L1, _, [], _, L1).
instant_formula([C|L1], Lr, V, V1, L2) :- judgeType(C, Type), append(V, V1, V3), %Lr=[C|L1]
	(Type = e, C = exist_next_clause(T, H,I), 
		(inter(H, V3), C1 = [], instant_formula(L1, Lr, V, V1, L3);
			(T=[P], (P=start, !, C1 = [], instant_formula(L1, Lr, V, V1, L3); (member(P, V1), elimElement(P, V1, V4), C1 = []; C1=[], instant_formula(L1, Lr, V, V1, L3)));  
				transP(Lr, V, V1, T, A), (A =[], C1 = [], instant_formula(L1, Lr, V, V1, L3); C1 = exist_next_clause(A, H,I))
			)
		);
		( Type = g, C = global_next_clause(T, H),  
			(inter(H, V3), C1 = [], instant_formula(L1, Lr, V, V1, L3);
				(T=[P], (P=start, !, C1 = [], instant_formula(L1, Lr, V, V1, L3); (member(P, V1), elimElement(P, V1, V4), C1 = []; C1=[], instant_formula(L1, Lr, V, V1, L3)));  
					transP(Lr, V, V1, T, A), (A =[], C1 = [], instant_formula(L1, Lr, V, V1, L3); C1 = global_next_clause(A, H))
				)
			);
			( Type = gf, C = global_future_clause(T, H),
				(inter(H, V3), C1 = [], instant_formula(L1, Lr, V, V1, L3);
					(T=[P], (P=start, !, C1 = [], instant_formula(L1, Lr, V, V1, L3); (member(P, V1), elimElement(P, V1, V4), C1 = []; C1=[], instant_formula(L1, Lr, V, V1, L3)));  
						transP(Lr, V, V1, T, A), (A =[], C1 = [], instant_formula(L1, Lr, V, V1, L3); C1 = global_future_clause(A, H))
					)
				);
				( Type = ef, C = exist_future_clause(T,H,I),
					(inter(H, V3), C1 = [], instant_formula(L1, Lr, V, V1, L3);
						(T=[P], (P=start, !, C1 = [], instant_formula(L1, Lr, V, V1, L3); (member(P, V1), elimElement(P, V1, V4), C1 = []; C1=[], instant_formula(L1, Lr, V, V1, L3)));  
							transP(Lr, V, V1, T, A), (A =[], C1 = [], instant_formula(L1, Lr, V, V1, L3); C1 = exist_future_clause(A, H,I))
						)
					); 
					instant_formula(L1, Lr, V, V1, L3)
				)
			)
		)
	), (C1 =[], L2 = Lr; append([C1], L3, L2)). %添加了特殊的子句，EX和AX的尾部含有start （也许还有EF， AF的情形）



%transP: 第(iV)条
transP([], V, V1, _, []).
transP(_, _, [], _, []).
transP([C|L1], V, V1, Q, F) :- split_st_t([C|L1], Lst, Lt),
	tranP_start(Lst, V, V1, Q, F1),
	(F1 = [], tranP_true(Lt, V, V1, Q, F); F = F1).
	

split_st_t([], [],[]).
split_st_t([C|L3], Lst, Lt) :- judgeType(C, Type), 
	(Type = st, C1 = C, C2 = [];
		(Type = t, C2 = C, C1 = []; C1=[], C2 = [])),
	split_st_t(L3, L1, L2),
	(C1 = [], (Lst=L1, C2=[], Lt = L2; append([C2], L2, Lt));
		(append([C1], L1, Lst), Lt = L2)
	).
	
	


 tranP_true([], _,_,_,_, []).
 tranP_true(_, _,_, [], _, []).
 tranP_true(L1, V, V2, [Y|V1], Q, F1) :- findall(X, (member(X, L1), inCt(X, V, V1,Q, Y)), L2),
	(includeQ(L2, Q), F1= Y; tranP_true(L1, V, V2, V1, Q, F1)). 
 
 
 
 includeQ([], _) :- !, fail.
 includeQ(_, []).
 includeQ(L1, [Y|Q]) :- incY(L1, Y, F), 
	(F=false, !, fail; includeQ(L1, Q)).
 
 incY([],_, false).
 incY([C|L1], Y, F) :- C = true_clause([true], D), 
	(inter([Y], D), F = true;
		incY(L1, Y, F)
	).
 
 %allInC([], V, V1,Q, Y, []).
 %allInC(L, V, V1,Q, Y, L1) :- findall(X, (member(X, L1), inCt(X, V, V1,Q, Y)), L1).
 
 inCt(C, V, V1,Q, Y) :- C = true_clause([true], D), 
	(inter(V, D), !, fail;
			(member(- Y, D), elimElement(- Y, D, D1), length(D1, N1),
				(N1=1, inter(D1, Q); !, fail); !, fail
			)
	).


	

tranP_start([], _, []).
tranP_start(L1, Q, F1) :- findall(X, (member(X, L1), inCst(X, Q)), L2),
	(includeQst(L2, Q), F1= start; tranP_start(L1, Q, F1)). 


includeQst([], _) :- !, fail.
 includeQst(_, []).
 includeQst(L1, [Y|Q]) :- incYst(L1, Y, F), 
	(F=false, !, fail; includeQst(L1, Q)).
 
 incYst([],_, false).
 incYst([C|L1], Y, F) :- C = start_clause([start], D), 
	(inter([Y], D), F = true;
		incYst(L1, Y, F)
	).
	
	
 inCst(C, Q) :- C = start_clause([start], D), 
	(inter(V, D), !, fail;
			(length(D, N1),
				(N1=1, inter(D, Q); !, fail); !, fail
			)
	).


%Judging the type of a Clause C with no index.
judgeType_NI(C, Type) :- C = exist_next_clause(_, _), Type = e.
judgeType_NI(C, Type) :- C = global_next_clause(_, _), Type = g.
judgeType_NI(C, Type) :- C = true_clause(_, _), Type = t.
judgeType_NI(C, Type) :- C = start_clause(_, _), Type = st. 
judgeType_NI(C, Type) :- C = global_future_clause(_,_), Type=gf.
judgeType_NI(C, Type) :- C = exist_future_clause(_,_), Type=ef.


%Substitution-------------------------------------end-------------------------------------------

%index2NI(T, T1)-------------------------------------------start-----------------------------------------------------
%将ind_CTL换为CTL
index2NI([],[]).
index2NI([C|L], [C1|L1]) :- judgeType(C, Type),
	(Type=e, C=exist_next_clause(T, H, I), unionEx([C|L], T, I, Ex, R), setminus(Ex, L, T1), index2NI(T1, L1);
		(Type=ef, C=exist_future_clause(T,H, I), findEf(L, I, Ef), append(C, Ef, Ef1), unionEf(Ef1, C1), setminus(Ef1, L, T1), index2NI(T1, L1);
		C1= C, index2NI(L, L1))
	).
	
unionEx([], _, _, [], []).
unionEx(L, T, I, Ex, R) :- findExI(L, I, Ex1), unionEXI(Ex1, F1), 
	findExIT(L, T, I, Ex2), unionEXIT(Ex2, F2), append(F1, [F2], R1), sort(R1, R), Ex=Ex1.


findExI([], _, []).
findExI([C|L], I, Ex) :- judgeType(C, Type), !,
	(Type = e, C=exist_next_clause(T, H, I1), (I = I1, C1= C; C1=[]);
		C1=[]
	), findExI(L, I, Ex1),
	(C1=[], Ex=Ex1; append([C1], Ex1, Ex)).
	
unionEXI([], _, []).
unionEXI(L, F) :- findall(X, sublist(X, L), R), setminus([[]], R, R1), unionF(R1, F).

unionF([],[]).
unionF([C|L], [C1|L1]) :- unionEXIT(C, C1), unionF(L, L1).


prefix(S,L) :- append(S,_,L). %前缀
suffix(S,L):- append(_,S,L). %后缀
sublist(SubL,L):- suffix(S,L), prefix(SubL,S).
	
findExIT([], _, _, []).
findExIT([C|L], T, I, Ex) :- judgeType(C, Type), 
	(Type = e, C=exist_next_clause(T1, H1, I1), (T=T1, I = I1, C1= C; C1=[]);
		C1=[]
	), findExIT(L, T, I, Ex1),
	(C1=[], Ex=Ex1; append([C1], Ex1, Ex)).
	
unionEXIT([], []).
unionEXIT([C|Ex], F) :- C = exist_next_clause(T1, H1, I1), length(Ex,N),
	(N=0, F1 = C; unionEXIT(Ex, F2)), 
	(F2=[], F=F1; F2=exist_next_clause(T2, H2, I2), append(T1, T2, T), sort(T, T3),
	append(H1, H2, H), sort(H, H3), F = exist_next_clause(T3, H3)).
	
	
	
aux(L, N, [H|T]) :-
    N > 1,
    select(H, L, M),   % Select an element "H" from "L", leaving "M"
    N1 is N-1,         % NOTE the "is" here, not "=" !!
    aux(M, N1, T).     % Recurse with remaining elements "M" and count-1
aux(L, 1, [X]) :- member(X, L).

arrangements(L, N, R):-
    findall(X, aux(L, N, X), R).
	

	

%index2NI(T, T1)-------------------------------------------start-----------------------------------------------------




%simplify ----------------------------------------start-------------------------------------------
%simplify clause (mc: merge clause) C such that there is no more [true] and []
%example: [true, a] =[a]; [[true],[a]] = [[a]]; []=false.
simplify_clause(C, C1) :- judgeType(C, Type),
	(	Type=t, simp_TC(C, C1);
		(	Type=e, simp_EC(C, C1);
			(Type=g, simp_GC(C, C1);
				(Type=st, simp_STC(C, C1))
			)
		)
	).

simplify_mclause(C, C1) :- judgeType_mc(C, Type),
	(	Type=mt, simp_TMC(C, C1);
		(	Type=me, simp_EMC(C, C1);
			(Type=mg, simp_GMC(C, C1);
				(Type=mst, simp_STMC(C, C1))
			)
		)
	).
	
simp_TC(C, C1) :- C = true_clause(T, H), simp_disSet(H, H1), C1 = true_clause(T, H1).
simp_EC(C, C1) :- C = exist_next_clause(T, H, I), simp_conSet(T, T1), simp_disSet(H, H1), C1=exist_next_clause(T1, H1, I).
simp_GC(C, C1) :- C = global_next_clause(T, H), simp_conSet(T, T1), simp_disSet(H, H1), C1 = global_next_clause(T1, H1).
simp_STC(C, C1) :- C = start_clause(T, H), simp_disSet(H, H1), C1 = start_clause(T, H1).

simp_disSet([],[false]).
simp_disSet(L, L1) :- (member(P, L), member(-P, L), L1= [true]; 
	(member(true, L), L1=[true]; 
		(member(false, L), elimElement(false, L, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离

simp_conSet([], [true]).
simp_conSet(L, L1) :- (member(P, L), member(-P, L), L1= [false]; 
	(member(false, L), L1 =[false]; 
		(member(true, L), elimElement(true, L, L2), sort(L2, L1); sort(L, L1))
	)
	). %注意负号与数字之间的距离
	
elimElement(H, [], []).
elimElement(H, [H1|T1], L1) :- elimElement(H, T1, L2), 
	(H = H1, L1=L2; append([H1], L2, L1)).

simp_TMC(C, C1) :- C = true_mc(T, H), simp_disSet_list(H, H1), simp_Con_list(H1, H1, H2), C1 = true_mc(T, H2).
simp_EMC(C, C1) :- C = exist_next_mc(T, H, I), simp_conSet(T, T1), simp_disSet_list(H, H1),
	simp_Con_list(H1,H1,H2), C1 = exist_next_mc(T1, H2, I).
simp_GMC(C, C1) :- C = global_next_mc(T, H), simp_conSet(T, T1), simp_disSet_list(H, H1), 
	simp_Con_list(H1,H1,H2), C1 = global_next_mc(T1, H2).
simp_STMC(C, C1) :- C = start_mc(T, H), simp_conSet(T, T1), simp_disSet_list(H, H1), 
	simp_Con_list(H1,H1,H2), C1 = start_mc(T1, H2).




simp_disSet_list([], []).
simp_disSet_list([H|T], L) :- simp_disSet(H, H1), simp_disSet_list(T, T1), append([H1], T1, L1), sort(L1, L).

%the subsume of the term in conjunction list(CNF)
%simplify list
simp_Con_list([], L, L).
simp_Con_list([H|T], X, L) :- ( member(H, X), elimElement_Con_list(H, X, L1), length(L1, N1), length(T, N2),
	(N1 =< N2, simp_Con_list(L1, L1, L); simp_Con_list(T, L1, L)); simp_Con_list(T, X, L)
	).
	

elimElement_Con_list(H, [], [H]).
elimElement_Con_list(H, [H1|L1], L) :- elimElement_Con_list(H, L1, L2), 
	(subset(H, H1), L = L2; append([H1], L2, L)).
	
%the subsume of the term in disjunction list (DNF) %应该与CNF的情形一样, 2020-2-25用simp_Con_list来化简DNF
%simplify list
simp_Dis_list([], L, L).
simp_Dis_list([H|T], X, L) :- ( member(H, X), elimElement_Dis_list(H, X, L1), length(L1, N1), length(T, N2),
	(N1 =< N2, simp_Dis_list(L1, L1, L); simp_Dis_list(T, L1, L)); simp_Dis_list(T, X, L)
	). 
	
	

elimElement_Dis_list(H, [], [H]).
elimElement_Dis_list(H, [H1|L1], L) :- elimElement_Dis_list(H, L1, L2), 
	(subset(H1, H), L = L2; append([H1], L2, L)).
	

	
simp_CNF([],[]).
simp_CNF(CNF,CNF1) :- simp_disSet_list(CNF, L1), (member([true], L1), elimElement([true], L1, L); L = L1),
	((member([P], L), member([- P], L)), CNF1=[[false]]; CNF1 = L).
	
simp_DNF([], []).
simp_DNF(DNF, DNF1) :- simp_conSet_list(DNF, L1), (member([false], L1), elimElement([false], L1, L); L = L1),
	((member([P], L), member([- P], L)), DNF1=[[true]]; DNF1 = L).
	
simp_conSet_list([], []).
simp_conSet_list([H|T], L) :- simp_conSet(H, H1), simp_conSet_list(T, T1), append([H1], T1, L1), sort(L1, L).
%simplify--------------------------------------------end-------------------------------------
	

%subsume_clause---------------------------------------start-------------------------------------------
%The subsume between SNF clauses: eliminate those clauses subsumed by some clause

subsume_clause(C1, C2) .

%subsume_clause---------------------------------------end-------------------------------------------


	
%snfL2CTLF------------------------------------------start-------------------------------------------	
%List to CTL formula （这种转换方式是基于在计算transtivety 时只计算了前面说的方式）
snfL2CTLF([],[]).
snfL2CTLF([H|T], [H1|T1]) :- %judgeType(H, Type),
	(H = true_clause(X,Y), !, tSNF2CTL(H, H1);
		(H = global_next_clause(X,Y), gSNF2CTL(H, H1);
			(
				H = exist_next_clause(X,Y), !, eSNF2CTL(H, H1);
					(H = start_clause(X,Y), !, stSNF2CTL(H, H1);
						cnf2wff([H], H1)
					)
			)
		)
	),
	snfL2CTLF(T, T1).
	
tSNF2CTL(C, C1) :- C = true_clause([true], T1), cnf2wff([T1], T2), C1 = (true -> T2).
gSNF2CTL(C, C1) :- C = global_next_clause(T, H), dnf2wff([T], F1), cnf2wff([H], F2), C1 = (F1 -> @*(F2)).
eSNF2CTL(C, C1) :- C = exist_next_clause(T, H), dnf2wff([T], F1), cnf2wff([H], F2), C1 = (F1 -> $*(F2)).
stSNF2CTL(C, C1) :- C = start_clause([start], H), cnf2wff([H], F2), C1 = (start -> F2).


%tran2SNFCl(F, V1, L): transform a CTL formula into a set of snf clauses
tran2SNFCl([], []).
tran2SNFCl([H|L],R) :- tranH2C(H, C), tran2SNFCl(L, R1), append([C], R1, R).

tranH2C(start -> P, C) :- prop(P), C = start_clause([start], [P]).
tranH2C(Q -> P, C) :- is_dis(P), negation([Q], Q1),  wff2cnf(P, P1), P1 = [P2], append(Q1, P2, P3), C = true_clause([true], P3).
tranH2C([Q -> ^(*P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = exist_next_clause([Q], P2, I).
tranH2C([Q -> ^(?P),I], C) :- wff2cnf(P, P1), P1 = [P2], C = exist_future_clause([Q], P2, I).
tranH2C(Q -> ~(*P), C) :- wff2cnf(P, P1), P1 = [P2], C = global_next_clause([Q], P2).
tranH2C(Q -> ~(?P), C) :- wff2cnf(P, P1), P1 = [P2], C = global_future_clause([Q], P2).


tran2SNF([], Ind, N, V, []) :- V=[].
tran2SNF(L, Ind, N, V, R) :- tran2SNF_list(L, V1, Ind, N, IndM, NM, L1),  %Ind表示index的初始值0，IndM表示index的最大值（结束transform过程后的值）； N表示变量的初始值0，NM表示transform结束后引入的原子的个数-1.
	(L1 = L, R = L1, V = V1;
		tran2SNF(L1, IndM, NM, V2, R), append(V1, V2, V)).

tran2SNF_list([], V, Ind, N, Ind, N, []) :- V=[].
tran2SNF_list([H|T], V1, Ind, N, IndM, NM, L) :- transF(H, Ind, V2, N, IndM1, NM1, L1), 
	tran2SNF_list(T, V3, IndM1, NM1, IndM, NM, L3), append(V2, V3, V1), append(L1, L3, L4), sort(L4, L).
	

%transF(start -> P, Ind, V, Ind, IndM, IndM, C) :-  C = start_clause([start], [P]).
%transF(Q -> P, Ind, V, Ind, IndM, IndM, C) :- is_dis(P), negation([Q], Q1),  wff2cnf(P, P1), P1 = [P2], append(Q1, P2, P3), %C = true_clause([true], P3).
transF(Q -> (P1 & P2), Ind, V, N, IndM, NM, L) :- NM = N, IndM=Ind, L = [Q -> P1, Q -> P2], V=[].
transF(Q -> (P1 \/ P2), Ind, V, N, IndM, NM, L) :-  IndM=Ind,%/ 
	(is_dis(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_dis(P2), !, N2=N1, NM=N1, V3=[], L2=[];
		(N2 is N1 +1, NM=N2, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], L =[Q -> (P1 \/ P2)], V = [];  %/
				L = [L2, Q -> P1 \/ Y2], V = [Y2]); %/
		(L2 =[], L = [L1, Q -> Y1 \/P2], V = [Y1];  %/
			L = [L1, L2, Q -> Y1 \/ Y2], V =[Y1, Y2] %/
		)
	).
	
	
/*transF(Q -> ^(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind+1,
	(is_lit(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_lit(P2), !, N2=N1, V3=[], L2=[];
		(N2 is N1 +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], tran2U(Q -> ^(P1 $ P2), N, IndM, Vx, L), V = [Vx], NM is N +1;  
					tran2U(Q -> ^(P1 $ Y2), N2, IndM, Vx, R1), append([L2], R1, L), V = [Y2, Vx], NM is N2 +1); 
		(L2 =[], tran2U(Q -> ^(Y1 $ P2), N2, IndM, Vx, R2), append([L1], R2, L), V = [Y1, Vx], NM is N + 1;
			 NM is N2 + 1, string_concat('x', NM, XY3), string_to_atom(XY3, Y3), assert(prop(Y3)),
			L = [L1, L2,  Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), IndM], [Q -> ^(? Y2),IndM]], V =[Y1, Y2, Y3]  
		)
	).*/
	
transF(Q -> ^(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind+1,
	(is_lit(P2), !, N2=N, V3=[], L2=[];
		(N2 is N +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L2 =[], tran2U(Q -> ^(P1 $ P2), N2, IndM, Vx, L), V = [Vx], NM is N + 1;
			 NM is N2 + 1, tran2U(Q -> ^(P1 $ Y2), N2, IndM, Vx, R), append([L2], R, L), V = [Y2, Vx]
	).
	
/*transF([Q -> ^(P1 $ P2), I], Ind, V, N, IndM, NM, L) :-  IndM = Ind,
	(is_lit(P1), !, L1=[], N1=N, V2=[];
		(N1 is N +1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), V2=[Y1], L1=(Y1 -> P1))
	),
	(is_lit(P2), !, N2=N1, V3=[], L2=[];
		(N2 is N1 +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L1=[], (L2=[], tran2U(Q -> ^(P1 $ P2), N, I, Vx, L), V = [Vx], NM is N +1;  
					tran2U(Q -> ^(P1 $ Y2), N2, I, Vx, R1), append([L2], R1, L), V = [Y2, Vx], NM is N2 +1); 
		(L2 =[], tran2U(Q -> ^(Y1 $ P2), N2, I, Vx, R2), append([L1], R2, L), V = [Y1, Vx], NM is N + 1;
			 NM is N2 + 1, string_concat('x', NM, XY3), string_to_atom(XY3, Y3), assert(prop(Y3)),
			L = [L1, L2,  Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), I], [Q -> ^(? Y2),I]], V =[Y1, Y2, Y3]  
		)
	).*/
	
transF(Q -> ~(P1 $ P2), Ind, V, N, IndM, NM, L) :-   IndM is Ind,
	(is_lit(P2), !, N2=N, V3=[], L2=[];
		(N2 is N +1, string_concat('x', N2, XY2), string_to_atom(XY2, Y2), assert(prop(Y2)), V3=[Y2], L2=(Y2 -> P2))
	), 
	(L2 =[], tran2Uall(Q -> ~(P1 $ P2), N2, IndM, Vx, L), V = [Vx], NM is N + 1;
			 NM is N2 + 1, tran2Uall(Q -> ~(P1 $ Y2), N2, IndM, Vx, R), append([L2], R, L), V = [Y2, Vx]
	).
	
tran2U(Q -> ^(Y1 $ Y2), N, IndM, V, L) :- N1 is N+1, string_concat('x', N1, XY3), 
	string_to_atom(XY3, Y3), assert(prop(Y3)), V= Y3,
	L = [Q -> Y2 \/ Y3, Y3 -> Y1, [Y3 -> ^(*(Y2 \/ Y3)), IndM], [Q -> ^(? Y2),IndM]]. %/

tran2Uall(Q -> ~(Y1 $ Y2), N, IndM, V, L) :- N1 is N+1, string_concat('x', N1, XY3), 
	string_to_atom(XY3, Y3), assert(prop(Y3)), V= Y3,
	L = [Q -> Y2 \/ Y3, Y3 -> Y1, Y3 -> ~(*(Y2 \/ Y3)), Q -> ~(? Y2)]. %/	
	
	

transF(Q -> ^(@P), Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind+1,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, [Y1 -> ^(*Y1), IndM]].
/*transF([Q -> ^(@P),I], Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind+1,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, [Y1 -> ^(*Y1), IndM]].*/
	
transF(Q -> ~(@P), Ind, V, N, IndM, NM, L) :-  N1 is N+1, NM=N1, IndM is Ind,
	string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)),
	V=[Y1], L=[Q -> Y1, Y1 -> P, Y1 -> ^(*Y1)].
	
transF(Q -> ^(*P), Ind, V, N, IndM, NM, L) :- IndM is Ind +1,
	(is_dis(P), L = [[Q -> ^(*P), IndM]], NM is N, V=[];
		N1 is N+1, NM=N1,  string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(* Y1),IndM], Y1 -> P]
	).
/*transF([Q -> ^(*P), I], Ind, V, N, IndM, NM, L) :- IndM=Ind,
	(is_dis(P), L = [[Q -> ^(*P),I]];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(* Y1),I], Y1 -> P]
	).*/

transF(Q -> ~(*P), Ind, V, N, IndM, NM, L) :- IndM is Ind,
	(is_dis(P), L = [Q -> ~(*P)], NM is N, V=[];
		N1 is N+1, NM=N1,  string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[Q -> ~(* Y1), Y1 -> P]
	).
	
transF(Q -> ^(?P), Ind, V, N, IndM, NM, L) :- IndM is Ind+1, 
	(is_lit(P), L = [[Q -> ^(?P), IndM]], NM is N, V=[];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(? Y1), IndM], Y1 -> P]
	).
/*transF([Q -> ^(?P), I], Ind, V, N, IndM, NM, L) :- 
	(is_lit(P), IndM=Ind, L = [[Q -> ^(?P), I]];
		N1 is N+1, NM=N1, IndM is Ind+1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[[Q -> ^(? Y1), IndM], Y1 -> P]
	).*/

transF(Q -> ~(?P), Ind, V, N, IndM, NM, L) :- IndM is Ind, 
	(is_lit(P), L = [Q -> ~(?P)], NM is N, V=[];
		N1 is N+1, NM=N1, string_concat('x', N1, XY1), string_to_atom(XY1, Y1), assert(prop(Y1)), 
		V = [Y1], L =[Q -> ^(? Y1), Y1 -> P]
	).
	
	
transF(Q -> P, Ind, V, N, IndM, NM, L) :- IndM=Ind, is_lit(P), V =[], NM =N, L=[Q -> P].
transF(Q, Ind, V, N, IndM, NM, [Q]) :- NM =N, IndM=Ind, V = [].
	

%gain the atom of a formula
gain_prop(P & Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), 
	append(L1, L2, L).
gain_prop(P \/ Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), %/
	append(L1, L2, L).
gain_prop(P -> Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L).
gain_prop(^(@P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(-P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(^(P $ Q), L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L3), sort(L3, L).
gain_prop(^(*P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(^(?P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(@P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(P $ Q), L) :- gain_prop(P, L1), gain_prop(Q, L2), append(L1, L2, L3), sort(L3, L).
gain_prop(~(*P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(~(?P), L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(P, [P]) :-  atom(P), !, assert(prop(P)).

 
 %判断是否为文字
 is_lit(C) :- (prop(C); equall(-C, D), prop(D)).
 
 %判断是否是文字的吸取
 is_dis(C) :- is_lit(C).
 is_dis(C) :- C = (P \/ Q), %/
	(is_dis(P), is_dis(Q), !; !, fail).
 



%snfL2CTLF-------------------------------------end----------------------------------------------------	
	
	
	
	
	
	
	
	
	
/* dnf2wff(L,W) convert a DNF list to a formula */

dnf2wff([],false) :- !.
dnf2wff([[]],true) :- !.
dnf2wff([L], W) :- list2conjunct(L,W), !.
dnf2wff([L1|L2], W1 \/ W2) :- list2conjunct(L1, W1), dnf2wff(L2,W2).

/* cnf2wff(L,W) convert a CNF list to a formula */

cnf2wff([[]],false) :- !.
cnf2wff([],true) :- !.
cnf2wff([L], W) :- list2disjunct(L,W), !.
cnf2wff([L1|L2], W1 & W2) :- list2disjunct(L1, W1), cnf2wff(L2,W2).


/* list2conjunct(L,A): A is the conjunction of all formulas in L */

list2conjunct([P],P) :- !.
list2conjunct([P | L],P & W) :- list2conjunct(L,W).


/* list2disjunct(L,A): A is the disjunction of all formulas in L: A=false when
   L is empty */

list2disjunct(L, true) :- member(true,L), !.
list2disjunct(L, true) :- member(-P,L), member(P,L), !.
list2disjunct(L, W) :- sort(L,L1), delete(L1,false,L2), list2disj(L2,W), !.
list2disj([], false) :- !.
list2disj([P],P) :- !.
list2disj([P | L],P \/ W) :- list2disj(L,W).%/


/* wff2dnf transforms a wff to its disjunctive normal form in list format */

wff2dnf(P,[[P]]) :- prop(P), !.
wff2dnf(-P,[[-P]]) :- prop(P), !.
wff2dnf(P->Q, L) :- wff2dnf(-P\/Q, L).%/
wff2dnf(P<->Q, L) :- wff2dnf((P->Q)&(Q->P), L).
wff2dnf(P\/Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2), append(L1,L2,L).%/
wff2dnf(P&Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2),
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L).
wff2dnf(-P, L) :- wff2cnf(P,L1), negate(L1,L).


/* negate(L1,L): negate L1 in DNF (CNF) and make it into a CNF (DNF). */
negate([],[]) :- !.
negate([[]],[[]]) :- !.
negate(L1,L) :- bagof(X, Y^(member(Y, L1), negate_one_clause(Y,X)), L).

/* negate_one_clause(L1, L2): make all elements in L1 into its complement */
negate_one_clause(L1, L2) :- bagof(X, Y^(member(Y,L1), complement(Y,X)), L2).



%----------wff2cnf------and--------wff2dnf--------
wff2cnf(P, [[P]]) :- prop(P), !.
wff2cnf(-P, [[-P]]) :- prop(P), !.
wff2cnf(P->Q, L) :- wff2cnf(-P\/Q, L), !.%/
wff2cnf(P<->Q, L) :- wff2cnf((-P\/Q)&(-Q\/P), L), !.%/
wff2cnf(P&Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), append(L1,L2,L), !.
wff2cnf(P\/Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), %/
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L), !.
wff2cnf(-P, L) :- wff2dnf(P, L1), negate(L1, L), !.

/* wff2cnf(W,NewW) :- negation_inside(W,W1), wff2cnf0(W1,NewW).
*/
wff2cnf0(P, [[P]]) :- prop(P), !.
wff2cnf0(-P, [[-P]]) :- prop(P), !.
wff2cnf0(P&Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), union(L1,L2,L), !.
wff2cnf0(P\/Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), %/
    setof(X, Y^Z^(member(Y,L1), member(Z,L2), union(Y,Z,X)), L), !.
	
complement(true,false) :- !.
complement(false,true) :- !.
complement(P,-P) :- prop(P).
complement(-P,P) :- prop(P).
	
