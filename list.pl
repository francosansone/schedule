slist(S) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)).

head(S,H) :- slist(S) & [1,H] in S.

last(S,L) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)) &
  [N,L] in S.

add(S,E,T) :- 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)) &
  M is N + 1 &
  T = {[M,E] / S}.

front(S,T) :-
  S = {[N,X] / T} & 
  pfun(S) & 
  dom(S,D) &
  size(D,N) &
  subset(D,int(1,N)) &
  comp({[N,N]},T,{})
  or
  S = {} & T = {}.

tail(S,T) :-
  slist(S) &
  S = {[1,E] / U} & comp({[1,1]},U,{}) &
  T = ris([X,Y] in U, [K], true, [K,Y], K is X - 1)
  or
  S = {} & T = {}.


% List operators implemented with recursion
% Some of them (maybe all of them) can be written
% as {log} formulas but it needs to be extended

% {log} formula for concat
% concat(S,T,U) :-
%   list(S) &
%   list(T) &
%   size(S,N) &
%   un(S,ris([A,B] in T,[K],true,[K,B],K is A + N),U).

% concat(S,T,U)
concat(S,{},S) :- slist(S).
concat({},{X/Y},{X/Y}) :- slist({X/Y}) & X nin Y.
concat({[I1,X]/S},{[I2,Y]/T},U) :-
  [I1,X] nin S &
  slist({[I2,Y]/T}) & [I2,Y] nin T &
  pfun({[I1,X]/S}) & 
  dom({[I1,X]/S},D) &
  size(D,N) &
  subset(D,int(1,N)) &
  offset_list(N,T,T_offset) &
  I2_offset is I2 + N &
  U = {[I1,X], [I2_offset,Y] / U1} &
  [I1,X] nin U1 & 
  [I2_offset,Y] nin U1 & 
  un(S,T_offset,U1).

% filter(A,S,T)
% A is not constrained to be a set of integers
% however it can be done as follows
% A = ris(N in A, integer(N))
% or as follows
% subset(A,int(M,N))
% where M and N are the min and max limits of int
% I wouldn't be necessary because squash will
% forse them to be integers

filter(A,S,T) :- slist(S) & dres(A,S,R) & squash(R,T).


% extract(S,A,T)
extract(S,A,T) :- slist(S) & rres(S,A,R) & squash(R,T).


%%% squash(S,L): true if S is a set of ordered pairs whose first
%%% components are natural numbers >= 1, L is a list (set of
%%% orderd pairs) containing
%%% the elements Y, for all [X,Y] in S, and L is ordered according
%%% to the values of X (e.g., squash({[2,a],[7,b],[4,c]},L) ==>
%%% [a,c,b])

% math formula for squash 
% assuming S is a partial function whose domain
% is a subset of the integers
% squash(S) = T <=>
%   exists F:
%     F in [1,|S|] --> dom(S) & 
%     injective(F) & monotone(F) & 
%     T = F;S
% since F in [1,|S|] --> dom(S) & injective(F)
%       <=> F in [1,|S|] --> dom(S) & ran(F) = dom(S)
% then we have
% squash(S) = T <=>
%   exists F:
%     F in [1,|S|] --> dom(S) & ran(F) = dom(S) & 
%     monotone(F) & T = F;S
% and monotone(F)
%     <=> forall x1,x2 in dom(F): x1 < x2 ==> F(x1) < F(x2)
% which is equivalent to (F is a function)
%         forall (x1,y1),(x2,y2) in F: x1 < x2 ==> y1 < y2
% which in turn is equivalent to
%         F*F = {((x1,y1),(x2,y2)) in F*F | x1 < x2 ==> y1 < y2}
% then the final formula is
% squash(S) = T <=>
%   exists F:
%     F in [1,|S|] --> dom(S) & ran(F) = dom(S) & 
%     F*F = {((x1,y1),(x2,y2)) in F*F | x1 < x2 ==> y1 < y2} &
%     T = F;S
% then the {log} formula for squash is
% squash(S,T) :-
%   pfun(S) &
%   size(S,N) &
%   dom(S,DS)
%   pfun(F) & dom(F,DF) & subset(DF,int(1,N)) & size(DF,N) &
%   ran(F,DS) &
%   cp(F,F) = 
%         ris([[X1,Y1],[X2,Y2] in cp(F,F), X1 >= X2 or Y1 < Y2) &
%   comp(S,F,T)

% a recursive implementation of squash
squash({},{}).
squash({X/Rel},{Y/List}) :- 
   X nin Rel & Y nin List &
   pfun({X/Rel}) &
   dom({X/Rel},D) & 
   set_to_list(D,LD) & 
   prolog_call(sort(LD,SLD)) & 
   squash0({X/Rel},SLD,1,{Y/List}).

squash0(Rel,[],_,{}).
squash0(Rel,[N|List],1,LSet) :-
   integer(N) &
   [N,X] in Rel &
   LSet = {[1,X] / L} & [1,X] nin L &
   squash0(Rel,List,2,L).
squash0(Rel,[N|List],K,LSet) :-
   integer(N) &
   [N,X] in Rel &
   LSet = {[K,X] / L} & [1,X] nin L &
   K1 is K + 1 &
   squash0(Rel,List,K1,L).


% Auxiliary predicates

% set_to_list(S,L): true if S is a set and L is 
% a list containing all and only the elements of S, 
% WITHOUT REPETITIONS
set_to_list({},[]).          
set_to_list({X/Set},List) :- 
   X nin Set &
   List = [X|L] & 
   set_to_list(Set,L).

% offset_list(K,S,SO): adds an offset (K) to all 
% the first components of the ordered pairs of
% of a set of ordered pairs which happens to be
% a list (S) 
offset_list(_,{},{}).
offset_list(Offset,{[N,X]/S},SO) :-
  [N,X] nin S &
  K is Offset + N &
  SO = {[K,X] / SO1} &
  offset_list(Offset,S,SO1).


