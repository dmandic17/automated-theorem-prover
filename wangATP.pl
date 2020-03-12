:-op(700,xfy, seq).
:-op(650,xfy,imp).
:-op(600,xfy,or).
:-op(500,xfy,and).
:-op(450,fy,neg).
:- op(650,xfx,iff).


%this is what the program calls:
prove([X|Tail]):-
	prove1(X,0),
    prove(Tail).
prove(List):-
    not(List=[_|_]),
write('\nYes\n').
prove([_|_]):-
write('\nNo\n').


%or this one:
printprove(X):-
    prove1(X,1),
    nl,
    write('*****ALGORITHM FINISHED PROVING*****').
printprove(_):- nl,
write('*****Can\'t be proven*****').


%predicate to delete an element X from a list L.
del(X,[X|Tail],Tail).
del(X,[H|Tl1],[H|Tl2]):-
        del(X,Tl1,Tl2).

%predicate for equal:
equals(A,A).

%cnf rules:

prove1(L seq R, N):-
member(A iff B,L),
del(A iff B,L,NewL),
    ( (N > 0) *-> nl,
    write(N),
    write('. [CNF Rule] Eliminating iff operation from left.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(NewL), write(' seq ' ), write(R),
        N1 is N+1; N1 is N),
prove1([(A imp B) and (B imp A)|NewL] seq R, N1).

prove1(L seq R, N):-
member(A iff B,R),
del(A iff B,R,NewR),
    ( (N > 0) *-> nl,
    write(N),
    write('. [CNF Rule] Eliminating iff operation from right.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(L), write(' seq ' ), write(NewR),
        N1 is N+1; N1 is N),
prove1(L seq [(A imp B) and (B imp A)|NewR], N1).

prove1(L seq R, N):-
member(A imp B,L),
del(A imp B,L,NewL),
    ( (N > 0) *-> nl,
    write(N),
    write('. [CNF Rule] Eliminating imp operation from left.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(NewL), write(' seq ' ), write(R),
        N1 is N+1; N1 is N),
prove1([(neg A) or B|NewL] seq R, N1).

prove1(L seq R, N):-
member(A imp B,R),
del(A imp B,R,NewR),
    ( (N > 0) *-> nl,
    write(N),
    write('. [CNF Rule] Eliminating imp operation from right.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(L), write(' seq ' ), write(NewR),
        N1 is N+1; N1 is N),
prove1([A|L] seq [B|NewR], N1).


%negation elimination on left and right:
prove1(L seq R, N):-
member(neg X,L),
del(neg X,L,NewL),
    ( (N > 0) *-> nl,
    write(N),
    write('. [Negation Elimination] Eliminating negation because  '),
    write(' neg '), write(X), write(' exists '),
    write('on the left side.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(NewL), write(' seq ' ), write(R),
        N1 is N+1; N1 is N),
prove1(NewL seq [X|R], N1).

prove1(L seq R, N):-
member(neg X,R),
del(neg X,R,NewR),
    ( (N > 0) *-> nl,
    write(N),
    write('. [Negation Elimination] Eliminating negation because  '),
    write(' neg '), write(X), write(' exists '),
    write('on the right side.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(L), write(' seq ' ), write(NewR),
        N1 is N+1; N1 is N),
prove1([X|L] seq NewR, N1).

%non-branching rules for left and right:
prove1(L seq R, N):-
member(A and B,L),
del(A and B,L,NewL),
    ( (N > 0) *-> nl,
    write(N),
    write('. [Spliting Rule] Spliting into two parts beacuse ('),
    write(A), write(' and '), write(B),
    write(') is on the left side.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(NewL), write(' seq ' ), write(R),
        N1 is N+1; N1 is N),
prove1([A,B|NewL] seq R, N1),
write('here').

prove1(L seq R, N):-
member(A or B,R),
del(A or B,R,NewR),
    ( (N > 0) *-> nl,
    write(N),
    write('. [Spliting Rule] Spliting into two parts beacuse ('),
    write(A), write(' or '), write(B),
    write(') is on the right side.'),nl,
        write('---> '),write(L), write(' seq '), write(R), write('  ---->  '),
        write(L), write(' seq ' ), write(NewR),
        N1 is N+1; N1 is N),
prove1(L seq [A,B|NewR], N1).

%branching rules for left and right:
prove1(L seq R, N):-
member(A and B,R),
del(A and B,R,NewR),
    ( (N > 0) *-> nl,
    write(N),
    write('. [Branching Rule] Branching into two subtrees beacuse ('),
    write(A), write(' and '), write(B),
    write(') is on the right side.'),nl, write('---> '),
        write(L), write(' seq '), write(R), write('  ---->  '),
        write(L), write(' seq ' ), write( [A|NewR]),write(' AND '),
        write(L), write(' seq ' ), write( [B|NewR]),
        N1 is N+1; N1 is N),
prove1(L seq [A|NewR], N1),
prove1(L seq [B|NewR], N1).

prove1(L seq R, N):-
member(A or B,L),
del(A or B,L,NewL),
( (N > 0) *-> nl,
    write(N),
    write('. [Branching Rule] Branching into two subtrees beacuse ('),
    write(A), write(' or '), write(B),
    write(') is on the left side.'),
    nl, write('--->'), write(L), write(' seq '), write(R), write('  ---->  '),
        write([A|NewL]), write(' seq ' ), write(R),write('   AND   '),
        write([B|NewL]), write(' seq ' ), write(R),N1 is N+1; N1 is N),
prove1([A|NewL] seq R, N1),
prove1([B|NewL] seq R, N1).


%rule for id, this is where proving ends:
prove1(L seq R, N):-
member(X,L),
member(X,R),
    ( (N > 0) *-> nl,
    write(N),
    write('. [ID Rule] Done here because there is '),
    write(X),
    write(' on both sides.'),nl, write('--->'),
        write(L), write(' seq '), write(R); true).
