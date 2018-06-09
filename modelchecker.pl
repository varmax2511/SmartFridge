% __________________________________________________
%
%             MODEL CHECKER (closed world assumption)
% __________________________________________________

% ===================================================
%
%  Team Details
%  -------------
%  UBIT Name: varunjai, snehameh
%  Person#: 50247176, 50245877
%
% ===================================================

% ==================================================
% A simple model
% ==================================================

model([tom1,sue1,mia1,sam1,
       egg1,egg2,egg3,
          chicken1,ham1,
            milk1,milk2,
              watermelon1,watermelon2,banana1,apple1,apple2,
                  sandwich1,sandwich2,
       container1,container2,container3,
       shelf1,shelf2,shelf3,
       box1,box2,box3,
       bowl1,
       fridge1,
       freezer1],
	  [
      % things
      [thing,[egg1,egg2,egg3,
              chicken1,ham1,
              milk1,milk2,
              watermelon1,watermelon2,banana1,apple1,apple2,
              sandwich1,sandwich2,
              container1,container2,container3,
              shelf1,shelf2,shelf3,
              box1,box2,box3,
              bowl1,
              fridge1,
              freezer1]
      ],
    
	   % persons
      [person,[tom1,sue1,mia1,sam1]],  
      
      % adjectives  
	  [red,[apple1,apple2,container1]],
      [blue,[box1,container3]],
      [white,[box2,container2]], 
      [yellow,[bowl1]],
      [green,[box3]], 
      [top,[shelf3]],	  
      [middle,[shelf1]],
      [bottom,[shelf2]],  
      [almond,[milk1]],
      [skim,[milk2]],  
	  
	  % containers
      [container,[container1,container2,container3]],
      [bowl,[bowl1]],  
      [box,[box1,box2,box3]], 
      [shelf,[shelf1,shelf2,shelf3]],
	  [fridge,[fridge1]],
      [freezer,[freezer1]],  
      
      % people
	  [tom,[tom1]],[sue,[sue1]],[mia,[mia1]],
	  [sam,[sam1]],
      
      % articles
	  [egg,[egg1,egg2,egg3]],
	  [chicken,[chicken1]],
	  [ham,[ham1]],
      [meat,[chicken1,ham1]],  
	  [milk,[milk1,milk2]],
      [banana,[banana1]],
      [apple,[apple1,apple2]],  
      [watermelon,[watermelon1,watermelon2]],
      [sandwich,[sandwich1,sandwich2]],  
     	  
	  % Relations
    
   
	  [drink,[
	         [tom1,milk1],
			 [mia1,milk1],
			 [sam1,milk2]]
			 ],
	  [drank,[
	         [tom1,milk1],
			 [mia1,milk1],
			 [sam1,milk2]]
			 ],		 
	  [in,[
	      [ham1,fridge1],
		  [chicken1,fridge1],
	      [egg1,fridge1],
		  [egg2,fridge1],
		  [egg3,fridge1],
	      [milk1,fridge1],
		  [milk2,fridge1],
		  [watermelon1,fridge1],
		  [watermelon2,fridge1],
		  [banana1,fridge1],
		  [apple1,fridge1],
		  [sandwich1,fridge1],
		  [container1,fridge1],
		  [container2,fridge1],
		  [container3,fridge1],
		  [shelf1,fridge1],
		  [shelf2,fridge1],
		  [shelf3,fridge1],
		  [box1,fridge1],
		  [box2,fridge1],
		  [box3,fridge1],
		  [bowl1,fridge1],
		  [freezer1,fridge1],
		  [egg1,box1],
          [egg2,box1],
          [egg3,box1],
          [ham1,box1],  
          [chicken1,box2],
          [apple1,box3],
          [egg1,container1],
		  [apple2,container1],
          [box2,freezer1],
          [banana1,container2],
		  [sandwich1,container3],
          [watermelon1,bowl1],
		  [container3,shelf3],
		  [container2,shelf2],
		  [ham1,sandwich2],
		  [chicken1,sandwich1]
		  ]],
     
      [contain,[
	           [fridge1,ham1],
		       [fridge1,chicken1],
	           [fridge1,egg1],
		       [fridge1,egg2],
		       [fridge1,egg3],
	           [fridge1,milk1],
		       [fridge1,milk2],
		       [fridge1,watermelon1],
		       [fridge1,watermelon2],
		       [fridge1,banana1],
		       [fridge1,apple1],
		       [fridge1,sandwich1],
		       [fridge1,container1],
		       [fridge1,container2],
		       [fridge1,container3],
		       [fridge1,shelf1],
		       [fridge1,shelf2],
		       [fridge1,shelf3],
		       [fridge1,box1],
		       [fridge1,box2],
		       [fridge1,box3],
		       [fridge1,bowl1],
		       [fridge1,freezer1],
                 [container1,egg1],
				 [container1,apple2],
                 [box1,ham1],
                 [box1,egg1],
                 [box1,egg3],
                 [box1,egg2],
                 [box2,chicken1],
                 [box3,apple1],
                 [freezer1,box2],
                 [container2,banana1],
				 [container3,sandwich1],
                 [bowl1,watermelon1],
				 [shelf3,container3],
		         [shelf2,container2],
				 [sandwich1,chicken1],
				 [sandwich2,ham1]
               ]],
	  [on,[
	      [container3,shelf3],
		  [container2,shelf2],
		  [container1,shelf1],
		  [bowl1,shelf1],
		  [box1,shelf3]
		  ]],
	   	  
      [belong,[
              [box3,tom1],
              [box2,sue1],
              [box1,mia1]
              ]]  
	  ]).


% ==================================================
% Function i
% Determines the value of a variableconstant in an assignment G
% ==================================================

i(Var,G,Value):- 
    var(Var),
    member([Var2,Value],G), 
    Var == Var2.   

i(C,_,Value):- 
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a PredicateRelation
% ==================================================

f(Symbol,Value):- 
   model(_,F),
    member([Symbol,ListOfValues],F), 
    member(Value,ListOfValues).  


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).


% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).

% ==================================================
% Sentence
% ==================================================
sat(G1,s(Formula,_),G3):- 
   sat(G1,Formula,G3).

% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value), 
   \+ ( ( sat(G1,exists(X,A),G2), 
          i(X,G2,Value2), 
		  \+(Value = Value2)) ).




% ==================================================
% Negation 
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).

% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2), 
  sat(G2,Formula2,G3). 



% ==================================================
% Disjunction
% ==================================================
sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% Handling cases like 
% Is there milk. Here g[[firdge]]g is always true. 
% ==================================================

sat(G,Predicate,G):-
   (Predicate = fridge);
   (Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value)).

% ==================================================
% Number
% ==================================================
sat(G1,two(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,2).

sat(G1,three(X,Formula),G1):-
   %findall(G,(sat(G1,exists(X,Formula),G),length(G3,X), X > 1),G3),
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,3).

sat(G1,four(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,4).

sat(G1,five(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,5).

sat(G1,six(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,6).

sat(G1,seven(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,7).

sat(G1,eight(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,8).

sat(G1,nine(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,9).

sat(G1,one(X,Formula),G1):-
   findall(G,(sat(G1,exists(X,Formula),G)),G3),
   length(G3,1).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).

% ============================================
% Model Checker
% ============================================


% helper methods
% get the last element of the list
last1([X],X).
last1([_|Z],X) :- last(Z,X).

% check if list is empty or not
%list_empty([]).
%list_not_empty([_|_]).

% concat
concat_list([],_).
concat_list([X],X).
concat_list([H1,H2|T],X):- atom_concat(H1,' ',H3),atom_concat(H3,H2,X),concat_list(T,X).  

% assign the label
label(X,X).

% iterate a list
listItr([],[]).

listItr(X,G):-
    last1(X,[_,V]),
    findType(V,G).
    
% find the given B in the model to find its type    
findType(B,G2):-
   findall(X,model(_,X),G),
   findall( V, (member(A, G), member([V,C], A),member(B,C),not(V=thing),not(V = person),not(V=meat)), G1),
   concat_list(G1,G2).


%
%   Model Checker
%

% for statements of type forall
modelchecker(s(forall(X,Formula),_),Evaluation):-
    (sat([],forall(X,Formula),G),
	list_empty(G),
    label(Evaluation,[true_in_the_model]),!);
    label(Evaluation,[not_true_in_the_model]),!.   

% for statements of type exists
modelchecker(s(Formula,_),Evaluation):-
    sat([],Formula,G),
	(list_not_empty(G),
    label(Evaluation,[true_in_the_model]),!);
    label(Evaluation,[not_true_in_the_model]),!.

% for ynq
modelchecker(ynq(Formula),Evaluation):-
    sat([],Formula,G),
	(nonvar(G),
    label(Evaluation,[yes_to_question])),!;
    label(Evaluation,[no_to_question]),!.

% for q
modelchecker(q(X,Formula),Evaluation):-
    findall(A,(sat([],exists(X,Formula),G),listItr(G,A)),G3),
    label(Evaluation,G3),!.







