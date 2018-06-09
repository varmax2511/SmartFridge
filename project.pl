:- ['modelchecker.pl'].

% ====================================================
%
%  Team Details
%  -------------
%  UBIT Name: varunjai, snehameh
%  Person#: 50247176, 50245877
%
% =====================================================


% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
% 		1.1 Reading an input string and convert it to a tokenized list
% 		1.2 Processing tokenized list
% ===========================================================

chat:-
 repeat,
   readinput(Input),
   process(Input), 
  (Input = [bye| _] ),!.
  

% ===========================================================
% Read input:
% 1. Read char string from keyboard. 
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).
   

% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
	parse(Input,SemanticRepresentation),
	modelchecker(SemanticRepresentation,Evaluation),
	respond(Evaluation),!,
	nl,nl.
	
process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

%parse(Input, SemanticRepresentation):-
parse(Sentence,SemParse):-
        srparse([],Sentence,SemParse).
 
srparse([X],[],X).
  %numbervars(X,0,_),
  %write(X).

srparse([Z,Y,X|MoreStack],Words,SemParse):-
       rule(LHS,[X,Y,Z]),
       srparse([LHS|MoreStack],Words,SemParse).  
   
srparse([Y,X|MoreStack],Words,SemParse):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words,SemParse).

srparse([X|MoreStack],Words,SemParse):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words,SemParse).

srparse(Stack,[Word|Words],SemParse):-
        lex(X,Word),
        srparse([X|Stack],Words,SemParse).	
% ...


% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================

% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------

% determiners exist
lemma(a,dtexists).
lemma(an,dtexists).
lemma(some,dtexists).

% determiners
lemma(no,dtsp).
lemma(the,dtsp).

% determiners forall
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).

% nouns
lemma(container,n).
lemma(shelf,n).
lemma(box,n).
lemma(bowl,n).
lemma(sandwich,n).
lemma(egg,n).
lemma(meat,n).
lemma(ham,n).
lemma(chicken,n).
lemma(milk,n).
lemma(banana,n).
lemma(apple,n).
lemma(watermelon,n).
lemma(almond,n).
lemma(popsicle,n).
lemma(fridge,n).
lemma(freezer,n).


% proper nouns
lemma(sam,pn).
lemma(mia,pn).
lemma(tom,pn).
lemma(sue,pn).


% WH pronouns
lemma(what,whprt).
lemma(which,whprn).
lemma(who,whprp).

% adjectives
lemma(white,adj).
lemma(blue,adj).
lemma(green,adj).
lemma(red,adj).
lemma(yellow,adj).
lemma(top,adj).
lemma(middle,adj).
lemma(bottom,adj).
lemma(almond,adj).
lemma(empty,adj).


% BE
lemma(is,betv).
lemma(is,be).
lemma(was,be).
lemma(are,be).
lemma(will,be).
lemma(were,be).

% verbs transitive
lemma(eat,tv).
lemma(have,tv).
lemma(drank,tv).
lemma(drink,tv).
lemma(belong,tv).

% verbs transitive contain
lemma(has,ctv).
lemma(contain,ctv).


% verbs auxillary
lemma(do,aux).
lemma(did,aux).
lemma(does,aux).
lemma(will,aux).

% adjectives predicate
lemma(red,ap).
lemma(white,ap).
lemma(yellow,ap).
lemma(blue,ap).
lemma(green,adj).
lemma(empty,ap).

% verbs intransitive
lemma(drink,iv).

% ditransitive verb
lemma(put,dtv).

% adverbs
lemma(not,adv).

% prepositions
lemma(in,p).
lemma(at,p).
lemma(under,p).
lemma(of,p).
lemma(on,p).
lemma(to,p).
lemma(on,vacp).   
lemma(to,vacp).

% there
lemma(there,vacsp).

% verbs transitive inside
lemma(inside,inp).

% REL
lemma(who,rel).
lemma(what,rel).
lemma(which,rel).
lemma(that,rel).
lemma(this,rel).
lemma(these,rel).
lemma(those,rel).


% numbers
lemma(one,one).
lemma(two,two).
lemma(three,three).
lemma(four,four).
lemma(five,five).
lemma(six,six).
lemma(seven,seven).
lemma(eight,eight).
lemma(nine,nine).

 
% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------

% nouns
lex(n(X^P),Word):-
    atom_concat(Lemma,_,Word),
	lemma(Lemma,n),
	P=.. [Lemma,X].	
	
	
% proper name
lex(pn((Word^X)^X),Word):-
    lemma(Word,pn).	

% determiners for all	
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):-
		lemma(Word,dtforall).
		
% determiners for exist
lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Word):-
		lemma(Word,dtexists).

% Determiners for the
lex(dt((X^P)^(X^Q)^the(X,and(P,Q))),Word):-
	lemma(Word,dtsp),
	Word=the.	

% Determiners for the,no
lex(dt((X^P)^(X^Q)^not(X,and(P,Q))),Word):-
	lemma(Word,dtsp),
	Word=no.


%
% Numbers, supporting 1-9
%
% Determiners for one
lex(dt((X^P)^(X^Q)^one(X,and(P,Q))),Word):-
	lemma(Word,one).		

	
% Determiners for two
lex(dt((X^P)^(X^Q)^two(X,and(P,Q))),Word):-
	lemma(Word,two).		

% Determiners for three
lex(dt((X^P)^(X^Q)^three(X,and(P,Q))),Word):-
	lemma(Word,three).		

% Determiners for four
lex(dt((X^P)^(X^Q)^four(X,and(P,Q))),Word):-
	lemma(Word,four).		

% Determiners for five
lex(dt((X^P)^(X^Q)^five(X,and(P,Q))),Word):-
	lemma(Word,five).

% Determiners for six
lex(dt((X^P)^(X^Q)^six(X,and(P,Q))),Word):-
	lemma(Word,six).

% Determiners for seven
lex(dt((X^P)^(X^Q)^seven(X,and(P,Q))),Word):-
	lemma(Word,seven).

% Determiners for eight
lex(dt((X^P)^(X^Q)^eight(X,and(P,Q))),Word):-
	lemma(Word,eight).

% Determiners for nine
lex(dt((X^P)^(X^Q)^nine(X,and(P,Q))),Word):-
	lemma(Word,nine).	

	
% intransitive verb phrase, here our lemma will be the root word		
lex(iv(X^P,[]),Word):-
    atom_concat(Lemma,_,Word),
    lemma(Lemma,iv),
    P=.. [Lemma,X].	
	
% transitive verb
lex(tv(K^W^P,[]),Word):-
		atom_concat(Lemma,_,Word),
		lemma(Lemma,tv),
        P=.. [Lemma,K,W].

% ctv transitive verb, defining contain as special tag
lex(tv(K^W^P,[]),Word):-
		atom_concat(Lemma,_,Word),
		lemma(Lemma,ctv),
        P=.. [contain,K,W].

% inside special prepositions, rotate variables to match contain
lex(p(K^W^P,[]),Word):-
		lemma(Word,inp),
        P=.. [contain,W,K].
		
		
		
% ditransitive verb
lex(dtv(X^Y^Z^P,[]),Word):-
		atom_concat(Lemma,_,Word),
		lemma(Lemma,dtv),
        P=.. [Lemma,X,Y,Z].
				
        		
% adjectives
lex(adj((X^P)^X^and(P,Q)),Word):-
    lemma(Word,adj),
    Q=.. [Word,X].

% prepositions
lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word):-
    lemma(Word,p),
    Z=.. [Word,X,Y].	

		
% coordinates
%lex(P^Q^and(P,Q),Word):-
%    lemma(Word,coord).

%lex(P^Q^or(P,Q),Word):-
%    lemma(Word,coordor).


% who, what, which
lex(whpr((X^P)^q(X,and(person(X),P))),Word):-
		lemma(Word,whprp).
lex(whpr((X^P)^q(X,and(thing(X),P))),Word):-
		lemma(Word,whprt).		
lex(whprn((X^Q)^(X^P)^q(X,and(Q,P))),Word):-
		lemma(Word,whprn).
		

% vacous prepositions, no schema
lex(p,Word):-
    lemma(Word,vacp).
    	
% aux, no schema	
lex(Y,Word):-
    lemma(Word,Y),
	Y=aux.
	
% relative clauses, no schema	
lex(Y,Word):-
    lemma(Word,Y),
	Y=rel.	
	
% be, no schema	
lex(Y,Word):-
    lemma(Word,Y),
	Y=be.	
	
% vacsp, no schema	
lex(Y,Word):-
    lemma(Word,Y),
	Y=vacsp.
	

% adjective predicates, AP
lex(ap(X^P),Word):-
    lemma(Word,ap),	
	P=.. [Word,X].

% adverbs, handling not	
lex(adv(X^P),Word):-
    lemma(Word,adv),
    P=.. [Word,X].	



% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

% Yes-no question
rule(Y,[whpr(X^Y),vp(X,[])]).
rule(ynq(Y),[aux,np(X^Y),vp(X,[])]).
rule(Z,[whpr((X^Y)^Z),inv_s(Y,[X])]).
rule(whpr(Z),[whprn(Y^Z),n(Y)]).

% inv_s
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).

% be rules
rule(ynq(Y),[be,np(X^Y),ap(X)]).
rule(ynq(Y),[be,np(X^Y),pp(X,[])]).
rule(ynq(Y),[be,np((_^fridge)^Y)]).
rule(be,[be,vacsp]).


% adverbs
rule(adv(X),[aux,adv(X)]).

% sentence rules
rule(s(Y,WH),[np(X^Y),vp(X,WH)]).
%rule(s(Y,WH),[np(X^Y),vp(X,WH)]).


% np rules
rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).
rule(np(X^Y),[adj(X^Z),pp(Z^Y)]).
%rule(np(A^B),[adj(A^C),pp(C^B)]).

% rule to handle NP -> N. Add a some determiner
rule(np((X^Y)^exists(X,and(P,Y))),[n(X^P)]).

% n rules   
rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
rule(n(X),[adj(Y^X),n(Y)]).

% verb phrase rules
rule(vp(X,WH),[iv(X,WH)]).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
%rule(vp(A^B,[]),[tv(A^C,[]),pp(C^B)]).
rule(vp(X^Y,[]),[tv(X^Z,[]),pp(Z^Y)]).
rule(vp(X^K,[]),[be(X^Y),pp(Y^K)]).
rule(vp(X),[be,pp(X)]).
rule(vp(Y,WH),[adv(X^Y),vp(X,WH)]).

% vp -> dtv np pp
rule(vp(X^A,[]),[dtv(X^Y^Z^W,[]),np((Y^B)^A),ppvac((Z^W)^B)]).

% whq conversions
rule(iv(X^Z,[Y]),[tv(X^Y^Z,[])]).
rule(tv(Y^Z,[X]),[tv(X^Y^Z,[])]).


% pp rules
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).
rule(pp(X^K,[]),[p(X^Y,[]),np(Y^K)]).
rule(ppvac(X),[p,np(X)]).


% relative clause
rule(rc(X,[]),[rel,vp(X,[])]).
rule(rc(Z,[X]),[rel,vp(Z,[X])]).
rule(rc(X,[Y]),[rel,s(X,[Y])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).




% ...



% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

	
% model(...,...)

% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% helper method to check if list is empty or not
list_empty([]).
list_not_empty([_|_]).

% print the elements of a list
print_list([]).
print_list([H|T]):-
     write(H),write(','),
	 print_list(T).

% Declarative true in the model
respond(Evaluation) :- 
		Evaluation = [true_in_the_model], 
		write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :- 
		Evaluation = [not_true_in_the_model],  
		write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :- 
		Evaluation = [yes_to_question],			
		write('yes').

% Yes-No interrogative false in the model		
respond(Evaluation) :- 
		Evaluation = [no_to_question], 			
		write('no').

% wh-interrogative true in the model
respond(Evaluation) :-
        list_not_empty(Evaluation), 
		print_list(Evaluation).		

% wh-interrogative false in the model
respond(Evaluation) :- 
        list_empty(Evaluation), 
		write('No idea').				

