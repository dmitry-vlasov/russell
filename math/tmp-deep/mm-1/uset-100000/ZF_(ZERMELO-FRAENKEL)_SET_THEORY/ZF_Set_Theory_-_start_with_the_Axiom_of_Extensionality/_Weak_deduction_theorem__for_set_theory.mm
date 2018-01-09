$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_empty_set.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           "Weak deduction theorem" for set theory

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In a Hilbert system of logic (which consists of a set of axioms, modus
  ponens, and the generalization rule), converting a deduction to a proof using
  the Deduction Theorem (taught in introductory logic books) involves an
  exponential increase of the number of steps as hypotheses are successively
  eliminated.  Here is a trick that is not as general as the Deduction Theorem
  but requires only a linear increase in the number of steps.

  The general problem:  We want to convert a deduction
    P |- Q
  into a proof of the theorem
    |- P -> Q
  i.e. we want to eliminate the hypothesis P.  Normally this is done using the
  Deduction (meta)Theorem, which looks at the microscopic steps of the
  deduction and usually doubles or triples the number of these microscopic
  steps for each hypothesis that is eliminated.  We will look at a special case
  of this problem, without appealing to the Deduction Theorem.

  We assume ZF with class notation.  A and B are arbitrary (possibly
  proper) classes.  P, Q, R, S and T are wffs.

  We define the conditional operator, if(P,A,B), as follows:
    if(P,A,B) =def= { x | (x \in A & P) v (x \in B & -. P) }
  (where x does not occur in A, B, or P).

  Lemma 1.
    A = if(P,A,B) -> (P <-> R), B = if(P,A,B) -> (S <-> R), S |- R
  Proof:  Logic and Axiom of Extensionality.

  Lemma 2.
    A = if(P,A,B) -> (Q <-> T), T |- P -> Q
  Proof:  Logic and Axiom of Extensionality.

  Here's a simple example that illustrates how it works.  Suppose we have
  a deduction
    Ord A |- Tr A
  which means, "Assume A is an ordinal class.  Then A is a transitive class."
  Note that A is a class variable that may be substituted with any class
  expression, so this is really a deduction scheme.

  We want to convert this to a proof of the theorem (scheme)
    |- Ord A -> Tr A.

  The catch is that we must be able to prove "Ord A" for at least one
  object A (and this is what makes it weaker than the ordinary Deduction
  Theorem).  However, it is easy to prove |- Ord 0 (the empty set is
  ordinal).  (For a typical textbook "theorem," i.e. deduction, there is
  usually at least one object satisfying each hypothesis, otherwise the
  theorem would not be very useful.  We can always go back to the standard
  Deduction Theorem for those hypotheses where this is not the case.)
  Continuing with the example:

  Equality axioms (and Extensionality) yield
    |- A = if(Ord A, A, 0) -> (Ord A <-> Ord if(Ord A, A, 0))  (1)
    |- 0 = if(Ord A, A, 0) -> (Ord 0 <-> Ord if(Ord A, A, 0))  (2)
  From (1), (2) and |- Ord 0, Lemma 1 yields
    |- Ord if(Ord A, A, 0)                                       (3)
  From (3) and substituting if(Ord A, A, 0) for
  A in the original deduction,
    |- Tr if(Ord A, A, 0)                                        (4)
  Equality axioms (and Extensionality) yield
    |- A = if(Ord A, A, 0) -> (Tr A <-> Tr if(Ord A, A, 0))    (5)
  From (4) and (5), Lemma 2 yields
    |- Ord A -> Tr A                                               (Q.E.D.)

$)
$( These lemmas are used to convert hypotheses into antecedents,
     when there is at least one class making the hypothesis true. $)
$( Declare new constant symbols. $)
$c if  $.
$( Conditional operator (was "ded" for "deduction class"). $)
$( Extend class notation to include the conditional operator.  See ~ df-if
     for a description.  (In older databases this was denoted "ded".) $)
${
	fcif_0 $f wff ph $.
	fcif_1 $f class A $.
	fcif_2 $f class B $.
	cif $a class if ( ph , A , B ) $.
$}
$( Define the conditional operator.  Read ` if ( ph , A , B ) ` as "if
       ` ph ` then ` A ` else ` B ` ."  See ~ iftrue and ~ iffalse for its
       values.  In mathematical literature, this operator is rarely defined
       formally but is implicit in informal definitions such as "let f(x)=0 if
       x=0 and 1/x otherwise."  (In older versions of this database, this
       operator was denoted "ded" and called the "deduction class.")

       An important use for us is in conjunction with the weak deduction
       theorem, which converts a hypothesis into an antecedent.  In that role,
       ` A ` is a class variable in the hypothesis and ` B ` is a class
       (usually a constant) that makes the hypothesis true when it is
       substituted for ` A ` .  See ~ dedth for the main part of the weak
       deduction theorem, ~ elimhyp to eliminate a hypothesis, and ~ keephyp to
       keep a hypothesis.  See the Deduction Theorem link on the Metamath Proof
       Explorer Home Page for a description of the weak deduction theorem.
       (Contributed by NM, 15-May-1999.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	fdf-if_0 $f wff ph $.
	fdf-if_1 $f set x $.
	fdf-if_2 $f class A $.
	fdf-if_3 $f class B $.
	df-if $a |- if ( ph , A , B ) = { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) } $.
$}
$( An alternate definition of the conditional operator ~ df-if with one
       fewer connectives (but probably less intuitive to understand).
       (Contributed by NM, 30-Jan-2006.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	fdfif2_0 $f wff ph $.
	fdfif2_1 $f set x $.
	fdfif2_2 $f class A $.
	fdfif2_3 $f class B $.
	dfif2 $p |- if ( ph , A , B ) = { x | ( ( x e. B -> ph ) -> ( x e. A /\ ph ) ) } $= fdfif2_0 fdfif2_2 fdfif2_3 cif fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa wo fdfif2_1 cab fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wi fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa wi fdfif2_1 cab fdfif2_0 fdfif2_1 fdfif2_2 fdfif2_3 df-if fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa wo fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wi fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa wi fdfif2_1 fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa wo fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa wn fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa wi fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa wo fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wi fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa wi fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa df-or fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa orcom fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wi fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 wn wa wn fdfif2_1 sup_set_class fdfif2_2 wcel fdfif2_0 wa fdfif2_1 sup_set_class fdfif2_3 wcel fdfif2_0 iman imbi1i 3bitr4i abbii eqtri $.
$}
$( An alternate definition of the conditional operator ~ df-if as a simple
       class abstraction.  (Contributed by Mario Carneiro, 8-Sep-2013.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	fdfif6_0 $f wff ph $.
	fdfif6_1 $f set x $.
	fdfif6_2 $f class A $.
	fdfif6_3 $f class B $.
	dfif6 $p |- if ( ph , A , B ) = ( { x e. A | ph } u. { x e. B | -. ph } ) $= fdfif6_1 sup_set_class fdfif6_2 wcel fdfif6_0 wa fdfif6_1 cab fdfif6_1 sup_set_class fdfif6_3 wcel fdfif6_0 wn wa fdfif6_1 cab cun fdfif6_1 sup_set_class fdfif6_2 wcel fdfif6_0 wa fdfif6_1 sup_set_class fdfif6_3 wcel fdfif6_0 wn wa wo fdfif6_1 cab fdfif6_0 fdfif6_1 fdfif6_2 crab fdfif6_0 wn fdfif6_1 fdfif6_3 crab cun fdfif6_0 fdfif6_2 fdfif6_3 cif fdfif6_1 sup_set_class fdfif6_2 wcel fdfif6_0 wa fdfif6_1 sup_set_class fdfif6_3 wcel fdfif6_0 wn wa fdfif6_1 unab fdfif6_0 fdfif6_1 fdfif6_2 crab fdfif6_1 sup_set_class fdfif6_2 wcel fdfif6_0 wa fdfif6_1 cab fdfif6_0 wn fdfif6_1 fdfif6_3 crab fdfif6_1 sup_set_class fdfif6_3 wcel fdfif6_0 wn wa fdfif6_1 cab fdfif6_0 fdfif6_1 fdfif6_2 df-rab fdfif6_0 wn fdfif6_1 fdfif6_3 df-rab uneq12i fdfif6_0 fdfif6_1 fdfif6_2 fdfif6_3 df-if 3eqtr4ri $.
$}
$( Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	$d x C $.
	iifeq1_0 $f set x $.
	fifeq1_0 $f wff ph $.
	fifeq1_1 $f class A $.
	fifeq1_2 $f class B $.
	fifeq1_3 $f class C $.
	ifeq1 $p |- ( A = B -> if ( ph , A , C ) = if ( ph , B , C ) ) $= fifeq1_1 fifeq1_2 wceq fifeq1_0 iifeq1_0 fifeq1_1 crab fifeq1_0 wn iifeq1_0 fifeq1_3 crab cun fifeq1_0 iifeq1_0 fifeq1_2 crab fifeq1_0 wn iifeq1_0 fifeq1_3 crab cun fifeq1_0 fifeq1_1 fifeq1_3 cif fifeq1_0 fifeq1_2 fifeq1_3 cif fifeq1_1 fifeq1_2 wceq fifeq1_0 iifeq1_0 fifeq1_1 crab fifeq1_0 iifeq1_0 fifeq1_2 crab fifeq1_0 wn iifeq1_0 fifeq1_3 crab fifeq1_0 iifeq1_0 fifeq1_1 fifeq1_2 rabeq uneq1d fifeq1_0 iifeq1_0 fifeq1_1 fifeq1_3 dfif6 fifeq1_0 iifeq1_0 fifeq1_2 fifeq1_3 dfif6 3eqtr4g $.
$}
$( Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	$d x C $.
	iifeq2_0 $f set x $.
	fifeq2_0 $f wff ph $.
	fifeq2_1 $f class A $.
	fifeq2_2 $f class B $.
	fifeq2_3 $f class C $.
	ifeq2 $p |- ( A = B -> if ( ph , C , A ) = if ( ph , C , B ) ) $= fifeq2_1 fifeq2_2 wceq fifeq2_0 iifeq2_0 fifeq2_3 crab fifeq2_0 wn iifeq2_0 fifeq2_1 crab cun fifeq2_0 iifeq2_0 fifeq2_3 crab fifeq2_0 wn iifeq2_0 fifeq2_2 crab cun fifeq2_0 fifeq2_3 fifeq2_1 cif fifeq2_0 fifeq2_3 fifeq2_2 cif fifeq2_1 fifeq2_2 wceq fifeq2_0 wn iifeq2_0 fifeq2_1 crab fifeq2_0 wn iifeq2_0 fifeq2_2 crab fifeq2_0 iifeq2_0 fifeq2_3 crab fifeq2_0 wn iifeq2_0 fifeq2_1 fifeq2_2 rabeq uneq2d fifeq2_0 iifeq2_0 fifeq2_3 fifeq2_1 dfif6 fifeq2_0 iifeq2_0 fifeq2_3 fifeq2_2 dfif6 3eqtr4g $.
$}
$( Value of the conditional operator when its first argument is true.
       (Contributed by NM, 15-May-1999.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	iiftrue_0 $f set x $.
	fiftrue_0 $f wff ph $.
	fiftrue_1 $f class A $.
	fiftrue_2 $f class B $.
	iftrue $p |- ( ph -> if ( ph , A , B ) = A ) $= fiftrue_0 fiftrue_1 iiftrue_0 sup_set_class fiftrue_2 wcel fiftrue_0 wi iiftrue_0 sup_set_class fiftrue_1 wcel fiftrue_0 wa wi iiftrue_0 cab fiftrue_0 fiftrue_1 fiftrue_2 cif fiftrue_0 iiftrue_0 sup_set_class fiftrue_2 wcel fiftrue_0 wi iiftrue_0 sup_set_class fiftrue_1 wcel fiftrue_0 wa wi iiftrue_0 fiftrue_1 fiftrue_0 iiftrue_0 sup_set_class fiftrue_1 wcel iiftrue_0 sup_set_class fiftrue_2 wcel dedlem0a abbi2dv fiftrue_0 iiftrue_0 fiftrue_1 fiftrue_2 dfif2 syl6reqr $.
$}
$( Value of the conditional operator when its first argument is false.
       (Contributed by NM, 14-Aug-1999.) $)
${
	$d x ph $.
	$d x A $.
	$d x B $.
	iiffalse_0 $f set x $.
	fiffalse_0 $f wff ph $.
	fiffalse_1 $f class A $.
	fiffalse_2 $f class B $.
	iffalse $p |- ( -. ph -> if ( ph , A , B ) = B ) $= fiffalse_0 wn fiffalse_2 iiffalse_0 sup_set_class fiffalse_1 wcel fiffalse_0 wa iiffalse_0 sup_set_class fiffalse_2 wcel fiffalse_0 wn wa wo iiffalse_0 cab fiffalse_0 fiffalse_1 fiffalse_2 cif fiffalse_0 wn iiffalse_0 sup_set_class fiffalse_1 wcel fiffalse_0 wa iiffalse_0 sup_set_class fiffalse_2 wcel fiffalse_0 wn wa wo iiffalse_0 fiffalse_2 fiffalse_0 iiffalse_0 sup_set_class fiffalse_1 wcel iiffalse_0 sup_set_class fiffalse_2 wcel dedlemb abbi2dv fiffalse_0 iiffalse_0 fiffalse_1 fiffalse_2 df-if syl6reqr $.
$}
$( When values are unequal, but an "if" condition checks if they are equal,
     then the "false" branch results.  This is a simple utility to provide a
     slight shortening and simplification of proofs vs. applying ~ iffalse
     directly in this case.  It happens, e.g., in ~ oevn0 .  (Contributed by
     David A. Wheeler, 15-May-2015.) $)
${
	fifnefalse_0 $f class A $.
	fifnefalse_1 $f class B $.
	fifnefalse_2 $f class C $.
	fifnefalse_3 $f class D $.
	ifnefalse $p |- ( A =/= B -> if ( A = B , C , D ) = D ) $= fifnefalse_0 fifnefalse_1 wne fifnefalse_0 fifnefalse_1 wceq wn fifnefalse_0 fifnefalse_1 wceq fifnefalse_2 fifnefalse_3 cif fifnefalse_3 wceq fifnefalse_0 fifnefalse_1 df-ne fifnefalse_0 fifnefalse_1 wceq fifnefalse_2 fifnefalse_3 iffalse sylbi $.
$}
$( Distribute a function over an if-clause.  (Contributed by Mario
       Carneiro, 14-Aug-2013.) $)
${
	fifsb_0 $f wff ph $.
	fifsb_1 $f class A $.
	fifsb_2 $f class B $.
	fifsb_3 $f class C $.
	fifsb_4 $f class D $.
	fifsb_5 $f class E $.
	eifsb_0 $e |- ( if ( ph , A , B ) = A -> C = D ) $.
	eifsb_1 $e |- ( if ( ph , A , B ) = B -> C = E ) $.
	ifsb $p |- C = if ( ph , D , E ) $= fifsb_0 fifsb_3 fifsb_0 fifsb_4 fifsb_5 cif wceq fifsb_0 fifsb_3 fifsb_4 fifsb_0 fifsb_4 fifsb_5 cif fifsb_0 fifsb_0 fifsb_1 fifsb_2 cif fifsb_1 wceq fifsb_3 fifsb_4 wceq fifsb_0 fifsb_1 fifsb_2 iftrue eifsb_0 syl fifsb_0 fifsb_4 fifsb_5 iftrue eqtr4d fifsb_0 wn fifsb_3 fifsb_5 fifsb_0 fifsb_4 fifsb_5 cif fifsb_0 wn fifsb_0 fifsb_1 fifsb_2 cif fifsb_2 wceq fifsb_3 fifsb_5 wceq fifsb_0 fifsb_1 fifsb_2 iffalse eifsb_1 syl fifsb_0 fifsb_4 fifsb_5 iffalse eqtr4d pm2.61i $.
$}
$( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
${
	$d y A $.
	$d y B $.
	$d x y ph $.
	idfif3_0 $f set y $.
	fdfif3_0 $f wff ph $.
	fdfif3_1 $f set x $.
	fdfif3_2 $f class A $.
	fdfif3_3 $f class B $.
	fdfif3_4 $f class C $.
	edfif3_0 $e |- C = { x | ph } $.
	dfif3 $p |- if ( ph , A , B ) = ( ( A i^i C ) u. ( B i^i ( _V \ C ) ) ) $= fdfif3_0 fdfif3_2 fdfif3_3 cif fdfif3_0 idfif3_0 fdfif3_2 crab fdfif3_0 wn idfif3_0 fdfif3_3 crab cun fdfif3_2 fdfif3_4 cin fdfif3_3 cvv fdfif3_4 cdif cin cun fdfif3_0 idfif3_0 fdfif3_2 fdfif3_3 dfif6 fdfif3_2 fdfif3_4 cin fdfif3_0 idfif3_0 fdfif3_2 crab fdfif3_3 cvv fdfif3_4 cdif cin fdfif3_0 wn idfif3_0 fdfif3_3 crab fdfif3_2 fdfif3_4 cin fdfif3_2 fdfif3_0 idfif3_0 cab cin fdfif3_0 idfif3_0 fdfif3_2 crab fdfif3_4 fdfif3_0 idfif3_0 cab fdfif3_2 fdfif3_4 fdfif3_0 fdfif3_1 cab fdfif3_0 idfif3_0 cab edfif3_0 fdfif3_0 fdfif3_0 fdfif3_1 idfif3_0 fdfif3_1 sup_set_class idfif3_0 sup_set_class wceq fdfif3_0 biidd cbvabv eqtri ineq2i fdfif3_0 idfif3_0 fdfif3_2 dfrab3 eqtr4i fdfif3_0 wn idfif3_0 fdfif3_3 crab fdfif3_3 fdfif3_0 wn idfif3_0 cab cin fdfif3_3 cvv fdfif3_4 cdif cin fdfif3_0 wn idfif3_0 fdfif3_3 dfrab3 fdfif3_0 wn idfif3_0 cab cvv fdfif3_4 cdif fdfif3_3 fdfif3_0 wn idfif3_0 cab cvv fdfif3_0 idfif3_0 cab cdif cvv fdfif3_4 cdif fdfif3_0 idfif3_0 notab fdfif3_4 fdfif3_0 idfif3_0 cab cvv fdfif3_4 fdfif3_0 fdfif3_1 cab fdfif3_0 idfif3_0 cab edfif3_0 fdfif3_0 fdfif3_0 fdfif3_1 idfif3_0 fdfif3_1 sup_set_class idfif3_0 sup_set_class wceq fdfif3_0 biidd cbvabv eqtri difeq2i eqtr4i ineq2i eqtr2i uneq12i eqtr4i $.
$}
$( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.) $)
${
	$d x ph $.
	fdfif4_0 $f wff ph $.
	fdfif4_1 $f set x $.
	fdfif4_2 $f class A $.
	fdfif4_3 $f class B $.
	fdfif4_4 $f class C $.
	edfif4_0 $e |- C = { x | ph } $.
	dfif4 $p |- if ( ph , A , B ) = ( ( A u. B ) i^i ( ( A u. ( _V \ C ) ) i^i ( B u. C ) ) ) $= fdfif4_0 fdfif4_2 fdfif4_3 cif fdfif4_2 fdfif4_4 cin fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_2 fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif cin cun cin fdfif4_2 fdfif4_3 cun fdfif4_2 cvv fdfif4_4 cdif cun fdfif4_3 fdfif4_4 cun cin cin fdfif4_0 fdfif4_1 fdfif4_2 fdfif4_3 fdfif4_4 edfif4_0 dfif3 fdfif4_2 fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif cin undir fdfif4_2 fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif cin cun cin fdfif4_2 fdfif4_3 cun fdfif4_2 cvv fdfif4_4 cdif cun cin fdfif4_3 fdfif4_4 cun cin fdfif4_2 fdfif4_3 cun fdfif4_2 cvv fdfif4_4 cdif cun fdfif4_3 fdfif4_4 cun cin cin fdfif4_2 fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_2 fdfif4_3 cun fdfif4_2 cvv fdfif4_4 cdif cun cin fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_3 fdfif4_4 cun fdfif4_2 fdfif4_3 cvv fdfif4_4 cdif undi fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif cin cun fdfif4_4 fdfif4_3 cun fdfif4_4 cvv fdfif4_4 cdif cun cin fdfif4_3 fdfif4_4 cun cvv cin fdfif4_3 fdfif4_4 cun fdfif4_4 fdfif4_3 cvv fdfif4_4 cdif undi fdfif4_4 fdfif4_3 cun fdfif4_3 fdfif4_4 cun fdfif4_4 cvv fdfif4_4 cdif cun cvv fdfif4_4 fdfif4_3 uncom fdfif4_4 undifv ineq12i fdfif4_3 fdfif4_4 cun inv1 3eqtri ineq12i fdfif4_2 fdfif4_3 cun fdfif4_2 cvv fdfif4_4 cdif cun fdfif4_3 fdfif4_4 cun inass eqtri 3eqtri $.
$}
$( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false (see also
       ~ abvor0 ).  (Contributed by G&eacute;rard Lang, 18-Aug-2013.) $)
${
	$d x ph $.
	fdfif5_0 $f wff ph $.
	fdfif5_1 $f set x $.
	fdfif5_2 $f class A $.
	fdfif5_3 $f class B $.
	fdfif5_4 $f class C $.
	edfif5_0 $e |- C = { x | ph } $.
	dfif5 $p |- if ( ph , A , B ) = ( ( A i^i B ) u. ( ( ( A \ B ) i^i C ) u. ( ( B \ A ) i^i ( _V \ C ) ) ) ) $= fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun fdfif5_3 fdfif5_4 cun cin cin fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 cun cin cin fdfif5_0 fdfif5_2 fdfif5_3 cif fdfif5_2 fdfif5_3 cin fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun fdfif5_3 fdfif5_4 cun inindi fdfif5_0 fdfif5_1 fdfif5_2 fdfif5_3 fdfif5_4 edfif5_0 dfif4 fdfif5_2 fdfif5_3 cin fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun cin fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 cun cin cin fdfif5_2 fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun undir fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 cun cin fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_2 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_2 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_2 cun fdfif5_3 cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_2 cun fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin fdfif5_2 unidm uneq1i fdfif5_2 fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin unass fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif undi 3eqtr3ri fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_2 fdfif5_2 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_2 fdfif5_2 fdfif5_3 cdif cun fdfif5_2 fdfif5_4 cun cin fdfif5_2 fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 undi fdfif5_2 fdfif5_2 fdfif5_3 cdif cun fdfif5_2 fdfif5_4 cun cin fdfif5_2 fdfif5_2 fdfif5_4 cun cin fdfif5_2 fdfif5_2 fdfif5_2 fdfif5_3 cdif cun fdfif5_2 fdfif5_2 fdfif5_4 cun fdfif5_2 fdfif5_3 undifabs ineq1i fdfif5_2 fdfif5_4 inabs eqtri eqtri fdfif5_2 fdfif5_3 fdfif5_2 cdif cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun cin fdfif5_2 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_3 fdfif5_2 cdif cun fdfif5_2 fdfif5_3 cun fdfif5_2 cvv fdfif5_4 cdif cun fdfif5_2 fdfif5_3 undif2 ineq1i fdfif5_2 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif undi fdfif5_2 fdfif5_3 cvv fdfif5_4 cdif undi 3eqtr4i uneq12i eqtr4i fdfif5_2 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin unundi eqtr4i fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_3 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 cun cin fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 cun fdfif5_2 fdfif5_4 cin fdfif5_3 fdfif5_3 cun cun fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_3 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun cun fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_2 fdfif5_4 cin fdfif5_3 fdfif5_3 unass fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_3 fdfif5_3 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 fdfif5_2 fdfif5_3 cdif cun fdfif5_3 fdfif5_4 cun cin fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin cun fdfif5_3 fdfif5_2 fdfif5_4 cin cun fdfif5_3 fdfif5_2 cun fdfif5_3 fdfif5_4 cun cin fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 fdfif5_2 fdfif5_3 cdif cun fdfif5_3 fdfif5_4 cun cin fdfif5_3 fdfif5_2 fdfif5_4 undi fdfif5_2 fdfif5_4 cin fdfif5_3 uncom fdfif5_3 fdfif5_2 fdfif5_3 cdif cun fdfif5_3 fdfif5_2 cun fdfif5_3 fdfif5_4 cun fdfif5_3 fdfif5_2 undif2 ineq1i 3eqtr4i fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 undi eqtr4i fdfif5_3 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin cun fdfif5_3 fdfif5_3 fdfif5_2 cdif cun fdfif5_3 cvv fdfif5_4 cdif cun cin fdfif5_3 fdfif5_3 cvv fdfif5_4 cdif cun cin fdfif5_3 fdfif5_3 fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif undi fdfif5_3 fdfif5_3 fdfif5_2 cdif cun fdfif5_3 fdfif5_3 cvv fdfif5_4 cdif cun fdfif5_3 fdfif5_2 undifabs ineq1i fdfif5_3 cvv fdfif5_4 cdif inabs 3eqtrri uneq12i fdfif5_3 fdfif5_3 cun fdfif5_3 fdfif5_2 fdfif5_4 cin fdfif5_3 unidm uneq2i 3eqtr3ri fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 cun cin fdfif5_2 fdfif5_3 cun fdfif5_4 fdfif5_3 cun cin fdfif5_2 fdfif5_4 cin fdfif5_3 cun fdfif5_3 fdfif5_4 cun fdfif5_4 fdfif5_3 cun fdfif5_2 fdfif5_3 cun fdfif5_3 fdfif5_4 uncom ineq2i fdfif5_2 fdfif5_4 fdfif5_3 undir eqtr4i fdfif5_3 fdfif5_2 fdfif5_3 cdif fdfif5_4 cin fdfif5_3 fdfif5_2 cdif cvv fdfif5_4 cdif cin unundi 3eqtr4i ineq12i eqtr4i 3eqtr4i $.
$}
$( Equality theorem for conditional operators.  (Contributed by NM,
     1-Sep-2004.) $)
${
	fifeq12_0 $f wff ph $.
	fifeq12_1 $f class A $.
	fifeq12_2 $f class B $.
	fifeq12_3 $f class C $.
	fifeq12_4 $f class D $.
	ifeq12 $p |- ( ( A = B /\ C = D ) -> if ( ph , A , C ) = if ( ph , B , D ) ) $= fifeq12_1 fifeq12_2 wceq fifeq12_3 fifeq12_4 wceq fifeq12_0 fifeq12_1 fifeq12_3 cif fifeq12_0 fifeq12_2 fifeq12_3 cif fifeq12_0 fifeq12_2 fifeq12_4 cif fifeq12_0 fifeq12_1 fifeq12_2 fifeq12_3 ifeq1 fifeq12_0 fifeq12_3 fifeq12_4 fifeq12_2 ifeq2 sylan9eq $.
$}
$( Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)
${
	fifeq1d_0 $f wff ph $.
	fifeq1d_1 $f wff ps $.
	fifeq1d_2 $f class A $.
	fifeq1d_3 $f class B $.
	fifeq1d_4 $f class C $.
	eifeq1d_0 $e |- ( ph -> A = B ) $.
	ifeq1d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $= fifeq1d_0 fifeq1d_2 fifeq1d_3 wceq fifeq1d_1 fifeq1d_2 fifeq1d_4 cif fifeq1d_1 fifeq1d_3 fifeq1d_4 cif wceq eifeq1d_0 fifeq1d_1 fifeq1d_2 fifeq1d_3 fifeq1d_4 ifeq1 syl $.
$}
$( Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)
${
	fifeq2d_0 $f wff ph $.
	fifeq2d_1 $f wff ps $.
	fifeq2d_2 $f class A $.
	fifeq2d_3 $f class B $.
	fifeq2d_4 $f class C $.
	eifeq2d_0 $e |- ( ph -> A = B ) $.
	ifeq2d $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $= fifeq2d_0 fifeq2d_2 fifeq2d_3 wceq fifeq2d_1 fifeq2d_4 fifeq2d_2 cif fifeq2d_1 fifeq2d_4 fifeq2d_3 cif wceq eifeq2d_0 fifeq2d_1 fifeq2d_2 fifeq2d_3 fifeq2d_4 ifeq2 syl $.
$}
$( Equality deduction for conditional operator.  (Contributed by NM,
       24-Mar-2015.) $)
${
	fifeq12d_0 $f wff ph $.
	fifeq12d_1 $f wff ps $.
	fifeq12d_2 $f class A $.
	fifeq12d_3 $f class B $.
	fifeq12d_4 $f class C $.
	fifeq12d_5 $f class D $.
	eifeq12d_0 $e |- ( ph -> A = B ) $.
	eifeq12d_1 $e |- ( ph -> C = D ) $.
	ifeq12d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , D ) ) $= fifeq12d_0 fifeq12d_1 fifeq12d_2 fifeq12d_4 cif fifeq12d_1 fifeq12d_3 fifeq12d_4 cif fifeq12d_1 fifeq12d_3 fifeq12d_5 cif fifeq12d_0 fifeq12d_1 fifeq12d_2 fifeq12d_3 fifeq12d_4 eifeq12d_0 ifeq1d fifeq12d_0 fifeq12d_1 fifeq12d_4 fifeq12d_5 fifeq12d_3 eifeq12d_1 ifeq2d eqtrd $.
$}
$( Equivalence theorem for conditional operators.  (Contributed by Raph
     Levien, 15-Jan-2004.) $)
${
	fifbi_0 $f wff ph $.
	fifbi_1 $f wff ps $.
	fifbi_2 $f class A $.
	fifbi_3 $f class B $.
	ifbi $p |- ( ( ph <-> ps ) -> if ( ph , A , B ) = if ( ps , A , B ) ) $= fifbi_0 fifbi_1 wb fifbi_0 fifbi_1 wa fifbi_0 wn fifbi_1 wn wa wo fifbi_0 fifbi_2 fifbi_3 cif fifbi_1 fifbi_2 fifbi_3 cif wceq fifbi_0 fifbi_1 dfbi3 fifbi_0 fifbi_1 wa fifbi_0 fifbi_2 fifbi_3 cif fifbi_1 fifbi_2 fifbi_3 cif wceq fifbi_0 wn fifbi_1 wn wa fifbi_0 fifbi_1 fifbi_0 fifbi_2 fifbi_3 cif fifbi_2 fifbi_1 fifbi_2 fifbi_3 cif fifbi_0 fifbi_2 fifbi_3 iftrue fifbi_1 fifbi_1 fifbi_2 fifbi_3 cif fifbi_2 fifbi_1 fifbi_2 fifbi_3 iftrue eqcomd sylan9eq fifbi_0 wn fifbi_1 wn fifbi_0 fifbi_2 fifbi_3 cif fifbi_3 fifbi_1 fifbi_2 fifbi_3 cif fifbi_0 fifbi_2 fifbi_3 iffalse fifbi_1 wn fifbi_1 fifbi_2 fifbi_3 cif fifbi_3 fifbi_1 fifbi_2 fifbi_3 iffalse eqcomd sylan9eq jaoi sylbi $.
$}
$( Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Apr-2005.) $)
${
	fifbid_0 $f wff ph $.
	fifbid_1 $f wff ps $.
	fifbid_2 $f wff ch $.
	fifbid_3 $f class A $.
	fifbid_4 $f class B $.
	eifbid_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ifbid $p |- ( ph -> if ( ps , A , B ) = if ( ch , A , B ) ) $= fifbid_0 fifbid_1 fifbid_2 wb fifbid_1 fifbid_3 fifbid_4 cif fifbid_2 fifbid_3 fifbid_4 cif wceq eifbid_0 fifbid_1 fifbid_2 fifbid_3 fifbid_4 ifbi syl $.
$}
$( Equivalence/equality inference for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)
${
	fifbieq2i_0 $f wff ph $.
	fifbieq2i_1 $f wff ps $.
	fifbieq2i_2 $f class A $.
	fifbieq2i_3 $f class B $.
	fifbieq2i_4 $f class C $.
	eifbieq2i_0 $e |- ( ph <-> ps ) $.
	eifbieq2i_1 $e |- A = B $.
	ifbieq2i $p |- if ( ph , C , A ) = if ( ps , C , B ) $= fifbieq2i_0 fifbieq2i_4 fifbieq2i_2 cif fifbieq2i_1 fifbieq2i_4 fifbieq2i_2 cif fifbieq2i_1 fifbieq2i_4 fifbieq2i_3 cif fifbieq2i_0 fifbieq2i_1 wb fifbieq2i_0 fifbieq2i_4 fifbieq2i_2 cif fifbieq2i_1 fifbieq2i_4 fifbieq2i_2 cif wceq eifbieq2i_0 fifbieq2i_0 fifbieq2i_1 fifbieq2i_4 fifbieq2i_2 ifbi ax-mp fifbieq2i_2 fifbieq2i_3 wceq fifbieq2i_1 fifbieq2i_4 fifbieq2i_2 cif fifbieq2i_1 fifbieq2i_4 fifbieq2i_3 cif wceq eifbieq2i_1 fifbieq2i_1 fifbieq2i_2 fifbieq2i_3 fifbieq2i_4 ifeq2 ax-mp eqtri $.
$}
$( Equivalence/equality deduction for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)
${
	fifbieq2d_0 $f wff ph $.
	fifbieq2d_1 $f wff ps $.
	fifbieq2d_2 $f wff ch $.
	fifbieq2d_3 $f class A $.
	fifbieq2d_4 $f class B $.
	fifbieq2d_5 $f class C $.
	eifbieq2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eifbieq2d_1 $e |- ( ph -> A = B ) $.
	ifbieq2d $p |- ( ph -> if ( ps , C , A ) = if ( ch , C , B ) ) $= fifbieq2d_0 fifbieq2d_1 fifbieq2d_5 fifbieq2d_3 cif fifbieq2d_2 fifbieq2d_5 fifbieq2d_3 cif fifbieq2d_2 fifbieq2d_5 fifbieq2d_4 cif fifbieq2d_0 fifbieq2d_1 fifbieq2d_2 fifbieq2d_5 fifbieq2d_3 eifbieq2d_0 ifbid fifbieq2d_0 fifbieq2d_2 fifbieq2d_3 fifbieq2d_4 fifbieq2d_5 eifbieq2d_1 ifeq2d eqtrd $.
$}
$( Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Mar-2013.) $)
${
	fifbieq12i_0 $f wff ph $.
	fifbieq12i_1 $f wff ps $.
	fifbieq12i_2 $f class A $.
	fifbieq12i_3 $f class B $.
	fifbieq12i_4 $f class C $.
	fifbieq12i_5 $f class D $.
	eifbieq12i_0 $e |- ( ph <-> ps ) $.
	eifbieq12i_1 $e |- A = C $.
	eifbieq12i_2 $e |- B = D $.
	ifbieq12i $p |- if ( ph , A , B ) = if ( ps , C , D ) $= fifbieq12i_0 fifbieq12i_2 fifbieq12i_3 cif fifbieq12i_0 fifbieq12i_4 fifbieq12i_3 cif fifbieq12i_1 fifbieq12i_4 fifbieq12i_5 cif fifbieq12i_2 fifbieq12i_4 wceq fifbieq12i_0 fifbieq12i_2 fifbieq12i_3 cif fifbieq12i_0 fifbieq12i_4 fifbieq12i_3 cif wceq eifbieq12i_1 fifbieq12i_0 fifbieq12i_2 fifbieq12i_4 fifbieq12i_3 ifeq1 ax-mp fifbieq12i_0 fifbieq12i_1 fifbieq12i_3 fifbieq12i_5 fifbieq12i_4 eifbieq12i_0 eifbieq12i_2 ifbieq2i eqtri $.
$}
$( Equivalence deduction for conditional operators.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
${
	fifbieq12d_0 $f wff ph $.
	fifbieq12d_1 $f wff ps $.
	fifbieq12d_2 $f wff ch $.
	fifbieq12d_3 $f class A $.
	fifbieq12d_4 $f class B $.
	fifbieq12d_5 $f class C $.
	fifbieq12d_6 $f class D $.
	eifbieq12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eifbieq12d_1 $e |- ( ph -> A = C ) $.
	eifbieq12d_2 $e |- ( ph -> B = D ) $.
	ifbieq12d $p |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) ) $= fifbieq12d_0 fifbieq12d_1 fifbieq12d_3 fifbieq12d_4 cif fifbieq12d_2 fifbieq12d_3 fifbieq12d_4 cif fifbieq12d_2 fifbieq12d_5 fifbieq12d_6 cif fifbieq12d_0 fifbieq12d_1 fifbieq12d_2 fifbieq12d_3 fifbieq12d_4 eifbieq12d_0 ifbid fifbieq12d_0 fifbieq12d_2 fifbieq12d_3 fifbieq12d_5 fifbieq12d_4 fifbieq12d_6 eifbieq12d_1 eifbieq12d_2 ifeq12d eqtrd $.
$}
$( Deduction version of ~ nfif .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	$d y ph $.
	$d y ps $.
	infifd_0 $f set y $.
	fnfifd_0 $f wff ph $.
	fnfifd_1 $f wff ps $.
	fnfifd_2 $f set x $.
	fnfifd_3 $f class A $.
	fnfifd_4 $f class B $.
	enfifd_0 $e |- ( ph -> F/ x ps ) $.
	enfifd_1 $e |- ( ph -> F/_ x A ) $.
	enfifd_2 $e |- ( ph -> F/_ x B ) $.
	nfifd $p |- ( ph -> F/_ x if ( ps , A , B ) ) $= fnfifd_0 fnfifd_2 fnfifd_1 fnfifd_3 fnfifd_4 cif infifd_0 sup_set_class fnfifd_4 wcel fnfifd_1 wi infifd_0 sup_set_class fnfifd_3 wcel fnfifd_1 wa wi infifd_0 cab fnfifd_1 infifd_0 fnfifd_3 fnfifd_4 dfif2 fnfifd_0 infifd_0 sup_set_class fnfifd_4 wcel fnfifd_1 wi infifd_0 sup_set_class fnfifd_3 wcel fnfifd_1 wa wi fnfifd_2 infifd_0 fnfifd_0 infifd_0 nfv fnfifd_0 infifd_0 sup_set_class fnfifd_4 wcel fnfifd_1 wi infifd_0 sup_set_class fnfifd_3 wcel fnfifd_1 wa fnfifd_2 fnfifd_0 infifd_0 sup_set_class fnfifd_4 wcel fnfifd_1 fnfifd_2 fnfifd_0 fnfifd_2 infifd_0 fnfifd_4 enfifd_2 nfcrd enfifd_0 nfimd fnfifd_0 infifd_0 sup_set_class fnfifd_3 wcel fnfifd_1 fnfifd_2 fnfifd_0 fnfifd_2 infifd_0 fnfifd_3 enfifd_1 nfcrd enfifd_0 nfand nfimd nfabd nfcxfrd $.
$}
$( Bound-variable hypothesis builder for a conditional operator.
       (Contributed by NM, 16-Feb-2005.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
${
	fnfif_0 $f wff ph $.
	fnfif_1 $f set x $.
	fnfif_2 $f class A $.
	fnfif_3 $f class B $.
	enfif_0 $e |- F/ x ph $.
	enfif_1 $e |- F/_ x A $.
	enfif_2 $e |- F/_ x B $.
	nfif $p |- F/_ x if ( ph , A , B ) $= fnfif_1 fnfif_0 fnfif_2 fnfif_3 cif wnfc wtru fnfif_0 fnfif_1 fnfif_2 fnfif_3 fnfif_0 fnfif_1 wnf wtru enfif_0 a1i fnfif_1 fnfif_2 wnfc wtru enfif_1 a1i fnfif_1 fnfif_3 wnfc wtru enfif_2 a1i nfifd trud $.
$}
$( Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
${
	fifeq1da_0 $f wff ph $.
	fifeq1da_1 $f wff ps $.
	fifeq1da_2 $f class A $.
	fifeq1da_3 $f class B $.
	fifeq1da_4 $f class C $.
	eifeq1da_0 $e |- ( ( ph /\ ps ) -> A = B ) $.
	ifeq1da $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $= fifeq1da_0 fifeq1da_1 fifeq1da_1 fifeq1da_2 fifeq1da_4 cif fifeq1da_1 fifeq1da_3 fifeq1da_4 cif wceq fifeq1da_0 fifeq1da_1 wa fifeq1da_1 fifeq1da_2 fifeq1da_3 fifeq1da_4 eifeq1da_0 ifeq1d fifeq1da_1 wn fifeq1da_1 fifeq1da_2 fifeq1da_4 cif fifeq1da_1 fifeq1da_3 fifeq1da_4 cif wceq fifeq1da_0 fifeq1da_1 wn fifeq1da_1 fifeq1da_2 fifeq1da_4 cif fifeq1da_4 fifeq1da_1 fifeq1da_3 fifeq1da_4 cif fifeq1da_1 fifeq1da_2 fifeq1da_4 iffalse fifeq1da_1 fifeq1da_3 fifeq1da_4 iffalse eqtr4d adantl pm2.61dan $.
$}
$( Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
${
	fifeq2da_0 $f wff ph $.
	fifeq2da_1 $f wff ps $.
	fifeq2da_2 $f class A $.
	fifeq2da_3 $f class B $.
	fifeq2da_4 $f class C $.
	eifeq2da_0 $e |- ( ( ph /\ -. ps ) -> A = B ) $.
	ifeq2da $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $= fifeq2da_0 fifeq2da_1 fifeq2da_1 fifeq2da_4 fifeq2da_2 cif fifeq2da_1 fifeq2da_4 fifeq2da_3 cif wceq fifeq2da_1 fifeq2da_1 fifeq2da_4 fifeq2da_2 cif fifeq2da_1 fifeq2da_4 fifeq2da_3 cif wceq fifeq2da_0 fifeq2da_1 fifeq2da_1 fifeq2da_4 fifeq2da_2 cif fifeq2da_4 fifeq2da_1 fifeq2da_4 fifeq2da_3 cif fifeq2da_1 fifeq2da_4 fifeq2da_2 iftrue fifeq2da_1 fifeq2da_4 fifeq2da_3 iftrue eqtr4d adantl fifeq2da_0 fifeq2da_1 wn wa fifeq2da_1 fifeq2da_2 fifeq2da_3 fifeq2da_4 eifeq2da_0 ifeq2d pm2.61dan $.
$}
$( Conditional closure.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
${
	fifclda_0 $f wff ph $.
	fifclda_1 $f wff ps $.
	fifclda_2 $f class A $.
	fifclda_3 $f class B $.
	fifclda_4 $f class C $.
	eifclda_0 $e |- ( ( ph /\ ps ) -> A e. C ) $.
	eifclda_1 $e |- ( ( ph /\ -. ps ) -> B e. C ) $.
	ifclda $p |- ( ph -> if ( ps , A , B ) e. C ) $= fifclda_0 fifclda_1 fifclda_1 fifclda_2 fifclda_3 cif fifclda_4 wcel fifclda_0 fifclda_1 wa fifclda_1 fifclda_2 fifclda_3 cif fifclda_2 fifclda_4 fifclda_1 fifclda_1 fifclda_2 fifclda_3 cif fifclda_2 wceq fifclda_0 fifclda_1 fifclda_2 fifclda_3 iftrue adantl eifclda_0 eqeltrd fifclda_0 fifclda_1 wn wa fifclda_1 fifclda_2 fifclda_3 cif fifclda_3 fifclda_4 fifclda_1 wn fifclda_1 fifclda_2 fifclda_3 cif fifclda_3 wceq fifclda_0 fifclda_1 fifclda_2 fifclda_3 iffalse adantl eifclda_1 eqeltrd pm2.61dan $.
$}
$( Distribute proper substitution through the conditional operator.
       (Contributed by NM, 24-Feb-2013.)  (Revised by Mario Carneiro,
       14-Nov-2016.) $)
${
	$d y A $.
	$d y B $.
	$d y C $.
	$d y ph $.
	$d x y $.
	icsbifg_0 $f set y $.
	fcsbifg_0 $f wff ph $.
	fcsbifg_1 $f set x $.
	fcsbifg_2 $f class A $.
	fcsbifg_3 $f class B $.
	fcsbifg_4 $f class C $.
	fcsbifg_5 $f class V $.
	csbifg $p |- ( A e. V -> [_ A / x ]_ if ( ph , B , C ) = if ( [. A / x ]. ph , [_ A / x ]_ B , [_ A / x ]_ C ) ) $= fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_0 fcsbifg_3 fcsbifg_4 cif csb fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb cif wceq fcsbifg_1 fcsbifg_2 fcsbifg_0 fcsbifg_3 fcsbifg_4 cif csb fcsbifg_0 fcsbifg_1 fcsbifg_2 wsbc fcsbifg_1 fcsbifg_2 fcsbifg_3 csb fcsbifg_1 fcsbifg_2 fcsbifg_4 csb cif wceq icsbifg_0 fcsbifg_2 fcsbifg_5 icsbifg_0 sup_set_class fcsbifg_2 wceq fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_0 fcsbifg_3 fcsbifg_4 cif csb fcsbifg_1 fcsbifg_2 fcsbifg_0 fcsbifg_3 fcsbifg_4 cif csb fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb cif fcsbifg_0 fcsbifg_1 fcsbifg_2 wsbc fcsbifg_1 fcsbifg_2 fcsbifg_3 csb fcsbifg_1 fcsbifg_2 fcsbifg_4 csb cif fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_2 fcsbifg_0 fcsbifg_3 fcsbifg_4 cif csbeq1 icsbifg_0 sup_set_class fcsbifg_2 wceq fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_0 fcsbifg_1 fcsbifg_2 wsbc fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb fcsbifg_1 fcsbifg_2 fcsbifg_3 csb fcsbifg_1 fcsbifg_2 fcsbifg_4 csb fcsbifg_0 fcsbifg_1 icsbifg_0 fcsbifg_2 dfsbcq2 fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_2 fcsbifg_3 csbeq1 fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_2 fcsbifg_4 csbeq1 ifbieq12d eqeq12d fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_0 fcsbifg_3 fcsbifg_4 cif fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb cif icsbifg_0 vex fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_1 fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb fcsbifg_0 fcsbifg_1 icsbifg_0 nfs1v fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 nfcsb1v fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 nfcsb1v nfif fcsbifg_1 sup_set_class icsbifg_0 sup_set_class wceq fcsbifg_0 fcsbifg_0 fcsbifg_1 icsbifg_0 wsb fcsbifg_3 fcsbifg_4 fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csb fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csb fcsbifg_0 fcsbifg_1 icsbifg_0 sbequ12 fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_3 csbeq1a fcsbifg_1 icsbifg_0 sup_set_class fcsbifg_4 csbeq1a ifbieq12d csbief vtoclg $.
$}
$( Elimination of a conditional operator contained in a wff ` ps ` .
       (Contributed by NM, 15-Feb-2005.) $)
${
	felimif_0 $f wff ph $.
	felimif_1 $f wff ps $.
	felimif_2 $f wff ch $.
	felimif_3 $f wff th $.
	felimif_4 $f class A $.
	felimif_5 $f class B $.
	eelimif_0 $e |- ( if ( ph , A , B ) = A -> ( ps <-> ch ) ) $.
	eelimif_1 $e |- ( if ( ph , A , B ) = B -> ( ps <-> th ) ) $.
	elimif $p |- ( ps <-> ( ( ph /\ ch ) \/ ( -. ph /\ th ) ) ) $= felimif_1 felimif_0 felimif_0 wn wo felimif_1 wa felimif_0 felimif_1 wa felimif_0 wn felimif_1 wa wo felimif_0 felimif_2 wa felimif_0 wn felimif_3 wa wo felimif_0 felimif_0 wn wo felimif_1 felimif_0 exmid biantrur felimif_0 felimif_0 wn felimif_1 andir felimif_0 felimif_1 wa felimif_0 felimif_2 wa felimif_0 wn felimif_1 wa felimif_0 wn felimif_3 wa felimif_0 felimif_1 felimif_2 felimif_0 felimif_0 felimif_4 felimif_5 cif felimif_4 wceq felimif_1 felimif_2 wb felimif_0 felimif_4 felimif_5 iftrue eelimif_0 syl pm5.32i felimif_0 wn felimif_1 felimif_3 felimif_0 wn felimif_0 felimif_4 felimif_5 cif felimif_5 wceq felimif_1 felimif_3 wb felimif_0 felimif_4 felimif_5 iffalse eelimif_1 syl pm5.32i orbi12i 3bitri $.
$}
$( A wff ` th ` containing a conditional operator is true when both of
         its cases are true.  (Contributed by NM, 15-Feb-2015.) $)
${
	fifbothda_0 $f wff ph $.
	fifbothda_1 $f wff ps $.
	fifbothda_2 $f wff ch $.
	fifbothda_3 $f wff th $.
	fifbothda_4 $f wff et $.
	fifbothda_5 $f class A $.
	fifbothda_6 $f class B $.
	eifbothda_0 $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	eifbothda_1 $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	eifbothda_2 $e |- ( ( et /\ ph ) -> ps ) $.
	eifbothda_3 $e |- ( ( et /\ -. ph ) -> ch ) $.
	ifbothda $p |- ( et -> th ) $= fifbothda_4 fifbothda_0 fifbothda_3 fifbothda_4 fifbothda_0 wa fifbothda_1 fifbothda_3 eifbothda_2 fifbothda_0 fifbothda_1 fifbothda_3 wb fifbothda_4 fifbothda_0 fifbothda_5 fifbothda_0 fifbothda_5 fifbothda_6 cif wceq fifbothda_1 fifbothda_3 wb fifbothda_0 fifbothda_0 fifbothda_5 fifbothda_6 cif fifbothda_5 fifbothda_0 fifbothda_5 fifbothda_6 iftrue eqcomd eifbothda_0 syl adantl mpbid fifbothda_4 fifbothda_0 wn wa fifbothda_2 fifbothda_3 eifbothda_3 fifbothda_0 wn fifbothda_2 fifbothda_3 wb fifbothda_4 fifbothda_0 wn fifbothda_6 fifbothda_0 fifbothda_5 fifbothda_6 cif wceq fifbothda_2 fifbothda_3 wb fifbothda_0 wn fifbothda_0 fifbothda_5 fifbothda_6 cif fifbothda_6 fifbothda_0 fifbothda_5 fifbothda_6 iffalse eqcomd eifbothda_1 syl adantl mpbid pm2.61dan $.
$}
$( A wff ` th ` containing a conditional operator is true when both of its
       cases are true.  (Contributed by NM, 3-Sep-2006.)  (Revised by Mario
       Carneiro, 15-Feb-2015.) $)
${
	fifboth_0 $f wff ph $.
	fifboth_1 $f wff ps $.
	fifboth_2 $f wff ch $.
	fifboth_3 $f wff th $.
	fifboth_4 $f class A $.
	fifboth_5 $f class B $.
	eifboth_0 $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	eifboth_1 $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	ifboth $p |- ( ( ps /\ ch ) -> th ) $= fifboth_0 fifboth_1 fifboth_2 fifboth_3 fifboth_1 fifboth_2 wa fifboth_4 fifboth_5 eifboth_0 eifboth_1 fifboth_1 fifboth_2 fifboth_0 simpll fifboth_1 fifboth_2 fifboth_0 wn simplr ifbothda $.
$}
$( Identical true and false arguments in the conditional operator.
     (Contributed by NM, 18-Apr-2005.) $)
${
	fifid_0 $f wff ph $.
	fifid_1 $f class A $.
	ifid $p |- if ( ph , A , A ) = A $= fifid_0 fifid_0 fifid_1 fifid_1 cif fifid_1 wceq fifid_0 fifid_1 fifid_1 iftrue fifid_0 fifid_1 fifid_1 iffalse pm2.61i $.
$}
$( Expansion of an equality with a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)
${
	feqif_0 $f wff ph $.
	feqif_1 $f class A $.
	feqif_2 $f class B $.
	feqif_3 $f class C $.
	eqif $p |- ( A = if ( ph , B , C ) <-> ( ( ph /\ A = B ) \/ ( -. ph /\ A = C ) ) ) $= feqif_0 feqif_1 feqif_0 feqif_2 feqif_3 cif wceq feqif_1 feqif_2 wceq feqif_1 feqif_3 wceq feqif_2 feqif_3 feqif_0 feqif_2 feqif_3 cif feqif_2 feqif_1 eqeq2 feqif_0 feqif_2 feqif_3 cif feqif_3 feqif_1 eqeq2 elimif $.
$}
$( Membership in a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)
${
	felif_0 $f wff ph $.
	felif_1 $f class A $.
	felif_2 $f class B $.
	felif_3 $f class C $.
	elif $p |- ( A e. if ( ph , B , C ) <-> ( ( ph /\ A e. B ) \/ ( -. ph /\ A e. C ) ) ) $= felif_0 felif_1 felif_0 felif_2 felif_3 cif wcel felif_1 felif_2 wcel felif_1 felif_3 wcel felif_2 felif_3 felif_0 felif_2 felif_3 cif felif_2 felif_1 eleq2 felif_0 felif_2 felif_3 cif felif_3 felif_1 eleq2 elimif $.
$}
$( Membership of a conditional operator.  (Contributed by NM,
     10-Sep-2005.) $)
${
	fifel_0 $f wff ph $.
	fifel_1 $f class A $.
	fifel_2 $f class B $.
	fifel_3 $f class C $.
	ifel $p |- ( if ( ph , A , B ) e. C <-> ( ( ph /\ A e. C ) \/ ( -. ph /\ B e. C ) ) ) $= fifel_0 fifel_0 fifel_1 fifel_2 cif fifel_3 wcel fifel_1 fifel_3 wcel fifel_2 fifel_3 wcel fifel_1 fifel_2 fifel_0 fifel_1 fifel_2 cif fifel_1 fifel_3 eleq1 fifel_0 fifel_1 fifel_2 cif fifel_2 fifel_3 eleq1 elimif $.
$}
$( Membership (closure) of a conditional operator.  (Contributed by NM,
     4-Apr-2005.) $)
${
	fifcl_0 $f wff ph $.
	fifcl_1 $f class A $.
	fifcl_2 $f class B $.
	fifcl_3 $f class C $.
	ifcl $p |- ( ( A e. C /\ B e. C ) -> if ( ph , A , B ) e. C ) $= fifcl_0 fifcl_1 fifcl_3 wcel fifcl_2 fifcl_3 wcel fifcl_0 fifcl_1 fifcl_2 cif fifcl_3 wcel fifcl_1 fifcl_2 fifcl_1 fifcl_0 fifcl_1 fifcl_2 cif fifcl_3 eleq1 fifcl_2 fifcl_0 fifcl_1 fifcl_2 cif fifcl_3 eleq1 ifboth $.
$}
$( The possible values of a conditional operator.  (Contributed by NM,
     17-Jun-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	fifeqor_0 $f wff ph $.
	fifeqor_1 $f class A $.
	fifeqor_2 $f class B $.
	ifeqor $p |- ( if ( ph , A , B ) = A \/ if ( ph , A , B ) = B ) $= fifeqor_0 fifeqor_1 fifeqor_2 cif fifeqor_1 wceq fifeqor_0 fifeqor_1 fifeqor_2 cif fifeqor_2 wceq fifeqor_0 fifeqor_1 fifeqor_2 cif fifeqor_1 wceq wn fifeqor_0 wn fifeqor_0 fifeqor_1 fifeqor_2 cif fifeqor_2 wceq fifeqor_0 fifeqor_0 fifeqor_1 fifeqor_2 cif fifeqor_1 wceq fifeqor_0 fifeqor_1 fifeqor_2 iftrue con3i fifeqor_0 fifeqor_1 fifeqor_2 iffalse syl orri $.
$}
$( Negating the first argument swaps the last two arguments of a conditional
     operator.  (Contributed by NM, 21-Jun-2007.) $)
${
	fifnot_0 $f wff ph $.
	fifnot_1 $f class A $.
	fifnot_2 $f class B $.
	ifnot $p |- if ( -. ph , A , B ) = if ( ph , B , A ) $= fifnot_0 fifnot_0 wn fifnot_1 fifnot_2 cif fifnot_0 fifnot_2 fifnot_1 cif wceq fifnot_0 fifnot_0 wn fifnot_1 fifnot_2 cif fifnot_2 fifnot_0 fifnot_2 fifnot_1 cif fifnot_0 fifnot_0 wn wn fifnot_0 wn fifnot_1 fifnot_2 cif fifnot_2 wceq fifnot_0 notnot1 fifnot_0 wn fifnot_1 fifnot_2 iffalse syl fifnot_0 fifnot_2 fifnot_1 iftrue eqtr4d fifnot_0 wn fifnot_0 wn fifnot_1 fifnot_2 cif fifnot_1 fifnot_0 fifnot_2 fifnot_1 cif fifnot_0 wn fifnot_1 fifnot_2 iftrue fifnot_0 fifnot_2 fifnot_1 iffalse eqtr4d pm2.61i $.
$}
$( Rewrite a conjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)
${
	fifan_0 $f wff ph $.
	fifan_1 $f wff ps $.
	fifan_2 $f class A $.
	fifan_3 $f class B $.
	ifan $p |- if ( ( ph /\ ps ) , A , B ) = if ( ph , if ( ps , A , B ) , B ) $= fifan_0 fifan_0 fifan_1 wa fifan_2 fifan_3 cif fifan_0 fifan_1 fifan_2 fifan_3 cif fifan_3 cif wceq fifan_0 fifan_0 fifan_1 fifan_2 fifan_3 cif fifan_3 cif fifan_1 fifan_2 fifan_3 cif fifan_0 fifan_1 wa fifan_2 fifan_3 cif fifan_0 fifan_1 fifan_2 fifan_3 cif fifan_3 iftrue fifan_0 fifan_1 fifan_0 fifan_1 wa fifan_2 fifan_3 fifan_0 fifan_1 ibar ifbid eqtr2d fifan_0 wn fifan_0 fifan_1 wa fifan_2 fifan_3 cif fifan_3 fifan_0 fifan_1 fifan_2 fifan_3 cif fifan_3 cif fifan_0 wn fifan_0 fifan_1 wa wn fifan_0 fifan_1 wa fifan_2 fifan_3 cif fifan_3 wceq fifan_0 fifan_1 wa fifan_0 fifan_0 fifan_1 simpl con3i fifan_0 fifan_1 wa fifan_2 fifan_3 iffalse syl fifan_0 fifan_1 fifan_2 fifan_3 cif fifan_3 iffalse eqtr4d pm2.61i $.
$}
$( Rewrite a disjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)
${
	fifor_0 $f wff ph $.
	fifor_1 $f wff ps $.
	fifor_2 $f class A $.
	fifor_3 $f class B $.
	ifor $p |- if ( ( ph \/ ps ) , A , B ) = if ( ph , A , if ( ps , A , B ) ) $= fifor_0 fifor_0 fifor_1 wo fifor_2 fifor_3 cif fifor_0 fifor_2 fifor_1 fifor_2 fifor_3 cif cif wceq fifor_0 fifor_0 fifor_1 wo fifor_2 fifor_3 cif fifor_2 fifor_0 fifor_2 fifor_1 fifor_2 fifor_3 cif cif fifor_0 fifor_1 fifor_0 fifor_1 wo fifor_2 fifor_3 cif fifor_2 wceq fifor_0 fifor_1 wo fifor_2 fifor_3 iftrue orcs fifor_0 fifor_2 fifor_1 fifor_2 fifor_3 cif iftrue eqtr4d fifor_0 wn fifor_0 fifor_2 fifor_1 fifor_2 fifor_3 cif cif fifor_1 fifor_2 fifor_3 cif fifor_0 fifor_1 wo fifor_2 fifor_3 cif fifor_0 fifor_2 fifor_1 fifor_2 fifor_3 cif iffalse fifor_0 wn fifor_1 fifor_0 fifor_1 wo fifor_2 fifor_3 fifor_0 fifor_1 biorf ifbid eqtr2d pm2.61i $.
$}
$( Weak deduction theorem that eliminates a hypothesis ` ph ` , making it
       become an antecedent.  We assume that a proof exists for ` ph ` when the
       class variable ` A ` is replaced with a specific class ` B ` .  The
       hypothesis ` ch ` should be assigned to the inference, and the
       inference's hypothesis eliminated with ~ elimhyp .  If the inference has
       other hypotheses with class variable ` A ` , these can be kept by
       assigning ~ keephyp to them.  For more information, see the Deduction
       Theorem ~ http://us.metamath.org/mpeuni/mmdeduction.html .  (Contributed
       by NM, 15-May-1999.) $)
${
	fdedth_0 $f wff ph $.
	fdedth_1 $f wff ps $.
	fdedth_2 $f wff ch $.
	fdedth_3 $f class A $.
	fdedth_4 $f class B $.
	ededth_0 $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
	ededth_1 $e |- ch $.
	dedth $p |- ( ph -> ps ) $= fdedth_0 fdedth_1 fdedth_2 ededth_1 fdedth_0 fdedth_3 fdedth_0 fdedth_3 fdedth_4 cif wceq fdedth_1 fdedth_2 wb fdedth_0 fdedth_0 fdedth_3 fdedth_4 cif fdedth_3 fdedth_0 fdedth_3 fdedth_4 iftrue eqcomd ededth_0 syl mpbiri $.
$}
$( Weak deduction theorem eliminating two hypotheses.  This theorem is
       simpler to use than ~ dedth2v but requires that each hypothesis has
       exactly one class variable.  See also comments in ~ dedth .
       (Contributed by NM, 15-May-1999.) $)
${
	fdedth2h_0 $f wff ph $.
	fdedth2h_1 $f wff ps $.
	fdedth2h_2 $f wff ch $.
	fdedth2h_3 $f wff th $.
	fdedth2h_4 $f wff ta $.
	fdedth2h_5 $f class A $.
	fdedth2h_6 $f class B $.
	fdedth2h_7 $f class C $.
	fdedth2h_8 $f class D $.
	ededth2h_0 $e |- ( A = if ( ph , A , C ) -> ( ch <-> th ) ) $.
	ededth2h_1 $e |- ( B = if ( ps , B , D ) -> ( th <-> ta ) ) $.
	ededth2h_2 $e |- ta $.
	dedth2h $p |- ( ( ph /\ ps ) -> ch ) $= fdedth2h_0 fdedth2h_1 fdedth2h_2 fdedth2h_0 fdedth2h_1 fdedth2h_2 wi fdedth2h_1 fdedth2h_3 wi fdedth2h_5 fdedth2h_7 fdedth2h_5 fdedth2h_0 fdedth2h_5 fdedth2h_7 cif wceq fdedth2h_2 fdedth2h_3 fdedth2h_1 ededth2h_0 imbi2d fdedth2h_1 fdedth2h_3 fdedth2h_4 fdedth2h_6 fdedth2h_8 ededth2h_1 ededth2h_2 dedth dedth imp $.
$}
$( Weak deduction theorem eliminating three hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 15-May-1999.) $)
${
	fdedth3h_0 $f wff ph $.
	fdedth3h_1 $f wff ps $.
	fdedth3h_2 $f wff ch $.
	fdedth3h_3 $f wff th $.
	fdedth3h_4 $f wff ta $.
	fdedth3h_5 $f wff et $.
	fdedth3h_6 $f wff ze $.
	fdedth3h_7 $f class A $.
	fdedth3h_8 $f class B $.
	fdedth3h_9 $f class C $.
	fdedth3h_10 $f class D $.
	fdedth3h_11 $f class R $.
	fdedth3h_12 $f class S $.
	ededth3h_0 $e |- ( A = if ( ph , A , D ) -> ( th <-> ta ) ) $.
	ededth3h_1 $e |- ( B = if ( ps , B , R ) -> ( ta <-> et ) ) $.
	ededth3h_2 $e |- ( C = if ( ch , C , S ) -> ( et <-> ze ) ) $.
	ededth3h_3 $e |- ze $.
	dedth3h $p |- ( ( ph /\ ps /\ ch ) -> th ) $= fdedth3h_0 fdedth3h_1 fdedth3h_2 fdedth3h_3 fdedth3h_0 fdedth3h_1 fdedth3h_2 wa fdedth3h_3 wi fdedth3h_1 fdedth3h_2 wa fdedth3h_4 wi fdedth3h_7 fdedth3h_10 fdedth3h_7 fdedth3h_0 fdedth3h_7 fdedth3h_10 cif wceq fdedth3h_3 fdedth3h_4 fdedth3h_1 fdedth3h_2 wa ededth3h_0 imbi2d fdedth3h_1 fdedth3h_2 fdedth3h_4 fdedth3h_5 fdedth3h_6 fdedth3h_8 fdedth3h_9 fdedth3h_11 fdedth3h_12 ededth3h_1 ededth3h_2 ededth3h_3 dedth2h dedth 3impib $.
$}
$( Weak deduction theorem eliminating four hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 16-May-1999.) $)
${
	fdedth4h_0 $f wff ph $.
	fdedth4h_1 $f wff ps $.
	fdedth4h_2 $f wff ch $.
	fdedth4h_3 $f wff th $.
	fdedth4h_4 $f wff ta $.
	fdedth4h_5 $f wff et $.
	fdedth4h_6 $f wff ze $.
	fdedth4h_7 $f wff si $.
	fdedth4h_8 $f wff rh $.
	fdedth4h_9 $f class A $.
	fdedth4h_10 $f class B $.
	fdedth4h_11 $f class C $.
	fdedth4h_12 $f class D $.
	fdedth4h_13 $f class R $.
	fdedth4h_14 $f class S $.
	fdedth4h_15 $f class F $.
	fdedth4h_16 $f class G $.
	ededth4h_0 $e |- ( A = if ( ph , A , R ) -> ( ta <-> et ) ) $.
	ededth4h_1 $e |- ( B = if ( ps , B , S ) -> ( et <-> ze ) ) $.
	ededth4h_2 $e |- ( C = if ( ch , C , F ) -> ( ze <-> si ) ) $.
	ededth4h_3 $e |- ( D = if ( th , D , G ) -> ( si <-> rh ) ) $.
	ededth4h_4 $e |- rh $.
	dedth4h $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $= fdedth4h_0 fdedth4h_1 wa fdedth4h_2 fdedth4h_3 wa fdedth4h_4 fdedth4h_0 fdedth4h_1 fdedth4h_2 fdedth4h_3 wa fdedth4h_4 wi fdedth4h_2 fdedth4h_3 wa fdedth4h_5 wi fdedth4h_2 fdedth4h_3 wa fdedth4h_6 wi fdedth4h_9 fdedth4h_10 fdedth4h_13 fdedth4h_14 fdedth4h_9 fdedth4h_0 fdedth4h_9 fdedth4h_13 cif wceq fdedth4h_4 fdedth4h_5 fdedth4h_2 fdedth4h_3 wa ededth4h_0 imbi2d fdedth4h_10 fdedth4h_1 fdedth4h_10 fdedth4h_14 cif wceq fdedth4h_5 fdedth4h_6 fdedth4h_2 fdedth4h_3 wa ededth4h_1 imbi2d fdedth4h_2 fdedth4h_3 fdedth4h_6 fdedth4h_7 fdedth4h_8 fdedth4h_11 fdedth4h_12 fdedth4h_15 fdedth4h_16 ededth4h_2 ededth4h_3 ededth4h_4 dedth2h dedth2h imp $.
$}
$( Weak deduction theorem for eliminating a hypothesis with 2 class
       variables.  Note: if the hypothesis can be separated into two
       hypotheses, each with one class variable, then ~ dedth2h is simpler to
       use.  See also comments in ~ dedth .  (Contributed by NM, 13-Aug-1999.)
       (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
${
	fdedth2v_0 $f wff ph $.
	fdedth2v_1 $f wff ps $.
	fdedth2v_2 $f wff ch $.
	fdedth2v_3 $f wff th $.
	fdedth2v_4 $f class A $.
	fdedth2v_5 $f class B $.
	fdedth2v_6 $f class C $.
	fdedth2v_7 $f class D $.
	ededth2v_0 $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
	ededth2v_1 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	ededth2v_2 $e |- th $.
	dedth2v $p |- ( ph -> ps ) $= fdedth2v_0 fdedth2v_1 fdedth2v_0 fdedth2v_0 fdedth2v_1 fdedth2v_2 fdedth2v_3 fdedth2v_4 fdedth2v_5 fdedth2v_6 fdedth2v_7 ededth2v_0 ededth2v_1 ededth2v_2 dedth2h anidms $.
$}
$( Weak deduction theorem for eliminating a hypothesis with 3 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       13-Aug-1999.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
${
	fdedth3v_0 $f wff ph $.
	fdedth3v_1 $f wff ps $.
	fdedth3v_2 $f wff ch $.
	fdedth3v_3 $f wff th $.
	fdedth3v_4 $f wff ta $.
	fdedth3v_5 $f class A $.
	fdedth3v_6 $f class B $.
	fdedth3v_7 $f class C $.
	fdedth3v_8 $f class D $.
	fdedth3v_9 $f class R $.
	fdedth3v_10 $f class S $.
	ededth3v_0 $e |- ( A = if ( ph , A , D ) -> ( ps <-> ch ) ) $.
	ededth3v_1 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	ededth3v_2 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	ededth3v_3 $e |- ta $.
	dedth3v $p |- ( ph -> ps ) $= fdedth3v_0 fdedth3v_1 fdedth3v_0 fdedth3v_0 fdedth3v_1 fdedth3v_0 fdedth3v_0 fdedth3v_0 fdedth3v_1 fdedth3v_2 fdedth3v_3 fdedth3v_4 fdedth3v_5 fdedth3v_6 fdedth3v_7 fdedth3v_8 fdedth3v_9 fdedth3v_10 ededth3v_0 ededth3v_1 ededth3v_2 ededth3v_3 dedth3h 3anidm12 anidms $.
$}
$( Weak deduction theorem for eliminating a hypothesis with 4 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       21-Apr-2007.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
$v U $.
${
	fdedth4v_0 $f wff ph $.
	fdedth4v_1 $f wff ps $.
	fdedth4v_2 $f wff ch $.
	fdedth4v_3 $f wff th $.
	fdedth4v_4 $f wff ta $.
	fdedth4v_5 $f wff et $.
	fdedth4v_6 $f class A $.
	fdedth4v_7 $f class B $.
	fdedth4v_8 $f class C $.
	fdedth4v_9 $f class D $.
	fdedth4v_10 $f class R $.
	fdedth4v_11 $f class S $.
	fdedth4v_12 $f class T $.
	fdedth4v_13 $f class U $.
	ededth4v_0 $e |- ( A = if ( ph , A , R ) -> ( ps <-> ch ) ) $.
	ededth4v_1 $e |- ( B = if ( ph , B , S ) -> ( ch <-> th ) ) $.
	ededth4v_2 $e |- ( C = if ( ph , C , T ) -> ( th <-> ta ) ) $.
	ededth4v_3 $e |- ( D = if ( ph , D , U ) -> ( ta <-> et ) ) $.
	ededth4v_4 $e |- et $.
	dedth4v $p |- ( ph -> ps ) $= fdedth4v_0 fdedth4v_1 fdedth4v_0 fdedth4v_0 wa fdedth4v_1 fdedth4v_0 fdedth4v_0 fdedth4v_0 fdedth4v_0 fdedth4v_1 fdedth4v_2 fdedth4v_3 fdedth4v_4 fdedth4v_5 fdedth4v_6 fdedth4v_7 fdedth4v_8 fdedth4v_9 fdedth4v_10 fdedth4v_11 fdedth4v_12 fdedth4v_13 ededth4v_0 ededth4v_1 ededth4v_2 ededth4v_3 ededth4v_4 dedth4h anidms anidms $.
$}
$( Eliminate a hypothesis containing class variable ` A ` when it is known
       for a specific class ` B ` .  For more information, see comments in
       ~ dedth .  (Contributed by NM, 15-May-1999.) $)
${
	felimhyp_0 $f wff ph $.
	felimhyp_1 $f wff ps $.
	felimhyp_2 $f wff ch $.
	felimhyp_3 $f class A $.
	felimhyp_4 $f class B $.
	eelimhyp_0 $e |- ( A = if ( ph , A , B ) -> ( ph <-> ps ) ) $.
	eelimhyp_1 $e |- ( B = if ( ph , A , B ) -> ( ch <-> ps ) ) $.
	eelimhyp_2 $e |- ch $.
	elimhyp $p |- ps $= felimhyp_0 felimhyp_1 felimhyp_0 felimhyp_1 felimhyp_0 felimhyp_3 felimhyp_0 felimhyp_3 felimhyp_4 cif wceq felimhyp_0 felimhyp_1 wb felimhyp_0 felimhyp_0 felimhyp_3 felimhyp_4 cif felimhyp_3 felimhyp_0 felimhyp_3 felimhyp_4 iftrue eqcomd eelimhyp_0 syl ibi felimhyp_0 wn felimhyp_2 felimhyp_1 eelimhyp_2 felimhyp_0 wn felimhyp_4 felimhyp_0 felimhyp_3 felimhyp_4 cif wceq felimhyp_2 felimhyp_1 wb felimhyp_0 wn felimhyp_0 felimhyp_3 felimhyp_4 cif felimhyp_4 felimhyp_0 felimhyp_3 felimhyp_4 iffalse eqcomd eelimhyp_1 syl mpbii pm2.61i $.
$}
$( Eliminate a hypothesis containing 2 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)
${
	felimhyp2v_0 $f wff ph $.
	felimhyp2v_1 $f wff ch $.
	felimhyp2v_2 $f wff th $.
	felimhyp2v_3 $f wff ta $.
	felimhyp2v_4 $f wff et $.
	felimhyp2v_5 $f class A $.
	felimhyp2v_6 $f class B $.
	felimhyp2v_7 $f class C $.
	felimhyp2v_8 $f class D $.
	eelimhyp2v_0 $e |- ( A = if ( ph , A , C ) -> ( ph <-> ch ) ) $.
	eelimhyp2v_1 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	eelimhyp2v_2 $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
	eelimhyp2v_3 $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
	eelimhyp2v_4 $e |- ta $.
	elimhyp2v $p |- th $= felimhyp2v_0 felimhyp2v_2 felimhyp2v_0 felimhyp2v_2 felimhyp2v_0 felimhyp2v_0 felimhyp2v_1 felimhyp2v_2 felimhyp2v_0 felimhyp2v_5 felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 cif wceq felimhyp2v_0 felimhyp2v_1 wb felimhyp2v_0 felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 cif felimhyp2v_5 felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 iftrue eqcomd eelimhyp2v_0 syl felimhyp2v_0 felimhyp2v_6 felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 cif wceq felimhyp2v_1 felimhyp2v_2 wb felimhyp2v_0 felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 cif felimhyp2v_6 felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 iftrue eqcomd eelimhyp2v_1 syl bitrd ibi felimhyp2v_0 wn felimhyp2v_3 felimhyp2v_2 eelimhyp2v_4 felimhyp2v_0 wn felimhyp2v_3 felimhyp2v_4 felimhyp2v_2 felimhyp2v_0 wn felimhyp2v_7 felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 cif wceq felimhyp2v_3 felimhyp2v_4 wb felimhyp2v_0 wn felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 cif felimhyp2v_7 felimhyp2v_0 felimhyp2v_5 felimhyp2v_7 iffalse eqcomd eelimhyp2v_2 syl felimhyp2v_0 wn felimhyp2v_8 felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 cif wceq felimhyp2v_4 felimhyp2v_2 wb felimhyp2v_0 wn felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 cif felimhyp2v_8 felimhyp2v_0 felimhyp2v_6 felimhyp2v_8 iffalse eqcomd eelimhyp2v_3 syl bitrd mpbii pm2.61i $.
$}
$( Eliminate a hypothesis containing 3 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)
${
	felimhyp3v_0 $f wff ph $.
	felimhyp3v_1 $f wff ch $.
	felimhyp3v_2 $f wff th $.
	felimhyp3v_3 $f wff ta $.
	felimhyp3v_4 $f wff et $.
	felimhyp3v_5 $f wff ze $.
	felimhyp3v_6 $f wff si $.
	felimhyp3v_7 $f class A $.
	felimhyp3v_8 $f class B $.
	felimhyp3v_9 $f class C $.
	felimhyp3v_10 $f class D $.
	felimhyp3v_11 $f class R $.
	felimhyp3v_12 $f class S $.
	eelimhyp3v_0 $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
	eelimhyp3v_1 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	eelimhyp3v_2 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	eelimhyp3v_3 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	eelimhyp3v_4 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	eelimhyp3v_5 $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
	eelimhyp3v_6 $e |- et $.
	elimhyp3v $p |- ta $= felimhyp3v_0 felimhyp3v_3 felimhyp3v_0 felimhyp3v_3 felimhyp3v_0 felimhyp3v_0 felimhyp3v_1 felimhyp3v_2 felimhyp3v_3 felimhyp3v_0 felimhyp3v_7 felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 cif wceq felimhyp3v_0 felimhyp3v_1 wb felimhyp3v_0 felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 cif felimhyp3v_7 felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 iftrue eqcomd eelimhyp3v_0 syl felimhyp3v_0 felimhyp3v_8 felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 cif wceq felimhyp3v_1 felimhyp3v_2 wb felimhyp3v_0 felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 cif felimhyp3v_8 felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 iftrue eqcomd eelimhyp3v_1 syl felimhyp3v_0 felimhyp3v_9 felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 cif wceq felimhyp3v_2 felimhyp3v_3 wb felimhyp3v_0 felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 cif felimhyp3v_9 felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 iftrue eqcomd eelimhyp3v_2 syl 3bitrd ibi felimhyp3v_0 wn felimhyp3v_4 felimhyp3v_3 eelimhyp3v_6 felimhyp3v_0 wn felimhyp3v_4 felimhyp3v_5 felimhyp3v_6 felimhyp3v_3 felimhyp3v_0 wn felimhyp3v_10 felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 cif wceq felimhyp3v_4 felimhyp3v_5 wb felimhyp3v_0 wn felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 cif felimhyp3v_10 felimhyp3v_0 felimhyp3v_7 felimhyp3v_10 iffalse eqcomd eelimhyp3v_3 syl felimhyp3v_0 wn felimhyp3v_11 felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 cif wceq felimhyp3v_5 felimhyp3v_6 wb felimhyp3v_0 wn felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 cif felimhyp3v_11 felimhyp3v_0 felimhyp3v_8 felimhyp3v_11 iffalse eqcomd eelimhyp3v_4 syl felimhyp3v_0 wn felimhyp3v_12 felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 cif wceq felimhyp3v_6 felimhyp3v_3 wb felimhyp3v_0 wn felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 cif felimhyp3v_12 felimhyp3v_0 felimhyp3v_9 felimhyp3v_12 iffalse eqcomd eelimhyp3v_5 syl 3bitrd mpbii pm2.61i $.
$}
$( Eliminate a hypothesis containing 4 class variables (for use with the
       weak deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)
${
	felimhyp4v_0 $f wff ph $.
	felimhyp4v_1 $f wff ps $.
	felimhyp4v_2 $f wff ch $.
	felimhyp4v_3 $f wff th $.
	felimhyp4v_4 $f wff ta $.
	felimhyp4v_5 $f wff et $.
	felimhyp4v_6 $f wff ze $.
	felimhyp4v_7 $f wff si $.
	felimhyp4v_8 $f wff rh $.
	felimhyp4v_9 $f class A $.
	felimhyp4v_10 $f class B $.
	felimhyp4v_11 $f class C $.
	felimhyp4v_12 $f class D $.
	felimhyp4v_13 $f class R $.
	felimhyp4v_14 $f class S $.
	felimhyp4v_15 $f class F $.
	felimhyp4v_16 $f class G $.
	eelimhyp4v_0 $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
	eelimhyp4v_1 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	eelimhyp4v_2 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	eelimhyp4v_3 $e |- ( F = if ( ph , F , G ) -> ( ta <-> ps ) ) $.
	eelimhyp4v_4 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	eelimhyp4v_5 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	eelimhyp4v_6 $e |- ( S = if ( ph , C , S ) -> ( si <-> rh ) ) $.
	eelimhyp4v_7 $e |- ( G = if ( ph , F , G ) -> ( rh <-> ps ) ) $.
	eelimhyp4v_8 $e |- et $.
	elimhyp4v $p |- ps $= felimhyp4v_0 felimhyp4v_1 felimhyp4v_0 felimhyp4v_1 felimhyp4v_0 felimhyp4v_0 felimhyp4v_3 felimhyp4v_4 felimhyp4v_1 felimhyp4v_0 felimhyp4v_0 felimhyp4v_2 felimhyp4v_3 felimhyp4v_0 felimhyp4v_9 felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 cif wceq felimhyp4v_0 felimhyp4v_2 wb felimhyp4v_0 felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 cif felimhyp4v_9 felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 iftrue eqcomd eelimhyp4v_0 syl felimhyp4v_0 felimhyp4v_10 felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 cif wceq felimhyp4v_2 felimhyp4v_3 wb felimhyp4v_0 felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 cif felimhyp4v_10 felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 iftrue eqcomd eelimhyp4v_1 syl bitrd felimhyp4v_0 felimhyp4v_11 felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 cif wceq felimhyp4v_3 felimhyp4v_4 wb felimhyp4v_0 felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 cif felimhyp4v_11 felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 iftrue eqcomd eelimhyp4v_2 syl felimhyp4v_0 felimhyp4v_15 felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 cif wceq felimhyp4v_4 felimhyp4v_1 wb felimhyp4v_0 felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 cif felimhyp4v_15 felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 iftrue eqcomd eelimhyp4v_3 syl 3bitrd ibi felimhyp4v_0 wn felimhyp4v_5 felimhyp4v_1 eelimhyp4v_8 felimhyp4v_0 wn felimhyp4v_5 felimhyp4v_7 felimhyp4v_8 felimhyp4v_1 felimhyp4v_0 wn felimhyp4v_5 felimhyp4v_6 felimhyp4v_7 felimhyp4v_0 wn felimhyp4v_12 felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 cif wceq felimhyp4v_5 felimhyp4v_6 wb felimhyp4v_0 wn felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 cif felimhyp4v_12 felimhyp4v_0 felimhyp4v_9 felimhyp4v_12 iffalse eqcomd eelimhyp4v_4 syl felimhyp4v_0 wn felimhyp4v_13 felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 cif wceq felimhyp4v_6 felimhyp4v_7 wb felimhyp4v_0 wn felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 cif felimhyp4v_13 felimhyp4v_0 felimhyp4v_10 felimhyp4v_13 iffalse eqcomd eelimhyp4v_5 syl bitrd felimhyp4v_0 wn felimhyp4v_14 felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 cif wceq felimhyp4v_7 felimhyp4v_8 wb felimhyp4v_0 wn felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 cif felimhyp4v_14 felimhyp4v_0 felimhyp4v_11 felimhyp4v_14 iffalse eqcomd eelimhyp4v_6 syl felimhyp4v_0 wn felimhyp4v_16 felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 cif wceq felimhyp4v_8 felimhyp4v_1 wb felimhyp4v_0 wn felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 cif felimhyp4v_16 felimhyp4v_0 felimhyp4v_15 felimhyp4v_16 iffalse eqcomd eelimhyp4v_7 syl 3bitrd mpbii pm2.61i $.
$}
$( Eliminate a membership hypothesis for weak deduction theorem, when
       special case ` B e. C ` is provable.  (Contributed by NM,
       15-May-1999.) $)
${
	felimel_0 $f class A $.
	felimel_1 $f class B $.
	felimel_2 $f class C $.
	eelimel_0 $e |- B e. C $.
	elimel $p |- if ( A e. C , A , B ) e. C $= felimel_0 felimel_2 wcel felimel_0 felimel_2 wcel felimel_0 felimel_1 cif felimel_2 wcel felimel_1 felimel_2 wcel felimel_0 felimel_1 felimel_0 felimel_0 felimel_2 wcel felimel_0 felimel_1 cif felimel_2 eleq1 felimel_1 felimel_0 felimel_2 wcel felimel_0 felimel_1 cif felimel_2 eleq1 eelimel_0 elimhyp $.
$}
$( Version of ~ elimhyp where the hypothesis is deduced from the final
       antecedent.  See ~ ghomgrplem for an example of its use.  (Contributed
       by Paul Chapman, 25-Mar-2008.) $)
${
	felimdhyp_0 $f wff ph $.
	felimdhyp_1 $f wff ps $.
	felimdhyp_2 $f wff ch $.
	felimdhyp_3 $f wff th $.
	felimdhyp_4 $f class A $.
	felimdhyp_5 $f class B $.
	eelimdhyp_0 $e |- ( ph -> ps ) $.
	eelimdhyp_1 $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
	eelimdhyp_2 $e |- ( B = if ( ph , A , B ) -> ( th <-> ch ) ) $.
	eelimdhyp_3 $e |- th $.
	elimdhyp $p |- ch $= felimdhyp_0 felimdhyp_2 felimdhyp_0 felimdhyp_1 felimdhyp_2 eelimdhyp_0 felimdhyp_0 felimdhyp_4 felimdhyp_0 felimdhyp_4 felimdhyp_5 cif wceq felimdhyp_1 felimdhyp_2 wb felimdhyp_0 felimdhyp_0 felimdhyp_4 felimdhyp_5 cif felimdhyp_4 felimdhyp_0 felimdhyp_4 felimdhyp_5 iftrue eqcomd eelimdhyp_1 syl mpbid felimdhyp_0 wn felimdhyp_3 felimdhyp_2 eelimdhyp_3 felimdhyp_0 wn felimdhyp_5 felimdhyp_0 felimdhyp_4 felimdhyp_5 cif wceq felimdhyp_3 felimdhyp_2 wb felimdhyp_0 wn felimdhyp_0 felimdhyp_4 felimdhyp_5 cif felimdhyp_5 felimdhyp_0 felimdhyp_4 felimdhyp_5 iffalse eqcomd eelimdhyp_2 syl mpbii pm2.61i $.
$}
$( Transform a hypothesis ` ps ` that we want to keep (but contains the
       same class variable ` A ` used in the eliminated hypothesis) for use
       with the weak deduction theorem.  (Contributed by NM, 15-May-1999.) $)
${
	fkeephyp_0 $f wff ph $.
	fkeephyp_1 $f wff ps $.
	fkeephyp_2 $f wff ch $.
	fkeephyp_3 $f wff th $.
	fkeephyp_4 $f class A $.
	fkeephyp_5 $f class B $.
	ekeephyp_0 $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	ekeephyp_1 $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	ekeephyp_2 $e |- ps $.
	ekeephyp_3 $e |- ch $.
	keephyp $p |- th $= fkeephyp_1 fkeephyp_2 fkeephyp_3 ekeephyp_2 ekeephyp_3 fkeephyp_0 fkeephyp_1 fkeephyp_2 fkeephyp_3 fkeephyp_4 fkeephyp_5 ekeephyp_0 ekeephyp_1 ifboth mp2an $.
$}
$( Keep a hypothesis containing 2 class variables (for use with the weak
       deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)
${
	fkeephyp2v_0 $f wff ph $.
	fkeephyp2v_1 $f wff ps $.
	fkeephyp2v_2 $f wff ch $.
	fkeephyp2v_3 $f wff th $.
	fkeephyp2v_4 $f wff ta $.
	fkeephyp2v_5 $f wff et $.
	fkeephyp2v_6 $f class A $.
	fkeephyp2v_7 $f class B $.
	fkeephyp2v_8 $f class C $.
	fkeephyp2v_9 $f class D $.
	ekeephyp2v_0 $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
	ekeephyp2v_1 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	ekeephyp2v_2 $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
	ekeephyp2v_3 $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
	ekeephyp2v_4 $e |- ps $.
	ekeephyp2v_5 $e |- ta $.
	keephyp2v $p |- th $= fkeephyp2v_0 fkeephyp2v_3 fkeephyp2v_0 fkeephyp2v_1 fkeephyp2v_3 ekeephyp2v_4 fkeephyp2v_0 fkeephyp2v_1 fkeephyp2v_2 fkeephyp2v_3 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 cif wceq fkeephyp2v_1 fkeephyp2v_2 wb fkeephyp2v_0 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 cif fkeephyp2v_6 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 iftrue eqcomd ekeephyp2v_0 syl fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 cif wceq fkeephyp2v_2 fkeephyp2v_3 wb fkeephyp2v_0 fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 cif fkeephyp2v_7 fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 iftrue eqcomd ekeephyp2v_1 syl bitrd mpbii fkeephyp2v_0 wn fkeephyp2v_4 fkeephyp2v_3 ekeephyp2v_5 fkeephyp2v_0 wn fkeephyp2v_4 fkeephyp2v_5 fkeephyp2v_3 fkeephyp2v_0 wn fkeephyp2v_8 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 cif wceq fkeephyp2v_4 fkeephyp2v_5 wb fkeephyp2v_0 wn fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 cif fkeephyp2v_8 fkeephyp2v_0 fkeephyp2v_6 fkeephyp2v_8 iffalse eqcomd ekeephyp2v_2 syl fkeephyp2v_0 wn fkeephyp2v_9 fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 cif wceq fkeephyp2v_5 fkeephyp2v_3 wb fkeephyp2v_0 wn fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 cif fkeephyp2v_9 fkeephyp2v_0 fkeephyp2v_7 fkeephyp2v_9 iffalse eqcomd ekeephyp2v_3 syl bitrd mpbii pm2.61i $.
$}
$( Keep a hypothesis containing 3 class variables.  (Contributed by NM,
       27-Sep-1999.) $)
${
	fkeephyp3v_0 $f wff ph $.
	fkeephyp3v_1 $f wff ch $.
	fkeephyp3v_2 $f wff th $.
	fkeephyp3v_3 $f wff ta $.
	fkeephyp3v_4 $f wff et $.
	fkeephyp3v_5 $f wff ze $.
	fkeephyp3v_6 $f wff si $.
	fkeephyp3v_7 $f wff rh $.
	fkeephyp3v_8 $f class A $.
	fkeephyp3v_9 $f class B $.
	fkeephyp3v_10 $f class C $.
	fkeephyp3v_11 $f class D $.
	fkeephyp3v_12 $f class R $.
	fkeephyp3v_13 $f class S $.
	ekeephyp3v_0 $e |- ( A = if ( ph , A , D ) -> ( rh <-> ch ) ) $.
	ekeephyp3v_1 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	ekeephyp3v_2 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	ekeephyp3v_3 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	ekeephyp3v_4 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	ekeephyp3v_5 $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
	ekeephyp3v_6 $e |- rh $.
	ekeephyp3v_7 $e |- et $.
	keephyp3v $p |- ta $= fkeephyp3v_0 fkeephyp3v_3 fkeephyp3v_0 fkeephyp3v_7 fkeephyp3v_3 ekeephyp3v_6 fkeephyp3v_0 fkeephyp3v_7 fkeephyp3v_1 fkeephyp3v_2 fkeephyp3v_3 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 cif wceq fkeephyp3v_7 fkeephyp3v_1 wb fkeephyp3v_0 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 cif fkeephyp3v_8 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 iftrue eqcomd ekeephyp3v_0 syl fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 cif wceq fkeephyp3v_1 fkeephyp3v_2 wb fkeephyp3v_0 fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 cif fkeephyp3v_9 fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 iftrue eqcomd ekeephyp3v_1 syl fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 cif wceq fkeephyp3v_2 fkeephyp3v_3 wb fkeephyp3v_0 fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 cif fkeephyp3v_10 fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 iftrue eqcomd ekeephyp3v_2 syl 3bitrd mpbii fkeephyp3v_0 wn fkeephyp3v_4 fkeephyp3v_3 ekeephyp3v_7 fkeephyp3v_0 wn fkeephyp3v_4 fkeephyp3v_5 fkeephyp3v_6 fkeephyp3v_3 fkeephyp3v_0 wn fkeephyp3v_11 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 cif wceq fkeephyp3v_4 fkeephyp3v_5 wb fkeephyp3v_0 wn fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 cif fkeephyp3v_11 fkeephyp3v_0 fkeephyp3v_8 fkeephyp3v_11 iffalse eqcomd ekeephyp3v_3 syl fkeephyp3v_0 wn fkeephyp3v_12 fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 cif wceq fkeephyp3v_5 fkeephyp3v_6 wb fkeephyp3v_0 wn fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 cif fkeephyp3v_12 fkeephyp3v_0 fkeephyp3v_9 fkeephyp3v_12 iffalse eqcomd ekeephyp3v_4 syl fkeephyp3v_0 wn fkeephyp3v_13 fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 cif wceq fkeephyp3v_6 fkeephyp3v_3 wb fkeephyp3v_0 wn fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 cif fkeephyp3v_13 fkeephyp3v_0 fkeephyp3v_10 fkeephyp3v_13 iffalse eqcomd ekeephyp3v_5 syl 3bitrd mpbii pm2.61i $.
$}
$( Keep a membership hypothesis for weak deduction theorem, when special
       case ` B e. C ` is provable.  (Contributed by NM, 14-Aug-1999.) $)
${
	fkeepel_0 $f wff ph $.
	fkeepel_1 $f class A $.
	fkeepel_2 $f class B $.
	fkeepel_3 $f class C $.
	ekeepel_0 $e |- A e. C $.
	ekeepel_1 $e |- B e. C $.
	keepel $p |- if ( ph , A , B ) e. C $= fkeepel_0 fkeepel_1 fkeepel_3 wcel fkeepel_2 fkeepel_3 wcel fkeepel_0 fkeepel_1 fkeepel_2 cif fkeepel_3 wcel fkeepel_1 fkeepel_2 fkeepel_1 fkeepel_0 fkeepel_1 fkeepel_2 cif fkeepel_3 eleq1 fkeepel_2 fkeepel_0 fkeepel_1 fkeepel_2 cif fkeepel_3 eleq1 ekeepel_0 ekeepel_1 keephyp $.
$}
$( Conditional operator existence.  (Contributed by NM, 2-Sep-2004.) $)
${
	fifex_0 $f wff ph $.
	fifex_1 $f class A $.
	fifex_2 $f class B $.
	eifex_0 $e |- A e. _V $.
	eifex_1 $e |- B e. _V $.
	ifex $p |- if ( ph , A , B ) e. _V $= fifex_0 fifex_1 fifex_2 cvv eifex_0 eifex_1 keepel $.
$}
$( Conditional operator existence.  (Contributed by NM, 21-Mar-2011.) $)
${
	$d A x y $.
	$d B y $.
	$d ph x y $.
	iifexg_0 $f set x $.
	iifexg_1 $f set y $.
	fifexg_0 $f wff ph $.
	fifexg_1 $f class A $.
	fifexg_2 $f class B $.
	fifexg_3 $f class V $.
	fifexg_4 $f class W $.
	ifexg $p |- ( ( A e. V /\ B e. W ) -> if ( ph , A , B ) e. _V ) $= fifexg_0 iifexg_0 sup_set_class iifexg_1 sup_set_class cif cvv wcel fifexg_0 fifexg_1 iifexg_1 sup_set_class cif cvv wcel fifexg_0 fifexg_1 fifexg_2 cif cvv wcel iifexg_0 iifexg_1 fifexg_1 fifexg_2 fifexg_3 fifexg_4 iifexg_0 sup_set_class fifexg_1 wceq fifexg_0 iifexg_0 sup_set_class iifexg_1 sup_set_class cif fifexg_0 fifexg_1 iifexg_1 sup_set_class cif cvv fifexg_0 iifexg_0 sup_set_class fifexg_1 iifexg_1 sup_set_class ifeq1 eleq1d iifexg_1 sup_set_class fifexg_2 wceq fifexg_0 fifexg_1 iifexg_1 sup_set_class cif fifexg_0 fifexg_1 fifexg_2 cif cvv fifexg_0 iifexg_1 sup_set_class fifexg_2 fifexg_1 ifeq2 eleq1d fifexg_0 iifexg_0 sup_set_class iifexg_1 sup_set_class iifexg_0 vex iifexg_1 vex ifex vtocl2g $.
$}

