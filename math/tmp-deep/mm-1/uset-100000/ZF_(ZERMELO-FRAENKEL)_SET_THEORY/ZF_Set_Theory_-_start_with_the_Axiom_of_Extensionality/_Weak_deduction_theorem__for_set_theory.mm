$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_empty_set.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

$(These lemmas are used to convert hypotheses into antecedents,
     when there is at least one class making the hypothesis true. $)

$(Declare new constant symbols. $)

$c if $.

$(Conditional operator (was "ded" for "deduction class"). $)

$(Extend class notation to include the conditional operator.  See ~ df-if
     for a description.  (In older databases this was denoted "ded".) $)

${
	$v ph A B  $.
	f0_cif $f wff ph $.
	f1_cif $f class A $.
	f2_cif $f class B $.
	a_cif $a class if ( ph , A , B ) $.
$}

$(Define the conditional operator.  Read ` if ( ph , A , B ) ` as "if
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
	$v ph x A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	f0_df-if $f wff ph $.
	f1_df-if $f set x $.
	f2_df-if $f class A $.
	f3_df-if $f class B $.
	a_df-if $a |- if ( ph , A , B ) = { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) } $.
$}

$(An alternate definition of the conditional operator ~ df-if with one
       fewer connectives (but probably less intuitive to understand).
       (Contributed by NM, 30-Jan-2006.) $)

${
	$v ph x A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_dfif2 $f wff ph $.
	f1_dfif2 $f set x $.
	f2_dfif2 $f class A $.
	f3_dfif2 $f class B $.
	p_dfif2 $p |- if ( ph , A , B ) = { x | ( ( x e. B -> ph ) -> ( x e. A /\ ph ) ) } $= f0_dfif2 f1_dfif2 f2_dfif2 f3_dfif2 a_df-if f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_df-or f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa p_orcom f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 p_iman f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wi f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa a_wn f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa p_imbi1i f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_wo f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa a_wn f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_wi f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa a_wo f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wi f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_wi p_3bitr4i f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa a_wo f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wi f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_wi f1_dfif2 p_abbii f0_dfif2 f2_dfif2 f3_dfif2 a_cif f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wn a_wa a_wo f1_dfif2 a_cab f1_dfif2 a_sup_set_class f3_dfif2 a_wcel f0_dfif2 a_wi f1_dfif2 a_sup_set_class f2_dfif2 a_wcel f0_dfif2 a_wa a_wi f1_dfif2 a_cab p_eqtri $.
$}

$(An alternate definition of the conditional operator ~ df-if as a simple
       class abstraction.  (Contributed by Mario Carneiro, 8-Sep-2013.) $)

${
	$v ph x A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_dfif6 $f wff ph $.
	f1_dfif6 $f set x $.
	f2_dfif6 $f class A $.
	f3_dfif6 $f class B $.
	p_dfif6 $p |- if ( ph , A , B ) = ( { x e. A | ph } u. { x e. B | -. ph } ) $= f1_dfif6 a_sup_set_class f2_dfif6 a_wcel f0_dfif6 a_wa f1_dfif6 a_sup_set_class f3_dfif6 a_wcel f0_dfif6 a_wn a_wa f1_dfif6 p_unab f0_dfif6 f1_dfif6 f2_dfif6 a_df-rab f0_dfif6 a_wn f1_dfif6 f3_dfif6 a_df-rab f0_dfif6 f1_dfif6 f2_dfif6 a_crab f1_dfif6 a_sup_set_class f2_dfif6 a_wcel f0_dfif6 a_wa f1_dfif6 a_cab f0_dfif6 a_wn f1_dfif6 f3_dfif6 a_crab f1_dfif6 a_sup_set_class f3_dfif6 a_wcel f0_dfif6 a_wn a_wa f1_dfif6 a_cab p_uneq12i f0_dfif6 f1_dfif6 f2_dfif6 f3_dfif6 a_df-if f1_dfif6 a_sup_set_class f2_dfif6 a_wcel f0_dfif6 a_wa f1_dfif6 a_cab f1_dfif6 a_sup_set_class f3_dfif6 a_wcel f0_dfif6 a_wn a_wa f1_dfif6 a_cab a_cun f1_dfif6 a_sup_set_class f2_dfif6 a_wcel f0_dfif6 a_wa f1_dfif6 a_sup_set_class f3_dfif6 a_wcel f0_dfif6 a_wn a_wa a_wo f1_dfif6 a_cab f0_dfif6 f1_dfif6 f2_dfif6 a_crab f0_dfif6 a_wn f1_dfif6 f3_dfif6 a_crab a_cun f0_dfif6 f2_dfif6 f3_dfif6 a_cif p_3eqtr4ri $.
$}

$(Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)

${
	$v ph A B C  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ifeq1 $f wff ph $.
	f1_ifeq1 $f class A $.
	f2_ifeq1 $f class B $.
	f3_ifeq1 $f class C $.
	i0_ifeq1 $f set x $.
	p_ifeq1 $p |- ( A = B -> if ( ph , A , C ) = if ( ph , B , C ) ) $= f0_ifeq1 i0_ifeq1 f1_ifeq1 f2_ifeq1 p_rabeq f1_ifeq1 f2_ifeq1 a_wceq f0_ifeq1 i0_ifeq1 f1_ifeq1 a_crab f0_ifeq1 i0_ifeq1 f2_ifeq1 a_crab f0_ifeq1 a_wn i0_ifeq1 f3_ifeq1 a_crab p_uneq1d f0_ifeq1 i0_ifeq1 f1_ifeq1 f3_ifeq1 p_dfif6 f0_ifeq1 i0_ifeq1 f2_ifeq1 f3_ifeq1 p_dfif6 f1_ifeq1 f2_ifeq1 a_wceq f0_ifeq1 i0_ifeq1 f1_ifeq1 a_crab f0_ifeq1 a_wn i0_ifeq1 f3_ifeq1 a_crab a_cun f0_ifeq1 i0_ifeq1 f2_ifeq1 a_crab f0_ifeq1 a_wn i0_ifeq1 f3_ifeq1 a_crab a_cun f0_ifeq1 f1_ifeq1 f3_ifeq1 a_cif f0_ifeq1 f2_ifeq1 f3_ifeq1 a_cif p_3eqtr4g $.
$}

$(Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)

${
	$v ph A B C  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ifeq2 $f wff ph $.
	f1_ifeq2 $f class A $.
	f2_ifeq2 $f class B $.
	f3_ifeq2 $f class C $.
	i0_ifeq2 $f set x $.
	p_ifeq2 $p |- ( A = B -> if ( ph , C , A ) = if ( ph , C , B ) ) $= f0_ifeq2 a_wn i0_ifeq2 f1_ifeq2 f2_ifeq2 p_rabeq f1_ifeq2 f2_ifeq2 a_wceq f0_ifeq2 a_wn i0_ifeq2 f1_ifeq2 a_crab f0_ifeq2 a_wn i0_ifeq2 f2_ifeq2 a_crab f0_ifeq2 i0_ifeq2 f3_ifeq2 a_crab p_uneq2d f0_ifeq2 i0_ifeq2 f3_ifeq2 f1_ifeq2 p_dfif6 f0_ifeq2 i0_ifeq2 f3_ifeq2 f2_ifeq2 p_dfif6 f1_ifeq2 f2_ifeq2 a_wceq f0_ifeq2 i0_ifeq2 f3_ifeq2 a_crab f0_ifeq2 a_wn i0_ifeq2 f1_ifeq2 a_crab a_cun f0_ifeq2 i0_ifeq2 f3_ifeq2 a_crab f0_ifeq2 a_wn i0_ifeq2 f2_ifeq2 a_crab a_cun f0_ifeq2 f3_ifeq2 f1_ifeq2 a_cif f0_ifeq2 f3_ifeq2 f2_ifeq2 a_cif p_3eqtr4g $.
$}

$(Value of the conditional operator when its first argument is true.
       (Contributed by NM, 15-May-1999.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)

${
	$v ph A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_iftrue $f wff ph $.
	f1_iftrue $f class A $.
	f2_iftrue $f class B $.
	i0_iftrue $f set x $.
	p_iftrue $p |- ( ph -> if ( ph , A , B ) = A ) $= f0_iftrue i0_iftrue a_sup_set_class f1_iftrue a_wcel i0_iftrue a_sup_set_class f2_iftrue a_wcel p_dedlem0a f0_iftrue i0_iftrue a_sup_set_class f2_iftrue a_wcel f0_iftrue a_wi i0_iftrue a_sup_set_class f1_iftrue a_wcel f0_iftrue a_wa a_wi i0_iftrue f1_iftrue p_abbi2dv f0_iftrue i0_iftrue f1_iftrue f2_iftrue p_dfif2 f0_iftrue f1_iftrue i0_iftrue a_sup_set_class f2_iftrue a_wcel f0_iftrue a_wi i0_iftrue a_sup_set_class f1_iftrue a_wcel f0_iftrue a_wa a_wi i0_iftrue a_cab f0_iftrue f1_iftrue f2_iftrue a_cif p_syl6reqr $.
$}

$(Value of the conditional operator when its first argument is false.
       (Contributed by NM, 14-Aug-1999.) $)

${
	$v ph A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_iffalse $f wff ph $.
	f1_iffalse $f class A $.
	f2_iffalse $f class B $.
	i0_iffalse $f set x $.
	p_iffalse $p |- ( -. ph -> if ( ph , A , B ) = B ) $= f0_iffalse i0_iffalse a_sup_set_class f1_iffalse a_wcel i0_iffalse a_sup_set_class f2_iffalse a_wcel p_dedlemb f0_iffalse a_wn i0_iffalse a_sup_set_class f1_iffalse a_wcel f0_iffalse a_wa i0_iffalse a_sup_set_class f2_iffalse a_wcel f0_iffalse a_wn a_wa a_wo i0_iffalse f2_iffalse p_abbi2dv f0_iffalse i0_iffalse f1_iffalse f2_iffalse a_df-if f0_iffalse a_wn f2_iffalse i0_iffalse a_sup_set_class f1_iffalse a_wcel f0_iffalse a_wa i0_iffalse a_sup_set_class f2_iffalse a_wcel f0_iffalse a_wn a_wa a_wo i0_iffalse a_cab f0_iffalse f1_iffalse f2_iffalse a_cif p_syl6reqr $.
$}

$(When values are unequal, but an "if" condition checks if they are equal,
     then the "false" branch results.  This is a simple utility to provide a
     slight shortening and simplification of proofs vs. applying ~ iffalse
     directly in this case.  It happens, e.g., in ~ oevn0 .  (Contributed by
     David A. Wheeler, 15-May-2015.) $)

${
	$v A B C D  $.
	f0_ifnefalse $f class A $.
	f1_ifnefalse $f class B $.
	f2_ifnefalse $f class C $.
	f3_ifnefalse $f class D $.
	p_ifnefalse $p |- ( A =/= B -> if ( A = B , C , D ) = D ) $= f0_ifnefalse f1_ifnefalse a_df-ne f0_ifnefalse f1_ifnefalse a_wceq f2_ifnefalse f3_ifnefalse p_iffalse f0_ifnefalse f1_ifnefalse a_wne f0_ifnefalse f1_ifnefalse a_wceq a_wn f0_ifnefalse f1_ifnefalse a_wceq f2_ifnefalse f3_ifnefalse a_cif f3_ifnefalse a_wceq p_sylbi $.
$}

$(Distribute a function over an if-clause.  (Contributed by Mario
       Carneiro, 14-Aug-2013.) $)

${
	$v ph A B C D E  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_ifsb $f wff ph $.
	f1_ifsb $f class A $.
	f2_ifsb $f class B $.
	f3_ifsb $f class C $.
	f4_ifsb $f class D $.
	f5_ifsb $f class E $.
	e0_ifsb $e |- ( if ( ph , A , B ) = A -> C = D ) $.
	e1_ifsb $e |- ( if ( ph , A , B ) = B -> C = E ) $.
	p_ifsb $p |- C = if ( ph , D , E ) $= f0_ifsb f1_ifsb f2_ifsb p_iftrue e0_ifsb f0_ifsb f0_ifsb f1_ifsb f2_ifsb a_cif f1_ifsb a_wceq f3_ifsb f4_ifsb a_wceq p_syl f0_ifsb f4_ifsb f5_ifsb p_iftrue f0_ifsb f3_ifsb f4_ifsb f0_ifsb f4_ifsb f5_ifsb a_cif p_eqtr4d f0_ifsb f1_ifsb f2_ifsb p_iffalse e1_ifsb f0_ifsb a_wn f0_ifsb f1_ifsb f2_ifsb a_cif f2_ifsb a_wceq f3_ifsb f5_ifsb a_wceq p_syl f0_ifsb f4_ifsb f5_ifsb p_iffalse f0_ifsb a_wn f3_ifsb f5_ifsb f0_ifsb f4_ifsb f5_ifsb a_cif p_eqtr4d f0_ifsb f3_ifsb f0_ifsb f4_ifsb f5_ifsb a_cif a_wceq p_pm2.61i $.
$}

$(Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)

${
	$v ph x A B C  $.
	$d y A  $.
	$d y B  $.
	$d x y ph  $.
	f0_dfif3 $f wff ph $.
	f1_dfif3 $f set x $.
	f2_dfif3 $f class A $.
	f3_dfif3 $f class B $.
	f4_dfif3 $f class C $.
	i0_dfif3 $f set y $.
	e0_dfif3 $e |- C = { x | ph } $.
	p_dfif3 $p |- if ( ph , A , B ) = ( ( A i^i C ) u. ( B i^i ( _V \ C ) ) ) $= f0_dfif3 i0_dfif3 f2_dfif3 f3_dfif3 p_dfif6 e0_dfif3 f1_dfif3 a_sup_set_class i0_dfif3 a_sup_set_class a_wceq f0_dfif3 p_biidd f0_dfif3 f0_dfif3 f1_dfif3 i0_dfif3 p_cbvabv f4_dfif3 f0_dfif3 f1_dfif3 a_cab f0_dfif3 i0_dfif3 a_cab p_eqtri f4_dfif3 f0_dfif3 i0_dfif3 a_cab f2_dfif3 p_ineq2i f0_dfif3 i0_dfif3 f2_dfif3 p_dfrab3 f2_dfif3 f4_dfif3 a_cin f2_dfif3 f0_dfif3 i0_dfif3 a_cab a_cin f0_dfif3 i0_dfif3 f2_dfif3 a_crab p_eqtr4i f0_dfif3 a_wn i0_dfif3 f3_dfif3 p_dfrab3 f0_dfif3 i0_dfif3 p_notab e0_dfif3 f1_dfif3 a_sup_set_class i0_dfif3 a_sup_set_class a_wceq f0_dfif3 p_biidd f0_dfif3 f0_dfif3 f1_dfif3 i0_dfif3 p_cbvabv f4_dfif3 f0_dfif3 f1_dfif3 a_cab f0_dfif3 i0_dfif3 a_cab p_eqtri f4_dfif3 f0_dfif3 i0_dfif3 a_cab a_cvv p_difeq2i f0_dfif3 a_wn i0_dfif3 a_cab a_cvv f0_dfif3 i0_dfif3 a_cab a_cdif a_cvv f4_dfif3 a_cdif p_eqtr4i f0_dfif3 a_wn i0_dfif3 a_cab a_cvv f4_dfif3 a_cdif f3_dfif3 p_ineq2i f0_dfif3 a_wn i0_dfif3 f3_dfif3 a_crab f3_dfif3 f0_dfif3 a_wn i0_dfif3 a_cab a_cin f3_dfif3 a_cvv f4_dfif3 a_cdif a_cin p_eqtr2i f2_dfif3 f4_dfif3 a_cin f0_dfif3 i0_dfif3 f2_dfif3 a_crab f3_dfif3 a_cvv f4_dfif3 a_cdif a_cin f0_dfif3 a_wn i0_dfif3 f3_dfif3 a_crab p_uneq12i f0_dfif3 f2_dfif3 f3_dfif3 a_cif f0_dfif3 i0_dfif3 f2_dfif3 a_crab f0_dfif3 a_wn i0_dfif3 f3_dfif3 a_crab a_cun f2_dfif3 f4_dfif3 a_cin f3_dfif3 a_cvv f4_dfif3 a_cdif a_cin a_cun p_eqtr4i $.
$}

$(Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.) $)

${
	$v ph x A B C  $.
	$d A  $.
	$d B  $.
	$d x ph  $.
	f0_dfif4 $f wff ph $.
	f1_dfif4 $f set x $.
	f2_dfif4 $f class A $.
	f3_dfif4 $f class B $.
	f4_dfif4 $f class C $.
	e0_dfif4 $e |- C = { x | ph } $.
	p_dfif4 $p |- if ( ph , A , B ) = ( ( A u. B ) i^i ( ( A u. ( _V \ C ) ) i^i ( B u. C ) ) ) $= e0_dfif4 f0_dfif4 f1_dfif4 f2_dfif4 f3_dfif4 f4_dfif4 p_dfif3 f2_dfif4 f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin p_undir f2_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif p_undi f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif p_undi f4_dfif4 f3_dfif4 p_uncom f4_dfif4 p_undifv f4_dfif4 f3_dfif4 a_cun f3_dfif4 f4_dfif4 a_cun f4_dfif4 a_cvv f4_dfif4 a_cdif a_cun a_cvv p_ineq12i f3_dfif4 f4_dfif4 a_cun p_inv1 f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f4_dfif4 f3_dfif4 a_cun f4_dfif4 a_cvv f4_dfif4 a_cdif a_cun a_cin f3_dfif4 f4_dfif4 a_cun a_cvv a_cin f3_dfif4 f4_dfif4 a_cun p_3eqtri f2_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f2_dfif4 f3_dfif4 a_cun f2_dfif4 a_cvv f4_dfif4 a_cdif a_cun a_cin f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f3_dfif4 f4_dfif4 a_cun p_ineq12i f2_dfif4 f3_dfif4 a_cun f2_dfif4 a_cvv f4_dfif4 a_cdif a_cun f3_dfif4 f4_dfif4 a_cun p_inass f2_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun a_cin f2_dfif4 f3_dfif4 a_cun f2_dfif4 a_cvv f4_dfif4 a_cdif a_cun a_cin f3_dfif4 f4_dfif4 a_cun a_cin f2_dfif4 f3_dfif4 a_cun f2_dfif4 a_cvv f4_dfif4 a_cdif a_cun f3_dfif4 f4_dfif4 a_cun a_cin a_cin p_eqtri f0_dfif4 f2_dfif4 f3_dfif4 a_cif f2_dfif4 f4_dfif4 a_cin f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f2_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun f4_dfif4 f3_dfif4 a_cvv f4_dfif4 a_cdif a_cin a_cun a_cin f2_dfif4 f3_dfif4 a_cun f2_dfif4 a_cvv f4_dfif4 a_cdif a_cun f3_dfif4 f4_dfif4 a_cun a_cin a_cin p_3eqtri $.
$}

$(Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false (see also
       ~ abvor0 ).  (Contributed by G&eacute;rard Lang, 18-Aug-2013.) $)

${
	$v ph x A B C  $.
	$d A  $.
	$d B  $.
	$d x ph  $.
	f0_dfif5 $f wff ph $.
	f1_dfif5 $f set x $.
	f2_dfif5 $f class A $.
	f3_dfif5 $f class B $.
	f4_dfif5 $f class C $.
	e0_dfif5 $e |- C = { x | ph } $.
	p_dfif5 $p |- if ( ph , A , B ) = ( ( A i^i B ) u. ( ( ( A \ B ) i^i C ) u. ( ( B \ A ) i^i ( _V \ C ) ) ) ) $= f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun f3_dfif5 f4_dfif5 a_cun p_inindi e0_dfif5 f0_dfif5 f1_dfif5 f2_dfif5 f3_dfif5 f4_dfif5 p_dfif4 f2_dfif5 f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun p_undir f2_dfif5 p_unidm f2_dfif5 f2_dfif5 a_cun f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin p_uneq1i f2_dfif5 f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin p_unass f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif p_undi f2_dfif5 f2_dfif5 a_cun f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun f2_dfif5 f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin p_3eqtr3ri f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 p_undi f2_dfif5 f3_dfif5 p_undifabs f2_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f2_dfif5 f2_dfif5 f4_dfif5 a_cun p_ineq1i f2_dfif5 f4_dfif5 p_inabs f2_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f2_dfif5 f4_dfif5 a_cun a_cin f2_dfif5 f2_dfif5 f4_dfif5 a_cun a_cin f2_dfif5 p_eqtri f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f2_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f2_dfif5 f4_dfif5 a_cun a_cin f2_dfif5 p_eqtri f2_dfif5 f3_dfif5 p_undif2 f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cun f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun p_ineq1i f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif p_undi f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif p_undi f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun p_3eqtr4i f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f2_dfif5 f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun p_uneq12i f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f2_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun p_eqtr4i f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin p_unundi f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f2_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun p_eqtr4i f2_dfif5 f4_dfif5 a_cin f3_dfif5 f3_dfif5 p_unass f3_dfif5 f2_dfif5 f4_dfif5 p_undi f2_dfif5 f4_dfif5 a_cin f3_dfif5 p_uncom f3_dfif5 f2_dfif5 p_undif2 f3_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f3_dfif5 f2_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun p_ineq1i f3_dfif5 f2_dfif5 f4_dfif5 a_cin a_cun f3_dfif5 f2_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f3_dfif5 f4_dfif5 a_cun a_cin p_3eqtr4i f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 p_undi f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif a_cun f3_dfif5 f4_dfif5 a_cun a_cin f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun p_eqtr4i f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif p_undi f3_dfif5 f2_dfif5 p_undifabs f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cun f3_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cun p_ineq1i f3_dfif5 a_cvv f4_dfif5 a_cdif p_inabs f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cun f3_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f3_dfif5 f3_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f3_dfif5 p_3eqtrri f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f3_dfif5 f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun p_uneq12i f3_dfif5 p_unidm f3_dfif5 f3_dfif5 a_cun f3_dfif5 f2_dfif5 f4_dfif5 a_cin p_uneq2i f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun f3_dfif5 a_cun f2_dfif5 f4_dfif5 a_cin f3_dfif5 f3_dfif5 a_cun a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun p_3eqtr3ri f3_dfif5 f4_dfif5 p_uncom f3_dfif5 f4_dfif5 a_cun f4_dfif5 f3_dfif5 a_cun f2_dfif5 f3_dfif5 a_cun p_ineq2i f2_dfif5 f4_dfif5 f3_dfif5 p_undir f2_dfif5 f3_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin f2_dfif5 f3_dfif5 a_cun f4_dfif5 f3_dfif5 a_cun a_cin f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun p_eqtr4i f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin p_unundi f2_dfif5 f4_dfif5 a_cin f3_dfif5 a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin a_cun f3_dfif5 f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f3_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun p_3eqtr4i f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f3_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun p_ineq12i f2_dfif5 f3_dfif5 a_cin f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f2_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun f3_dfif5 f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun a_cin f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f3_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin a_cin p_eqtr4i f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun f3_dfif5 f4_dfif5 a_cun a_cin a_cin f2_dfif5 f3_dfif5 a_cun f2_dfif5 a_cvv f4_dfif5 a_cdif a_cun a_cin f2_dfif5 f3_dfif5 a_cun f3_dfif5 f4_dfif5 a_cun a_cin a_cin f0_dfif5 f2_dfif5 f3_dfif5 a_cif f2_dfif5 f3_dfif5 a_cin f2_dfif5 f3_dfif5 a_cdif f4_dfif5 a_cin f3_dfif5 f2_dfif5 a_cdif a_cvv f4_dfif5 a_cdif a_cin a_cun a_cun p_3eqtr4i $.
$}

$(Equality theorem for conditional operators.  (Contributed by NM,
     1-Sep-2004.) $)

${
	$v ph A B C D  $.
	f0_ifeq12 $f wff ph $.
	f1_ifeq12 $f class A $.
	f2_ifeq12 $f class B $.
	f3_ifeq12 $f class C $.
	f4_ifeq12 $f class D $.
	p_ifeq12 $p |- ( ( A = B /\ C = D ) -> if ( ph , A , C ) = if ( ph , B , D ) ) $= f0_ifeq12 f1_ifeq12 f2_ifeq12 f3_ifeq12 p_ifeq1 f0_ifeq12 f3_ifeq12 f4_ifeq12 f2_ifeq12 p_ifeq2 f1_ifeq12 f2_ifeq12 a_wceq f3_ifeq12 f4_ifeq12 a_wceq f0_ifeq12 f1_ifeq12 f3_ifeq12 a_cif f0_ifeq12 f2_ifeq12 f3_ifeq12 a_cif f0_ifeq12 f2_ifeq12 f4_ifeq12 a_cif p_sylan9eq $.
$}

$(Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)

${
	$v ph ps A B C  $.
	f0_ifeq1d $f wff ph $.
	f1_ifeq1d $f wff ps $.
	f2_ifeq1d $f class A $.
	f3_ifeq1d $f class B $.
	f4_ifeq1d $f class C $.
	e0_ifeq1d $e |- ( ph -> A = B ) $.
	p_ifeq1d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $= e0_ifeq1d f1_ifeq1d f2_ifeq1d f3_ifeq1d f4_ifeq1d p_ifeq1 f0_ifeq1d f2_ifeq1d f3_ifeq1d a_wceq f1_ifeq1d f2_ifeq1d f4_ifeq1d a_cif f1_ifeq1d f3_ifeq1d f4_ifeq1d a_cif a_wceq p_syl $.
$}

$(Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)

${
	$v ph ps A B C  $.
	f0_ifeq2d $f wff ph $.
	f1_ifeq2d $f wff ps $.
	f2_ifeq2d $f class A $.
	f3_ifeq2d $f class B $.
	f4_ifeq2d $f class C $.
	e0_ifeq2d $e |- ( ph -> A = B ) $.
	p_ifeq2d $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $= e0_ifeq2d f1_ifeq2d f2_ifeq2d f3_ifeq2d f4_ifeq2d p_ifeq2 f0_ifeq2d f2_ifeq2d f3_ifeq2d a_wceq f1_ifeq2d f4_ifeq2d f2_ifeq2d a_cif f1_ifeq2d f4_ifeq2d f3_ifeq2d a_cif a_wceq p_syl $.
$}

$(Equality deduction for conditional operator.  (Contributed by NM,
       24-Mar-2015.) $)

${
	$v ph ps A B C D  $.
	f0_ifeq12d $f wff ph $.
	f1_ifeq12d $f wff ps $.
	f2_ifeq12d $f class A $.
	f3_ifeq12d $f class B $.
	f4_ifeq12d $f class C $.
	f5_ifeq12d $f class D $.
	e0_ifeq12d $e |- ( ph -> A = B ) $.
	e1_ifeq12d $e |- ( ph -> C = D ) $.
	p_ifeq12d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , D ) ) $= e0_ifeq12d f0_ifeq12d f1_ifeq12d f2_ifeq12d f3_ifeq12d f4_ifeq12d p_ifeq1d e1_ifeq12d f0_ifeq12d f1_ifeq12d f4_ifeq12d f5_ifeq12d f3_ifeq12d p_ifeq2d f0_ifeq12d f1_ifeq12d f2_ifeq12d f4_ifeq12d a_cif f1_ifeq12d f3_ifeq12d f4_ifeq12d a_cif f1_ifeq12d f3_ifeq12d f5_ifeq12d a_cif p_eqtrd $.
$}

$(Equivalence theorem for conditional operators.  (Contributed by Raph
     Levien, 15-Jan-2004.) $)

${
	$v ph ps A B  $.
	f0_ifbi $f wff ph $.
	f1_ifbi $f wff ps $.
	f2_ifbi $f class A $.
	f3_ifbi $f class B $.
	p_ifbi $p |- ( ( ph <-> ps ) -> if ( ph , A , B ) = if ( ps , A , B ) ) $= f0_ifbi f1_ifbi p_dfbi3 f0_ifbi f2_ifbi f3_ifbi p_iftrue f1_ifbi f2_ifbi f3_ifbi p_iftrue f1_ifbi f1_ifbi f2_ifbi f3_ifbi a_cif f2_ifbi p_eqcomd f0_ifbi f1_ifbi f0_ifbi f2_ifbi f3_ifbi a_cif f2_ifbi f1_ifbi f2_ifbi f3_ifbi a_cif p_sylan9eq f0_ifbi f2_ifbi f3_ifbi p_iffalse f1_ifbi f2_ifbi f3_ifbi p_iffalse f1_ifbi a_wn f1_ifbi f2_ifbi f3_ifbi a_cif f3_ifbi p_eqcomd f0_ifbi a_wn f1_ifbi a_wn f0_ifbi f2_ifbi f3_ifbi a_cif f3_ifbi f1_ifbi f2_ifbi f3_ifbi a_cif p_sylan9eq f0_ifbi f1_ifbi a_wa f0_ifbi f2_ifbi f3_ifbi a_cif f1_ifbi f2_ifbi f3_ifbi a_cif a_wceq f0_ifbi a_wn f1_ifbi a_wn a_wa p_jaoi f0_ifbi f1_ifbi a_wb f0_ifbi f1_ifbi a_wa f0_ifbi a_wn f1_ifbi a_wn a_wa a_wo f0_ifbi f2_ifbi f3_ifbi a_cif f1_ifbi f2_ifbi f3_ifbi a_cif a_wceq p_sylbi $.
$}

$(Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Apr-2005.) $)

${
	$v ph ps ch A B  $.
	f0_ifbid $f wff ph $.
	f1_ifbid $f wff ps $.
	f2_ifbid $f wff ch $.
	f3_ifbid $f class A $.
	f4_ifbid $f class B $.
	e0_ifbid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_ifbid $p |- ( ph -> if ( ps , A , B ) = if ( ch , A , B ) ) $= e0_ifbid f1_ifbid f2_ifbid f3_ifbid f4_ifbid p_ifbi f0_ifbid f1_ifbid f2_ifbid a_wb f1_ifbid f3_ifbid f4_ifbid a_cif f2_ifbid f3_ifbid f4_ifbid a_cif a_wceq p_syl $.
$}

$(Equivalence/equality inference for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)

${
	$v ph ps A B C  $.
	f0_ifbieq2i $f wff ph $.
	f1_ifbieq2i $f wff ps $.
	f2_ifbieq2i $f class A $.
	f3_ifbieq2i $f class B $.
	f4_ifbieq2i $f class C $.
	e0_ifbieq2i $e |- ( ph <-> ps ) $.
	e1_ifbieq2i $e |- A = B $.
	p_ifbieq2i $p |- if ( ph , C , A ) = if ( ps , C , B ) $= e0_ifbieq2i f0_ifbieq2i f1_ifbieq2i f4_ifbieq2i f2_ifbieq2i p_ifbi f0_ifbieq2i f1_ifbieq2i a_wb f0_ifbieq2i f4_ifbieq2i f2_ifbieq2i a_cif f1_ifbieq2i f4_ifbieq2i f2_ifbieq2i a_cif a_wceq a_ax-mp e1_ifbieq2i f1_ifbieq2i f2_ifbieq2i f3_ifbieq2i f4_ifbieq2i p_ifeq2 f2_ifbieq2i f3_ifbieq2i a_wceq f1_ifbieq2i f4_ifbieq2i f2_ifbieq2i a_cif f1_ifbieq2i f4_ifbieq2i f3_ifbieq2i a_cif a_wceq a_ax-mp f0_ifbieq2i f4_ifbieq2i f2_ifbieq2i a_cif f1_ifbieq2i f4_ifbieq2i f2_ifbieq2i a_cif f1_ifbieq2i f4_ifbieq2i f3_ifbieq2i a_cif p_eqtri $.
$}

$(Equivalence/equality deduction for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)

${
	$v ph ps ch A B C  $.
	f0_ifbieq2d $f wff ph $.
	f1_ifbieq2d $f wff ps $.
	f2_ifbieq2d $f wff ch $.
	f3_ifbieq2d $f class A $.
	f4_ifbieq2d $f class B $.
	f5_ifbieq2d $f class C $.
	e0_ifbieq2d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_ifbieq2d $e |- ( ph -> A = B ) $.
	p_ifbieq2d $p |- ( ph -> if ( ps , C , A ) = if ( ch , C , B ) ) $= e0_ifbieq2d f0_ifbieq2d f1_ifbieq2d f2_ifbieq2d f5_ifbieq2d f3_ifbieq2d p_ifbid e1_ifbieq2d f0_ifbieq2d f2_ifbieq2d f3_ifbieq2d f4_ifbieq2d f5_ifbieq2d p_ifeq2d f0_ifbieq2d f1_ifbieq2d f5_ifbieq2d f3_ifbieq2d a_cif f2_ifbieq2d f5_ifbieq2d f3_ifbieq2d a_cif f2_ifbieq2d f5_ifbieq2d f4_ifbieq2d a_cif p_eqtrd $.
$}

$(Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Mar-2013.) $)

${
	$v ph ps A B C D  $.
	f0_ifbieq12i $f wff ph $.
	f1_ifbieq12i $f wff ps $.
	f2_ifbieq12i $f class A $.
	f3_ifbieq12i $f class B $.
	f4_ifbieq12i $f class C $.
	f5_ifbieq12i $f class D $.
	e0_ifbieq12i $e |- ( ph <-> ps ) $.
	e1_ifbieq12i $e |- A = C $.
	e2_ifbieq12i $e |- B = D $.
	p_ifbieq12i $p |- if ( ph , A , B ) = if ( ps , C , D ) $= e1_ifbieq12i f0_ifbieq12i f2_ifbieq12i f4_ifbieq12i f3_ifbieq12i p_ifeq1 f2_ifbieq12i f4_ifbieq12i a_wceq f0_ifbieq12i f2_ifbieq12i f3_ifbieq12i a_cif f0_ifbieq12i f4_ifbieq12i f3_ifbieq12i a_cif a_wceq a_ax-mp e0_ifbieq12i e2_ifbieq12i f0_ifbieq12i f1_ifbieq12i f3_ifbieq12i f5_ifbieq12i f4_ifbieq12i p_ifbieq2i f0_ifbieq12i f2_ifbieq12i f3_ifbieq12i a_cif f0_ifbieq12i f4_ifbieq12i f3_ifbieq12i a_cif f1_ifbieq12i f4_ifbieq12i f5_ifbieq12i a_cif p_eqtri $.
$}

$(Equivalence deduction for conditional operators.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)

${
	$v ph ps ch A B C D  $.
	f0_ifbieq12d $f wff ph $.
	f1_ifbieq12d $f wff ps $.
	f2_ifbieq12d $f wff ch $.
	f3_ifbieq12d $f class A $.
	f4_ifbieq12d $f class B $.
	f5_ifbieq12d $f class C $.
	f6_ifbieq12d $f class D $.
	e0_ifbieq12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_ifbieq12d $e |- ( ph -> A = C ) $.
	e2_ifbieq12d $e |- ( ph -> B = D ) $.
	p_ifbieq12d $p |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) ) $= e0_ifbieq12d f0_ifbieq12d f1_ifbieq12d f2_ifbieq12d f3_ifbieq12d f4_ifbieq12d p_ifbid e1_ifbieq12d e2_ifbieq12d f0_ifbieq12d f2_ifbieq12d f3_ifbieq12d f5_ifbieq12d f4_ifbieq12d f6_ifbieq12d p_ifeq12d f0_ifbieq12d f1_ifbieq12d f3_ifbieq12d f4_ifbieq12d a_cif f2_ifbieq12d f3_ifbieq12d f4_ifbieq12d a_cif f2_ifbieq12d f5_ifbieq12d f6_ifbieq12d a_cif p_eqtrd $.
$}

$(Deduction version of ~ nfif .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	$d y ph  $.
	$d y ps  $.
	f0_nfifd $f wff ph $.
	f1_nfifd $f wff ps $.
	f2_nfifd $f set x $.
	f3_nfifd $f class A $.
	f4_nfifd $f class B $.
	i0_nfifd $f set y $.
	e0_nfifd $e |- ( ph -> F/ x ps ) $.
	e1_nfifd $e |- ( ph -> F/_ x A ) $.
	e2_nfifd $e |- ( ph -> F/_ x B ) $.
	p_nfifd $p |- ( ph -> F/_ x if ( ps , A , B ) ) $= f1_nfifd i0_nfifd f3_nfifd f4_nfifd p_dfif2 f0_nfifd i0_nfifd p_nfv e2_nfifd f0_nfifd f2_nfifd i0_nfifd f4_nfifd p_nfcrd e0_nfifd f0_nfifd i0_nfifd a_sup_set_class f4_nfifd a_wcel f1_nfifd f2_nfifd p_nfimd e1_nfifd f0_nfifd f2_nfifd i0_nfifd f3_nfifd p_nfcrd e0_nfifd f0_nfifd i0_nfifd a_sup_set_class f3_nfifd a_wcel f1_nfifd f2_nfifd p_nfand f0_nfifd i0_nfifd a_sup_set_class f4_nfifd a_wcel f1_nfifd a_wi i0_nfifd a_sup_set_class f3_nfifd a_wcel f1_nfifd a_wa f2_nfifd p_nfimd f0_nfifd i0_nfifd a_sup_set_class f4_nfifd a_wcel f1_nfifd a_wi i0_nfifd a_sup_set_class f3_nfifd a_wcel f1_nfifd a_wa a_wi f2_nfifd i0_nfifd p_nfabd f0_nfifd f2_nfifd f1_nfifd f3_nfifd f4_nfifd a_cif i0_nfifd a_sup_set_class f4_nfifd a_wcel f1_nfifd a_wi i0_nfifd a_sup_set_class f3_nfifd a_wcel f1_nfifd a_wa a_wi i0_nfifd a_cab p_nfcxfrd $.
$}

$(Bound-variable hypothesis builder for a conditional operator.
       (Contributed by NM, 16-Feb-2005.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)

${
	$v ph x A B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	$d ph  $.
	f0_nfif $f wff ph $.
	f1_nfif $f set x $.
	f2_nfif $f class A $.
	f3_nfif $f class B $.
	e0_nfif $e |- F/ x ph $.
	e1_nfif $e |- F/_ x A $.
	e2_nfif $e |- F/_ x B $.
	p_nfif $p |- F/_ x if ( ph , A , B ) $= e0_nfif f0_nfif f1_nfif a_wnf a_wtru p_a1i e1_nfif f1_nfif f2_nfif a_wnfc a_wtru p_a1i e2_nfif f1_nfif f3_nfif a_wnfc a_wtru p_a1i a_wtru f0_nfif f1_nfif f2_nfif f3_nfif p_nfifd f1_nfif f0_nfif f2_nfif f3_nfif a_cif a_wnfc p_trud $.
$}

$(Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)

${
	$v ph ps A B C  $.
	f0_ifeq1da $f wff ph $.
	f1_ifeq1da $f wff ps $.
	f2_ifeq1da $f class A $.
	f3_ifeq1da $f class B $.
	f4_ifeq1da $f class C $.
	e0_ifeq1da $e |- ( ( ph /\ ps ) -> A = B ) $.
	p_ifeq1da $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $= e0_ifeq1da f0_ifeq1da f1_ifeq1da a_wa f1_ifeq1da f2_ifeq1da f3_ifeq1da f4_ifeq1da p_ifeq1d f1_ifeq1da f2_ifeq1da f4_ifeq1da p_iffalse f1_ifeq1da f3_ifeq1da f4_ifeq1da p_iffalse f1_ifeq1da a_wn f1_ifeq1da f2_ifeq1da f4_ifeq1da a_cif f4_ifeq1da f1_ifeq1da f3_ifeq1da f4_ifeq1da a_cif p_eqtr4d f1_ifeq1da a_wn f1_ifeq1da f2_ifeq1da f4_ifeq1da a_cif f1_ifeq1da f3_ifeq1da f4_ifeq1da a_cif a_wceq f0_ifeq1da p_adantl f0_ifeq1da f1_ifeq1da f1_ifeq1da f2_ifeq1da f4_ifeq1da a_cif f1_ifeq1da f3_ifeq1da f4_ifeq1da a_cif a_wceq p_pm2.61dan $.
$}

$(Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)

${
	$v ph ps A B C  $.
	f0_ifeq2da $f wff ph $.
	f1_ifeq2da $f wff ps $.
	f2_ifeq2da $f class A $.
	f3_ifeq2da $f class B $.
	f4_ifeq2da $f class C $.
	e0_ifeq2da $e |- ( ( ph /\ -. ps ) -> A = B ) $.
	p_ifeq2da $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $= f1_ifeq2da f4_ifeq2da f2_ifeq2da p_iftrue f1_ifeq2da f4_ifeq2da f3_ifeq2da p_iftrue f1_ifeq2da f1_ifeq2da f4_ifeq2da f2_ifeq2da a_cif f4_ifeq2da f1_ifeq2da f4_ifeq2da f3_ifeq2da a_cif p_eqtr4d f1_ifeq2da f1_ifeq2da f4_ifeq2da f2_ifeq2da a_cif f1_ifeq2da f4_ifeq2da f3_ifeq2da a_cif a_wceq f0_ifeq2da p_adantl e0_ifeq2da f0_ifeq2da f1_ifeq2da a_wn a_wa f1_ifeq2da f2_ifeq2da f3_ifeq2da f4_ifeq2da p_ifeq2d f0_ifeq2da f1_ifeq2da f1_ifeq2da f4_ifeq2da f2_ifeq2da a_cif f1_ifeq2da f4_ifeq2da f3_ifeq2da a_cif a_wceq p_pm2.61dan $.
$}

$(Conditional closure.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)

${
	$v ph ps A B C  $.
	f0_ifclda $f wff ph $.
	f1_ifclda $f wff ps $.
	f2_ifclda $f class A $.
	f3_ifclda $f class B $.
	f4_ifclda $f class C $.
	e0_ifclda $e |- ( ( ph /\ ps ) -> A e. C ) $.
	e1_ifclda $e |- ( ( ph /\ -. ps ) -> B e. C ) $.
	p_ifclda $p |- ( ph -> if ( ps , A , B ) e. C ) $= f1_ifclda f2_ifclda f3_ifclda p_iftrue f1_ifclda f1_ifclda f2_ifclda f3_ifclda a_cif f2_ifclda a_wceq f0_ifclda p_adantl e0_ifclda f0_ifclda f1_ifclda a_wa f1_ifclda f2_ifclda f3_ifclda a_cif f2_ifclda f4_ifclda p_eqeltrd f1_ifclda f2_ifclda f3_ifclda p_iffalse f1_ifclda a_wn f1_ifclda f2_ifclda f3_ifclda a_cif f3_ifclda a_wceq f0_ifclda p_adantl e1_ifclda f0_ifclda f1_ifclda a_wn a_wa f1_ifclda f2_ifclda f3_ifclda a_cif f3_ifclda f4_ifclda p_eqeltrd f0_ifclda f1_ifclda f1_ifclda f2_ifclda f3_ifclda a_cif f4_ifclda a_wcel p_pm2.61dan $.
$}

$(Distribute proper substitution through the conditional operator.
       (Contributed by NM, 24-Feb-2013.)  (Revised by Mario Carneiro,
       14-Nov-2016.) $)

${
	$v ph x A B C V  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d y ph  $.
	$d x y  $.
	f0_csbifg $f wff ph $.
	f1_csbifg $f set x $.
	f2_csbifg $f class A $.
	f3_csbifg $f class B $.
	f4_csbifg $f class C $.
	f5_csbifg $f class V $.
	i0_csbifg $f set y $.
	p_csbifg $p |- ( A e. V -> [_ A / x ]_ if ( ph , B , C ) = if ( [. A / x ]. ph , [_ A / x ]_ B , [_ A / x ]_ C ) ) $= f1_csbifg i0_csbifg a_sup_set_class f2_csbifg f0_csbifg f3_csbifg f4_csbifg a_cif p_csbeq1 f0_csbifg f1_csbifg i0_csbifg f2_csbifg p_dfsbcq2 f1_csbifg i0_csbifg a_sup_set_class f2_csbifg f3_csbifg p_csbeq1 f1_csbifg i0_csbifg a_sup_set_class f2_csbifg f4_csbifg p_csbeq1 i0_csbifg a_sup_set_class f2_csbifg a_wceq f0_csbifg f1_csbifg i0_csbifg a_wsb f0_csbifg f1_csbifg f2_csbifg a_wsbc f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb f1_csbifg f2_csbifg f3_csbifg a_csb f1_csbifg f2_csbifg f4_csbifg a_csb p_ifbieq12d i0_csbifg a_sup_set_class f2_csbifg a_wceq f1_csbifg i0_csbifg a_sup_set_class f0_csbifg f3_csbifg f4_csbifg a_cif a_csb f1_csbifg f2_csbifg f0_csbifg f3_csbifg f4_csbifg a_cif a_csb f0_csbifg f1_csbifg i0_csbifg a_wsb f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb a_cif f0_csbifg f1_csbifg f2_csbifg a_wsbc f1_csbifg f2_csbifg f3_csbifg a_csb f1_csbifg f2_csbifg f4_csbifg a_csb a_cif p_eqeq12d i0_csbifg p_vex f0_csbifg f1_csbifg i0_csbifg p_nfs1v f1_csbifg i0_csbifg a_sup_set_class f3_csbifg p_nfcsb1v f1_csbifg i0_csbifg a_sup_set_class f4_csbifg p_nfcsb1v f0_csbifg f1_csbifg i0_csbifg a_wsb f1_csbifg f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb p_nfif f0_csbifg f1_csbifg i0_csbifg p_sbequ12 f1_csbifg i0_csbifg a_sup_set_class f3_csbifg p_csbeq1a f1_csbifg i0_csbifg a_sup_set_class f4_csbifg p_csbeq1a f1_csbifg a_sup_set_class i0_csbifg a_sup_set_class a_wceq f0_csbifg f0_csbifg f1_csbifg i0_csbifg a_wsb f3_csbifg f4_csbifg f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb p_ifbieq12d f1_csbifg i0_csbifg a_sup_set_class f0_csbifg f3_csbifg f4_csbifg a_cif f0_csbifg f1_csbifg i0_csbifg a_wsb f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb a_cif p_csbief f1_csbifg i0_csbifg a_sup_set_class f0_csbifg f3_csbifg f4_csbifg a_cif a_csb f0_csbifg f1_csbifg i0_csbifg a_wsb f1_csbifg i0_csbifg a_sup_set_class f3_csbifg a_csb f1_csbifg i0_csbifg a_sup_set_class f4_csbifg a_csb a_cif a_wceq f1_csbifg f2_csbifg f0_csbifg f3_csbifg f4_csbifg a_cif a_csb f0_csbifg f1_csbifg f2_csbifg a_wsbc f1_csbifg f2_csbifg f3_csbifg a_csb f1_csbifg f2_csbifg f4_csbifg a_csb a_cif a_wceq i0_csbifg f2_csbifg f5_csbifg p_vtoclg $.
$}

$(Elimination of a conditional operator contained in a wff ` ps ` .
       (Contributed by NM, 15-Feb-2005.) $)

${
	$v ph ps ch th A B  $.
	f0_elimif $f wff ph $.
	f1_elimif $f wff ps $.
	f2_elimif $f wff ch $.
	f3_elimif $f wff th $.
	f4_elimif $f class A $.
	f5_elimif $f class B $.
	e0_elimif $e |- ( if ( ph , A , B ) = A -> ( ps <-> ch ) ) $.
	e1_elimif $e |- ( if ( ph , A , B ) = B -> ( ps <-> th ) ) $.
	p_elimif $p |- ( ps <-> ( ( ph /\ ch ) \/ ( -. ph /\ th ) ) ) $= f0_elimif p_exmid f0_elimif f0_elimif a_wn a_wo f1_elimif p_biantrur f0_elimif f0_elimif a_wn f1_elimif p_andir f0_elimif f4_elimif f5_elimif p_iftrue e0_elimif f0_elimif f0_elimif f4_elimif f5_elimif a_cif f4_elimif a_wceq f1_elimif f2_elimif a_wb p_syl f0_elimif f1_elimif f2_elimif p_pm5.32i f0_elimif f4_elimif f5_elimif p_iffalse e1_elimif f0_elimif a_wn f0_elimif f4_elimif f5_elimif a_cif f5_elimif a_wceq f1_elimif f3_elimif a_wb p_syl f0_elimif a_wn f1_elimif f3_elimif p_pm5.32i f0_elimif f1_elimif a_wa f0_elimif f2_elimif a_wa f0_elimif a_wn f1_elimif a_wa f0_elimif a_wn f3_elimif a_wa p_orbi12i f1_elimif f0_elimif f0_elimif a_wn a_wo f1_elimif a_wa f0_elimif f1_elimif a_wa f0_elimif a_wn f1_elimif a_wa a_wo f0_elimif f2_elimif a_wa f0_elimif a_wn f3_elimif a_wa a_wo p_3bitri $.
$}

$(A wff ` th ` containing a conditional operator is true when both of
         its cases are true.  (Contributed by NM, 15-Feb-2015.) $)

${
	$v ph ps ch th et A B  $.
	f0_ifbothda $f wff ph $.
	f1_ifbothda $f wff ps $.
	f2_ifbothda $f wff ch $.
	f3_ifbothda $f wff th $.
	f4_ifbothda $f wff et $.
	f5_ifbothda $f class A $.
	f6_ifbothda $f class B $.
	e0_ifbothda $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	e1_ifbothda $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	e2_ifbothda $e |- ( ( et /\ ph ) -> ps ) $.
	e3_ifbothda $e |- ( ( et /\ -. ph ) -> ch ) $.
	p_ifbothda $p |- ( et -> th ) $= e2_ifbothda f0_ifbothda f5_ifbothda f6_ifbothda p_iftrue f0_ifbothda f0_ifbothda f5_ifbothda f6_ifbothda a_cif f5_ifbothda p_eqcomd e0_ifbothda f0_ifbothda f5_ifbothda f0_ifbothda f5_ifbothda f6_ifbothda a_cif a_wceq f1_ifbothda f3_ifbothda a_wb p_syl f0_ifbothda f1_ifbothda f3_ifbothda a_wb f4_ifbothda p_adantl f4_ifbothda f0_ifbothda a_wa f1_ifbothda f3_ifbothda p_mpbid e3_ifbothda f0_ifbothda f5_ifbothda f6_ifbothda p_iffalse f0_ifbothda a_wn f0_ifbothda f5_ifbothda f6_ifbothda a_cif f6_ifbothda p_eqcomd e1_ifbothda f0_ifbothda a_wn f6_ifbothda f0_ifbothda f5_ifbothda f6_ifbothda a_cif a_wceq f2_ifbothda f3_ifbothda a_wb p_syl f0_ifbothda a_wn f2_ifbothda f3_ifbothda a_wb f4_ifbothda p_adantl f4_ifbothda f0_ifbothda a_wn a_wa f2_ifbothda f3_ifbothda p_mpbid f4_ifbothda f0_ifbothda f3_ifbothda p_pm2.61dan $.
$}

$(A wff ` th ` containing a conditional operator is true when both of its
       cases are true.  (Contributed by NM, 3-Sep-2006.)  (Revised by Mario
       Carneiro, 15-Feb-2015.) $)

${
	$v ph ps ch th A B  $.
	f0_ifboth $f wff ph $.
	f1_ifboth $f wff ps $.
	f2_ifboth $f wff ch $.
	f3_ifboth $f wff th $.
	f4_ifboth $f class A $.
	f5_ifboth $f class B $.
	e0_ifboth $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	e1_ifboth $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	p_ifboth $p |- ( ( ps /\ ch ) -> th ) $= e0_ifboth e1_ifboth f1_ifboth f2_ifboth f0_ifboth p_simpll f1_ifboth f2_ifboth f0_ifboth a_wn p_simplr f0_ifboth f1_ifboth f2_ifboth f3_ifboth f1_ifboth f2_ifboth a_wa f4_ifboth f5_ifboth p_ifbothda $.
$}

$(Identical true and false arguments in the conditional operator.
     (Contributed by NM, 18-Apr-2005.) $)

${
	$v ph A  $.
	f0_ifid $f wff ph $.
	f1_ifid $f class A $.
	p_ifid $p |- if ( ph , A , A ) = A $= f0_ifid f1_ifid f1_ifid p_iftrue f0_ifid f1_ifid f1_ifid p_iffalse f0_ifid f0_ifid f1_ifid f1_ifid a_cif f1_ifid a_wceq p_pm2.61i $.
$}

$(Expansion of an equality with a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)

${
	$v ph A B C  $.
	f0_eqif $f wff ph $.
	f1_eqif $f class A $.
	f2_eqif $f class B $.
	f3_eqif $f class C $.
	p_eqif $p |- ( A = if ( ph , B , C ) <-> ( ( ph /\ A = B ) \/ ( -. ph /\ A = C ) ) ) $= f0_eqif f2_eqif f3_eqif a_cif f2_eqif f1_eqif p_eqeq2 f0_eqif f2_eqif f3_eqif a_cif f3_eqif f1_eqif p_eqeq2 f0_eqif f1_eqif f0_eqif f2_eqif f3_eqif a_cif a_wceq f1_eqif f2_eqif a_wceq f1_eqif f3_eqif a_wceq f2_eqif f3_eqif p_elimif $.
$}

$(Membership in a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)

${
	$v ph A B C  $.
	f0_elif $f wff ph $.
	f1_elif $f class A $.
	f2_elif $f class B $.
	f3_elif $f class C $.
	p_elif $p |- ( A e. if ( ph , B , C ) <-> ( ( ph /\ A e. B ) \/ ( -. ph /\ A e. C ) ) ) $= f0_elif f2_elif f3_elif a_cif f2_elif f1_elif p_eleq2 f0_elif f2_elif f3_elif a_cif f3_elif f1_elif p_eleq2 f0_elif f1_elif f0_elif f2_elif f3_elif a_cif a_wcel f1_elif f2_elif a_wcel f1_elif f3_elif a_wcel f2_elif f3_elif p_elimif $.
$}

$(Membership of a conditional operator.  (Contributed by NM,
     10-Sep-2005.) $)

${
	$v ph A B C  $.
	f0_ifel $f wff ph $.
	f1_ifel $f class A $.
	f2_ifel $f class B $.
	f3_ifel $f class C $.
	p_ifel $p |- ( if ( ph , A , B ) e. C <-> ( ( ph /\ A e. C ) \/ ( -. ph /\ B e. C ) ) ) $= f0_ifel f1_ifel f2_ifel a_cif f1_ifel f3_ifel p_eleq1 f0_ifel f1_ifel f2_ifel a_cif f2_ifel f3_ifel p_eleq1 f0_ifel f0_ifel f1_ifel f2_ifel a_cif f3_ifel a_wcel f1_ifel f3_ifel a_wcel f2_ifel f3_ifel a_wcel f1_ifel f2_ifel p_elimif $.
$}

$(Membership (closure) of a conditional operator.  (Contributed by NM,
     4-Apr-2005.) $)

${
	$v ph A B C  $.
	f0_ifcl $f wff ph $.
	f1_ifcl $f class A $.
	f2_ifcl $f class B $.
	f3_ifcl $f class C $.
	p_ifcl $p |- ( ( A e. C /\ B e. C ) -> if ( ph , A , B ) e. C ) $= f1_ifcl f0_ifcl f1_ifcl f2_ifcl a_cif f3_ifcl p_eleq1 f2_ifcl f0_ifcl f1_ifcl f2_ifcl a_cif f3_ifcl p_eleq1 f0_ifcl f1_ifcl f3_ifcl a_wcel f2_ifcl f3_ifcl a_wcel f0_ifcl f1_ifcl f2_ifcl a_cif f3_ifcl a_wcel f1_ifcl f2_ifcl p_ifboth $.
$}

$(The possible values of a conditional operator.  (Contributed by NM,
     17-Jun-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph A B  $.
	f0_ifeqor $f wff ph $.
	f1_ifeqor $f class A $.
	f2_ifeqor $f class B $.
	p_ifeqor $p |- ( if ( ph , A , B ) = A \/ if ( ph , A , B ) = B ) $= f0_ifeqor f1_ifeqor f2_ifeqor p_iftrue f0_ifeqor f0_ifeqor f1_ifeqor f2_ifeqor a_cif f1_ifeqor a_wceq p_con3i f0_ifeqor f1_ifeqor f2_ifeqor p_iffalse f0_ifeqor f1_ifeqor f2_ifeqor a_cif f1_ifeqor a_wceq a_wn f0_ifeqor a_wn f0_ifeqor f1_ifeqor f2_ifeqor a_cif f2_ifeqor a_wceq p_syl f0_ifeqor f1_ifeqor f2_ifeqor a_cif f1_ifeqor a_wceq f0_ifeqor f1_ifeqor f2_ifeqor a_cif f2_ifeqor a_wceq p_orri $.
$}

$(Negating the first argument swaps the last two arguments of a conditional
     operator.  (Contributed by NM, 21-Jun-2007.) $)

${
	$v ph A B  $.
	f0_ifnot $f wff ph $.
	f1_ifnot $f class A $.
	f2_ifnot $f class B $.
	p_ifnot $p |- if ( -. ph , A , B ) = if ( ph , B , A ) $= f0_ifnot p_notnot1 f0_ifnot a_wn f1_ifnot f2_ifnot p_iffalse f0_ifnot f0_ifnot a_wn a_wn f0_ifnot a_wn f1_ifnot f2_ifnot a_cif f2_ifnot a_wceq p_syl f0_ifnot f2_ifnot f1_ifnot p_iftrue f0_ifnot f0_ifnot a_wn f1_ifnot f2_ifnot a_cif f2_ifnot f0_ifnot f2_ifnot f1_ifnot a_cif p_eqtr4d f0_ifnot a_wn f1_ifnot f2_ifnot p_iftrue f0_ifnot f2_ifnot f1_ifnot p_iffalse f0_ifnot a_wn f0_ifnot a_wn f1_ifnot f2_ifnot a_cif f1_ifnot f0_ifnot f2_ifnot f1_ifnot a_cif p_eqtr4d f0_ifnot f0_ifnot a_wn f1_ifnot f2_ifnot a_cif f0_ifnot f2_ifnot f1_ifnot a_cif a_wceq p_pm2.61i $.
$}

$(Rewrite a conjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph ps A B  $.
	f0_ifan $f wff ph $.
	f1_ifan $f wff ps $.
	f2_ifan $f class A $.
	f3_ifan $f class B $.
	p_ifan $p |- if ( ( ph /\ ps ) , A , B ) = if ( ph , if ( ps , A , B ) , B ) $= f0_ifan f1_ifan f2_ifan f3_ifan a_cif f3_ifan p_iftrue f0_ifan f1_ifan p_ibar f0_ifan f1_ifan f0_ifan f1_ifan a_wa f2_ifan f3_ifan p_ifbid f0_ifan f0_ifan f1_ifan f2_ifan f3_ifan a_cif f3_ifan a_cif f1_ifan f2_ifan f3_ifan a_cif f0_ifan f1_ifan a_wa f2_ifan f3_ifan a_cif p_eqtr2d f0_ifan f1_ifan p_simpl f0_ifan f1_ifan a_wa f0_ifan p_con3i f0_ifan f1_ifan a_wa f2_ifan f3_ifan p_iffalse f0_ifan a_wn f0_ifan f1_ifan a_wa a_wn f0_ifan f1_ifan a_wa f2_ifan f3_ifan a_cif f3_ifan a_wceq p_syl f0_ifan f1_ifan f2_ifan f3_ifan a_cif f3_ifan p_iffalse f0_ifan a_wn f0_ifan f1_ifan a_wa f2_ifan f3_ifan a_cif f3_ifan f0_ifan f1_ifan f2_ifan f3_ifan a_cif f3_ifan a_cif p_eqtr4d f0_ifan f0_ifan f1_ifan a_wa f2_ifan f3_ifan a_cif f0_ifan f1_ifan f2_ifan f3_ifan a_cif f3_ifan a_cif a_wceq p_pm2.61i $.
$}

$(Rewrite a disjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)

${
	$v ph ps A B  $.
	f0_ifor $f wff ph $.
	f1_ifor $f wff ps $.
	f2_ifor $f class A $.
	f3_ifor $f class B $.
	p_ifor $p |- if ( ( ph \/ ps ) , A , B ) = if ( ph , A , if ( ps , A , B ) ) $= f0_ifor f1_ifor a_wo f2_ifor f3_ifor p_iftrue f0_ifor f1_ifor f0_ifor f1_ifor a_wo f2_ifor f3_ifor a_cif f2_ifor a_wceq p_orcs f0_ifor f2_ifor f1_ifor f2_ifor f3_ifor a_cif p_iftrue f0_ifor f0_ifor f1_ifor a_wo f2_ifor f3_ifor a_cif f2_ifor f0_ifor f2_ifor f1_ifor f2_ifor f3_ifor a_cif a_cif p_eqtr4d f0_ifor f2_ifor f1_ifor f2_ifor f3_ifor a_cif p_iffalse f0_ifor f1_ifor p_biorf f0_ifor a_wn f1_ifor f0_ifor f1_ifor a_wo f2_ifor f3_ifor p_ifbid f0_ifor a_wn f0_ifor f2_ifor f1_ifor f2_ifor f3_ifor a_cif a_cif f1_ifor f2_ifor f3_ifor a_cif f0_ifor f1_ifor a_wo f2_ifor f3_ifor a_cif p_eqtr2d f0_ifor f0_ifor f1_ifor a_wo f2_ifor f3_ifor a_cif f0_ifor f2_ifor f1_ifor f2_ifor f3_ifor a_cif a_cif a_wceq p_pm2.61i $.
$}

$(Weak deduction theorem that eliminates a hypothesis ` ph ` , making it
       become an antecedent.  We assume that a proof exists for ` ph ` when the
       class variable ` A ` is replaced with a specific class ` B ` .  The
       hypothesis ` ch ` should be assigned to the inference, and the
       inference's hypothesis eliminated with ~ elimhyp .  If the inference has
       other hypotheses with class variable ` A ` , these can be kept by
       assigning ~ keephyp to them.  For more information, see the Deduction
       Theorem ~ http://us.metamath.org/mpeuni/mmdeduction.html .  (Contributed
       by NM, 15-May-1999.) $)

${
	$v ph ps ch A B  $.
	$d A  $.
	$d B  $.
	$d ph  $.
	f0_dedth $f wff ph $.
	f1_dedth $f wff ps $.
	f2_dedth $f wff ch $.
	f3_dedth $f class A $.
	f4_dedth $f class B $.
	e0_dedth $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
	e1_dedth $e |- ch $.
	p_dedth $p |- ( ph -> ps ) $= e1_dedth f0_dedth f3_dedth f4_dedth p_iftrue f0_dedth f0_dedth f3_dedth f4_dedth a_cif f3_dedth p_eqcomd e0_dedth f0_dedth f3_dedth f0_dedth f3_dedth f4_dedth a_cif a_wceq f1_dedth f2_dedth a_wb p_syl f0_dedth f1_dedth f2_dedth p_mpbiri $.
$}

$(Weak deduction theorem eliminating two hypotheses.  This theorem is
       simpler to use than ~ dedth2v but requires that each hypothesis has
       exactly one class variable.  See also comments in ~ dedth .
       (Contributed by NM, 15-May-1999.) $)

${
	$v ph ps ch th ta A B C D  $.
	f0_dedth2h $f wff ph $.
	f1_dedth2h $f wff ps $.
	f2_dedth2h $f wff ch $.
	f3_dedth2h $f wff th $.
	f4_dedth2h $f wff ta $.
	f5_dedth2h $f class A $.
	f6_dedth2h $f class B $.
	f7_dedth2h $f class C $.
	f8_dedth2h $f class D $.
	e0_dedth2h $e |- ( A = if ( ph , A , C ) -> ( ch <-> th ) ) $.
	e1_dedth2h $e |- ( B = if ( ps , B , D ) -> ( th <-> ta ) ) $.
	e2_dedth2h $e |- ta $.
	p_dedth2h $p |- ( ( ph /\ ps ) -> ch ) $= e0_dedth2h f5_dedth2h f0_dedth2h f5_dedth2h f7_dedth2h a_cif a_wceq f2_dedth2h f3_dedth2h f1_dedth2h p_imbi2d e1_dedth2h e2_dedth2h f1_dedth2h f3_dedth2h f4_dedth2h f6_dedth2h f8_dedth2h p_dedth f0_dedth2h f1_dedth2h f2_dedth2h a_wi f1_dedth2h f3_dedth2h a_wi f5_dedth2h f7_dedth2h p_dedth f0_dedth2h f1_dedth2h f2_dedth2h p_imp $.
$}

$(Weak deduction theorem eliminating three hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 15-May-1999.) $)

${
	$v ph ps ch th ta et ze A B C D R S  $.
	f0_dedth3h $f wff ph $.
	f1_dedth3h $f wff ps $.
	f2_dedth3h $f wff ch $.
	f3_dedth3h $f wff th $.
	f4_dedth3h $f wff ta $.
	f5_dedth3h $f wff et $.
	f6_dedth3h $f wff ze $.
	f7_dedth3h $f class A $.
	f8_dedth3h $f class B $.
	f9_dedth3h $f class C $.
	f10_dedth3h $f class D $.
	f11_dedth3h $f class R $.
	f12_dedth3h $f class S $.
	e0_dedth3h $e |- ( A = if ( ph , A , D ) -> ( th <-> ta ) ) $.
	e1_dedth3h $e |- ( B = if ( ps , B , R ) -> ( ta <-> et ) ) $.
	e2_dedth3h $e |- ( C = if ( ch , C , S ) -> ( et <-> ze ) ) $.
	e3_dedth3h $e |- ze $.
	p_dedth3h $p |- ( ( ph /\ ps /\ ch ) -> th ) $= e0_dedth3h f7_dedth3h f0_dedth3h f7_dedth3h f10_dedth3h a_cif a_wceq f3_dedth3h f4_dedth3h f1_dedth3h f2_dedth3h a_wa p_imbi2d e1_dedth3h e2_dedth3h e3_dedth3h f1_dedth3h f2_dedth3h f4_dedth3h f5_dedth3h f6_dedth3h f8_dedth3h f9_dedth3h f11_dedth3h f12_dedth3h p_dedth2h f0_dedth3h f1_dedth3h f2_dedth3h a_wa f3_dedth3h a_wi f1_dedth3h f2_dedth3h a_wa f4_dedth3h a_wi f7_dedth3h f10_dedth3h p_dedth f0_dedth3h f1_dedth3h f2_dedth3h f3_dedth3h p_3impib $.
$}

$(Weak deduction theorem eliminating four hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 16-May-1999.) $)

${
	$v ph ps ch th ta et ze si rh A B C D R S F G  $.
	f0_dedth4h $f wff ph $.
	f1_dedth4h $f wff ps $.
	f2_dedth4h $f wff ch $.
	f3_dedth4h $f wff th $.
	f4_dedth4h $f wff ta $.
	f5_dedth4h $f wff et $.
	f6_dedth4h $f wff ze $.
	f7_dedth4h $f wff si $.
	f8_dedth4h $f wff rh $.
	f9_dedth4h $f class A $.
	f10_dedth4h $f class B $.
	f11_dedth4h $f class C $.
	f12_dedth4h $f class D $.
	f13_dedth4h $f class R $.
	f14_dedth4h $f class S $.
	f15_dedth4h $f class F $.
	f16_dedth4h $f class G $.
	e0_dedth4h $e |- ( A = if ( ph , A , R ) -> ( ta <-> et ) ) $.
	e1_dedth4h $e |- ( B = if ( ps , B , S ) -> ( et <-> ze ) ) $.
	e2_dedth4h $e |- ( C = if ( ch , C , F ) -> ( ze <-> si ) ) $.
	e3_dedth4h $e |- ( D = if ( th , D , G ) -> ( si <-> rh ) ) $.
	e4_dedth4h $e |- rh $.
	p_dedth4h $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $= e0_dedth4h f9_dedth4h f0_dedth4h f9_dedth4h f13_dedth4h a_cif a_wceq f4_dedth4h f5_dedth4h f2_dedth4h f3_dedth4h a_wa p_imbi2d e1_dedth4h f10_dedth4h f1_dedth4h f10_dedth4h f14_dedth4h a_cif a_wceq f5_dedth4h f6_dedth4h f2_dedth4h f3_dedth4h a_wa p_imbi2d e2_dedth4h e3_dedth4h e4_dedth4h f2_dedth4h f3_dedth4h f6_dedth4h f7_dedth4h f8_dedth4h f11_dedth4h f12_dedth4h f15_dedth4h f16_dedth4h p_dedth2h f0_dedth4h f1_dedth4h f2_dedth4h f3_dedth4h a_wa f4_dedth4h a_wi f2_dedth4h f3_dedth4h a_wa f5_dedth4h a_wi f2_dedth4h f3_dedth4h a_wa f6_dedth4h a_wi f9_dedth4h f10_dedth4h f13_dedth4h f14_dedth4h p_dedth2h f0_dedth4h f1_dedth4h a_wa f2_dedth4h f3_dedth4h a_wa f4_dedth4h p_imp $.
$}

$(Weak deduction theorem for eliminating a hypothesis with 2 class
       variables.  Note: if the hypothesis can be separated into two
       hypotheses, each with one class variable, then ~ dedth2h is simpler to
       use.  See also comments in ~ dedth .  (Contributed by NM, 13-Aug-1999.)
       (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)

${
	$v ph ps ch th A B C D  $.
	f0_dedth2v $f wff ph $.
	f1_dedth2v $f wff ps $.
	f2_dedth2v $f wff ch $.
	f3_dedth2v $f wff th $.
	f4_dedth2v $f class A $.
	f5_dedth2v $f class B $.
	f6_dedth2v $f class C $.
	f7_dedth2v $f class D $.
	e0_dedth2v $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
	e1_dedth2v $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	e2_dedth2v $e |- th $.
	p_dedth2v $p |- ( ph -> ps ) $= e0_dedth2v e1_dedth2v e2_dedth2v f0_dedth2v f0_dedth2v f1_dedth2v f2_dedth2v f3_dedth2v f4_dedth2v f5_dedth2v f6_dedth2v f7_dedth2v p_dedth2h f0_dedth2v f1_dedth2v p_anidms $.
$}

$(Weak deduction theorem for eliminating a hypothesis with 3 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       13-Aug-1999.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)

${
	$v ph ps ch th ta A B C D R S  $.
	f0_dedth3v $f wff ph $.
	f1_dedth3v $f wff ps $.
	f2_dedth3v $f wff ch $.
	f3_dedth3v $f wff th $.
	f4_dedth3v $f wff ta $.
	f5_dedth3v $f class A $.
	f6_dedth3v $f class B $.
	f7_dedth3v $f class C $.
	f8_dedth3v $f class D $.
	f9_dedth3v $f class R $.
	f10_dedth3v $f class S $.
	e0_dedth3v $e |- ( A = if ( ph , A , D ) -> ( ps <-> ch ) ) $.
	e1_dedth3v $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	e2_dedth3v $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	e3_dedth3v $e |- ta $.
	p_dedth3v $p |- ( ph -> ps ) $= e0_dedth3v e1_dedth3v e2_dedth3v e3_dedth3v f0_dedth3v f0_dedth3v f0_dedth3v f1_dedth3v f2_dedth3v f3_dedth3v f4_dedth3v f5_dedth3v f6_dedth3v f7_dedth3v f8_dedth3v f9_dedth3v f10_dedth3v p_dedth3h f0_dedth3v f0_dedth3v f1_dedth3v p_3anidm12 f0_dedth3v f1_dedth3v p_anidms $.
$}

$(Weak deduction theorem for eliminating a hypothesis with 4 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       21-Apr-2007.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)

${
	$v ph ps ch th ta et A B C D R S T U  $.
	f0_dedth4v $f wff ph $.
	f1_dedth4v $f wff ps $.
	f2_dedth4v $f wff ch $.
	f3_dedth4v $f wff th $.
	f4_dedth4v $f wff ta $.
	f5_dedth4v $f wff et $.
	f6_dedth4v $f class A $.
	f7_dedth4v $f class B $.
	f8_dedth4v $f class C $.
	f9_dedth4v $f class D $.
	f10_dedth4v $f class R $.
	f11_dedth4v $f class S $.
	f12_dedth4v $f class T $.
	f13_dedth4v $f class U $.
	e0_dedth4v $e |- ( A = if ( ph , A , R ) -> ( ps <-> ch ) ) $.
	e1_dedth4v $e |- ( B = if ( ph , B , S ) -> ( ch <-> th ) ) $.
	e2_dedth4v $e |- ( C = if ( ph , C , T ) -> ( th <-> ta ) ) $.
	e3_dedth4v $e |- ( D = if ( ph , D , U ) -> ( ta <-> et ) ) $.
	e4_dedth4v $e |- et $.
	p_dedth4v $p |- ( ph -> ps ) $= e0_dedth4v e1_dedth4v e2_dedth4v e3_dedth4v e4_dedth4v f0_dedth4v f0_dedth4v f0_dedth4v f0_dedth4v f1_dedth4v f2_dedth4v f3_dedth4v f4_dedth4v f5_dedth4v f6_dedth4v f7_dedth4v f8_dedth4v f9_dedth4v f10_dedth4v f11_dedth4v f12_dedth4v f13_dedth4v p_dedth4h f0_dedth4v f0_dedth4v a_wa f1_dedth4v p_anidms f0_dedth4v f1_dedth4v p_anidms $.
$}

$(Eliminate a hypothesis containing class variable ` A ` when it is known
       for a specific class ` B ` .  For more information, see comments in
       ~ dedth .  (Contributed by NM, 15-May-1999.) $)

${
	$v ph ps ch A B  $.
	f0_elimhyp $f wff ph $.
	f1_elimhyp $f wff ps $.
	f2_elimhyp $f wff ch $.
	f3_elimhyp $f class A $.
	f4_elimhyp $f class B $.
	e0_elimhyp $e |- ( A = if ( ph , A , B ) -> ( ph <-> ps ) ) $.
	e1_elimhyp $e |- ( B = if ( ph , A , B ) -> ( ch <-> ps ) ) $.
	e2_elimhyp $e |- ch $.
	p_elimhyp $p |- ps $= f0_elimhyp f3_elimhyp f4_elimhyp p_iftrue f0_elimhyp f0_elimhyp f3_elimhyp f4_elimhyp a_cif f3_elimhyp p_eqcomd e0_elimhyp f0_elimhyp f3_elimhyp f0_elimhyp f3_elimhyp f4_elimhyp a_cif a_wceq f0_elimhyp f1_elimhyp a_wb p_syl f0_elimhyp f1_elimhyp p_ibi e2_elimhyp f0_elimhyp f3_elimhyp f4_elimhyp p_iffalse f0_elimhyp a_wn f0_elimhyp f3_elimhyp f4_elimhyp a_cif f4_elimhyp p_eqcomd e1_elimhyp f0_elimhyp a_wn f4_elimhyp f0_elimhyp f3_elimhyp f4_elimhyp a_cif a_wceq f2_elimhyp f1_elimhyp a_wb p_syl f0_elimhyp a_wn f2_elimhyp f1_elimhyp p_mpbii f0_elimhyp f1_elimhyp p_pm2.61i $.
$}

$(Eliminate a hypothesis containing 2 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)

${
	$v ph ch th ta et A B C D  $.
	f0_elimhyp2v $f wff ph $.
	f1_elimhyp2v $f wff ch $.
	f2_elimhyp2v $f wff th $.
	f3_elimhyp2v $f wff ta $.
	f4_elimhyp2v $f wff et $.
	f5_elimhyp2v $f class A $.
	f6_elimhyp2v $f class B $.
	f7_elimhyp2v $f class C $.
	f8_elimhyp2v $f class D $.
	e0_elimhyp2v $e |- ( A = if ( ph , A , C ) -> ( ph <-> ch ) ) $.
	e1_elimhyp2v $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	e2_elimhyp2v $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
	e3_elimhyp2v $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
	e4_elimhyp2v $e |- ta $.
	p_elimhyp2v $p |- th $= f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v p_iftrue f0_elimhyp2v f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v a_cif f5_elimhyp2v p_eqcomd e0_elimhyp2v f0_elimhyp2v f5_elimhyp2v f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v a_cif a_wceq f0_elimhyp2v f1_elimhyp2v a_wb p_syl f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v p_iftrue f0_elimhyp2v f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v a_cif f6_elimhyp2v p_eqcomd e1_elimhyp2v f0_elimhyp2v f6_elimhyp2v f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v a_cif a_wceq f1_elimhyp2v f2_elimhyp2v a_wb p_syl f0_elimhyp2v f0_elimhyp2v f1_elimhyp2v f2_elimhyp2v p_bitrd f0_elimhyp2v f2_elimhyp2v p_ibi e4_elimhyp2v f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v p_iffalse f0_elimhyp2v a_wn f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v a_cif f7_elimhyp2v p_eqcomd e2_elimhyp2v f0_elimhyp2v a_wn f7_elimhyp2v f0_elimhyp2v f5_elimhyp2v f7_elimhyp2v a_cif a_wceq f3_elimhyp2v f4_elimhyp2v a_wb p_syl f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v p_iffalse f0_elimhyp2v a_wn f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v a_cif f8_elimhyp2v p_eqcomd e3_elimhyp2v f0_elimhyp2v a_wn f8_elimhyp2v f0_elimhyp2v f6_elimhyp2v f8_elimhyp2v a_cif a_wceq f4_elimhyp2v f2_elimhyp2v a_wb p_syl f0_elimhyp2v a_wn f3_elimhyp2v f4_elimhyp2v f2_elimhyp2v p_bitrd f0_elimhyp2v a_wn f3_elimhyp2v f2_elimhyp2v p_mpbii f0_elimhyp2v f2_elimhyp2v p_pm2.61i $.
$}

$(Eliminate a hypothesis containing 3 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)

${
	$v ph ch th ta et ze si A B C D R S  $.
	f0_elimhyp3v $f wff ph $.
	f1_elimhyp3v $f wff ch $.
	f2_elimhyp3v $f wff th $.
	f3_elimhyp3v $f wff ta $.
	f4_elimhyp3v $f wff et $.
	f5_elimhyp3v $f wff ze $.
	f6_elimhyp3v $f wff si $.
	f7_elimhyp3v $f class A $.
	f8_elimhyp3v $f class B $.
	f9_elimhyp3v $f class C $.
	f10_elimhyp3v $f class D $.
	f11_elimhyp3v $f class R $.
	f12_elimhyp3v $f class S $.
	e0_elimhyp3v $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
	e1_elimhyp3v $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	e2_elimhyp3v $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	e3_elimhyp3v $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	e4_elimhyp3v $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	e5_elimhyp3v $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
	e6_elimhyp3v $e |- et $.
	p_elimhyp3v $p |- ta $= f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v p_iftrue f0_elimhyp3v f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v a_cif f7_elimhyp3v p_eqcomd e0_elimhyp3v f0_elimhyp3v f7_elimhyp3v f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v a_cif a_wceq f0_elimhyp3v f1_elimhyp3v a_wb p_syl f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v p_iftrue f0_elimhyp3v f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v a_cif f8_elimhyp3v p_eqcomd e1_elimhyp3v f0_elimhyp3v f8_elimhyp3v f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v a_cif a_wceq f1_elimhyp3v f2_elimhyp3v a_wb p_syl f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v p_iftrue f0_elimhyp3v f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v a_cif f9_elimhyp3v p_eqcomd e2_elimhyp3v f0_elimhyp3v f9_elimhyp3v f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v a_cif a_wceq f2_elimhyp3v f3_elimhyp3v a_wb p_syl f0_elimhyp3v f0_elimhyp3v f1_elimhyp3v f2_elimhyp3v f3_elimhyp3v p_3bitrd f0_elimhyp3v f3_elimhyp3v p_ibi e6_elimhyp3v f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v p_iffalse f0_elimhyp3v a_wn f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v a_cif f10_elimhyp3v p_eqcomd e3_elimhyp3v f0_elimhyp3v a_wn f10_elimhyp3v f0_elimhyp3v f7_elimhyp3v f10_elimhyp3v a_cif a_wceq f4_elimhyp3v f5_elimhyp3v a_wb p_syl f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v p_iffalse f0_elimhyp3v a_wn f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v a_cif f11_elimhyp3v p_eqcomd e4_elimhyp3v f0_elimhyp3v a_wn f11_elimhyp3v f0_elimhyp3v f8_elimhyp3v f11_elimhyp3v a_cif a_wceq f5_elimhyp3v f6_elimhyp3v a_wb p_syl f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v p_iffalse f0_elimhyp3v a_wn f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v a_cif f12_elimhyp3v p_eqcomd e5_elimhyp3v f0_elimhyp3v a_wn f12_elimhyp3v f0_elimhyp3v f9_elimhyp3v f12_elimhyp3v a_cif a_wceq f6_elimhyp3v f3_elimhyp3v a_wb p_syl f0_elimhyp3v a_wn f4_elimhyp3v f5_elimhyp3v f6_elimhyp3v f3_elimhyp3v p_3bitrd f0_elimhyp3v a_wn f4_elimhyp3v f3_elimhyp3v p_mpbii f0_elimhyp3v f3_elimhyp3v p_pm2.61i $.
$}

$(Eliminate a hypothesis containing 4 class variables (for use with the
       weak deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)

${
	$v ph ps ch th ta et ze si rh A B C D R S F G  $.
	f0_elimhyp4v $f wff ph $.
	f1_elimhyp4v $f wff ps $.
	f2_elimhyp4v $f wff ch $.
	f3_elimhyp4v $f wff th $.
	f4_elimhyp4v $f wff ta $.
	f5_elimhyp4v $f wff et $.
	f6_elimhyp4v $f wff ze $.
	f7_elimhyp4v $f wff si $.
	f8_elimhyp4v $f wff rh $.
	f9_elimhyp4v $f class A $.
	f10_elimhyp4v $f class B $.
	f11_elimhyp4v $f class C $.
	f12_elimhyp4v $f class D $.
	f13_elimhyp4v $f class R $.
	f14_elimhyp4v $f class S $.
	f15_elimhyp4v $f class F $.
	f16_elimhyp4v $f class G $.
	e0_elimhyp4v $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
	e1_elimhyp4v $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	e2_elimhyp4v $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	e3_elimhyp4v $e |- ( F = if ( ph , F , G ) -> ( ta <-> ps ) ) $.
	e4_elimhyp4v $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	e5_elimhyp4v $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	e6_elimhyp4v $e |- ( S = if ( ph , C , S ) -> ( si <-> rh ) ) $.
	e7_elimhyp4v $e |- ( G = if ( ph , F , G ) -> ( rh <-> ps ) ) $.
	e8_elimhyp4v $e |- et $.
	p_elimhyp4v $p |- ps $= f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v p_iftrue f0_elimhyp4v f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v a_cif f9_elimhyp4v p_eqcomd e0_elimhyp4v f0_elimhyp4v f9_elimhyp4v f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v a_cif a_wceq f0_elimhyp4v f2_elimhyp4v a_wb p_syl f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v p_iftrue f0_elimhyp4v f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v a_cif f10_elimhyp4v p_eqcomd e1_elimhyp4v f0_elimhyp4v f10_elimhyp4v f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v a_cif a_wceq f2_elimhyp4v f3_elimhyp4v a_wb p_syl f0_elimhyp4v f0_elimhyp4v f2_elimhyp4v f3_elimhyp4v p_bitrd f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v p_iftrue f0_elimhyp4v f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v a_cif f11_elimhyp4v p_eqcomd e2_elimhyp4v f0_elimhyp4v f11_elimhyp4v f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v a_cif a_wceq f3_elimhyp4v f4_elimhyp4v a_wb p_syl f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v p_iftrue f0_elimhyp4v f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v a_cif f15_elimhyp4v p_eqcomd e3_elimhyp4v f0_elimhyp4v f15_elimhyp4v f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v a_cif a_wceq f4_elimhyp4v f1_elimhyp4v a_wb p_syl f0_elimhyp4v f0_elimhyp4v f3_elimhyp4v f4_elimhyp4v f1_elimhyp4v p_3bitrd f0_elimhyp4v f1_elimhyp4v p_ibi e8_elimhyp4v f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v p_iffalse f0_elimhyp4v a_wn f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v a_cif f12_elimhyp4v p_eqcomd e4_elimhyp4v f0_elimhyp4v a_wn f12_elimhyp4v f0_elimhyp4v f9_elimhyp4v f12_elimhyp4v a_cif a_wceq f5_elimhyp4v f6_elimhyp4v a_wb p_syl f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v p_iffalse f0_elimhyp4v a_wn f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v a_cif f13_elimhyp4v p_eqcomd e5_elimhyp4v f0_elimhyp4v a_wn f13_elimhyp4v f0_elimhyp4v f10_elimhyp4v f13_elimhyp4v a_cif a_wceq f6_elimhyp4v f7_elimhyp4v a_wb p_syl f0_elimhyp4v a_wn f5_elimhyp4v f6_elimhyp4v f7_elimhyp4v p_bitrd f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v p_iffalse f0_elimhyp4v a_wn f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v a_cif f14_elimhyp4v p_eqcomd e6_elimhyp4v f0_elimhyp4v a_wn f14_elimhyp4v f0_elimhyp4v f11_elimhyp4v f14_elimhyp4v a_cif a_wceq f7_elimhyp4v f8_elimhyp4v a_wb p_syl f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v p_iffalse f0_elimhyp4v a_wn f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v a_cif f16_elimhyp4v p_eqcomd e7_elimhyp4v f0_elimhyp4v a_wn f16_elimhyp4v f0_elimhyp4v f15_elimhyp4v f16_elimhyp4v a_cif a_wceq f8_elimhyp4v f1_elimhyp4v a_wb p_syl f0_elimhyp4v a_wn f5_elimhyp4v f7_elimhyp4v f8_elimhyp4v f1_elimhyp4v p_3bitrd f0_elimhyp4v a_wn f5_elimhyp4v f1_elimhyp4v p_mpbii f0_elimhyp4v f1_elimhyp4v p_pm2.61i $.
$}

$(Eliminate a membership hypothesis for weak deduction theorem, when
       special case ` B e. C ` is provable.  (Contributed by NM,
       15-May-1999.) $)

${
	$v A B C  $.
	f0_elimel $f class A $.
	f1_elimel $f class B $.
	f2_elimel $f class C $.
	e0_elimel $e |- B e. C $.
	p_elimel $p |- if ( A e. C , A , B ) e. C $= f0_elimel f0_elimel f2_elimel a_wcel f0_elimel f1_elimel a_cif f2_elimel p_eleq1 f1_elimel f0_elimel f2_elimel a_wcel f0_elimel f1_elimel a_cif f2_elimel p_eleq1 e0_elimel f0_elimel f2_elimel a_wcel f0_elimel f2_elimel a_wcel f0_elimel f1_elimel a_cif f2_elimel a_wcel f1_elimel f2_elimel a_wcel f0_elimel f1_elimel p_elimhyp $.
$}

$(Version of ~ elimhyp where the hypothesis is deduced from the final
       antecedent.  See ~ ghomgrplem for an example of its use.  (Contributed
       by Paul Chapman, 25-Mar-2008.) $)

${
	$v ph ps ch th A B  $.
	f0_elimdhyp $f wff ph $.
	f1_elimdhyp $f wff ps $.
	f2_elimdhyp $f wff ch $.
	f3_elimdhyp $f wff th $.
	f4_elimdhyp $f class A $.
	f5_elimdhyp $f class B $.
	e0_elimdhyp $e |- ( ph -> ps ) $.
	e1_elimdhyp $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
	e2_elimdhyp $e |- ( B = if ( ph , A , B ) -> ( th <-> ch ) ) $.
	e3_elimdhyp $e |- th $.
	p_elimdhyp $p |- ch $= e0_elimdhyp f0_elimdhyp f4_elimdhyp f5_elimdhyp p_iftrue f0_elimdhyp f0_elimdhyp f4_elimdhyp f5_elimdhyp a_cif f4_elimdhyp p_eqcomd e1_elimdhyp f0_elimdhyp f4_elimdhyp f0_elimdhyp f4_elimdhyp f5_elimdhyp a_cif a_wceq f1_elimdhyp f2_elimdhyp a_wb p_syl f0_elimdhyp f1_elimdhyp f2_elimdhyp p_mpbid e3_elimdhyp f0_elimdhyp f4_elimdhyp f5_elimdhyp p_iffalse f0_elimdhyp a_wn f0_elimdhyp f4_elimdhyp f5_elimdhyp a_cif f5_elimdhyp p_eqcomd e2_elimdhyp f0_elimdhyp a_wn f5_elimdhyp f0_elimdhyp f4_elimdhyp f5_elimdhyp a_cif a_wceq f3_elimdhyp f2_elimdhyp a_wb p_syl f0_elimdhyp a_wn f3_elimdhyp f2_elimdhyp p_mpbii f0_elimdhyp f2_elimdhyp p_pm2.61i $.
$}

$(Transform a hypothesis ` ps ` that we want to keep (but contains the
       same class variable ` A ` used in the eliminated hypothesis) for use
       with the weak deduction theorem.  (Contributed by NM, 15-May-1999.) $)

${
	$v ph ps ch th A B  $.
	f0_keephyp $f wff ph $.
	f1_keephyp $f wff ps $.
	f2_keephyp $f wff ch $.
	f3_keephyp $f wff th $.
	f4_keephyp $f class A $.
	f5_keephyp $f class B $.
	e0_keephyp $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
	e1_keephyp $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
	e2_keephyp $e |- ps $.
	e3_keephyp $e |- ch $.
	p_keephyp $p |- th $= e2_keephyp e3_keephyp e0_keephyp e1_keephyp f0_keephyp f1_keephyp f2_keephyp f3_keephyp f4_keephyp f5_keephyp p_ifboth f1_keephyp f2_keephyp f3_keephyp p_mp2an $.
$}

$(Keep a hypothesis containing 2 class variables (for use with the weak
       deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)

${
	$v ph ps ch th ta et A B C D  $.
	f0_keephyp2v $f wff ph $.
	f1_keephyp2v $f wff ps $.
	f2_keephyp2v $f wff ch $.
	f3_keephyp2v $f wff th $.
	f4_keephyp2v $f wff ta $.
	f5_keephyp2v $f wff et $.
	f6_keephyp2v $f class A $.
	f7_keephyp2v $f class B $.
	f8_keephyp2v $f class C $.
	f9_keephyp2v $f class D $.
	e0_keephyp2v $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
	e1_keephyp2v $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
	e2_keephyp2v $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
	e3_keephyp2v $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
	e4_keephyp2v $e |- ps $.
	e5_keephyp2v $e |- ta $.
	p_keephyp2v $p |- th $= e4_keephyp2v f0_keephyp2v f6_keephyp2v f8_keephyp2v p_iftrue f0_keephyp2v f0_keephyp2v f6_keephyp2v f8_keephyp2v a_cif f6_keephyp2v p_eqcomd e0_keephyp2v f0_keephyp2v f6_keephyp2v f0_keephyp2v f6_keephyp2v f8_keephyp2v a_cif a_wceq f1_keephyp2v f2_keephyp2v a_wb p_syl f0_keephyp2v f7_keephyp2v f9_keephyp2v p_iftrue f0_keephyp2v f0_keephyp2v f7_keephyp2v f9_keephyp2v a_cif f7_keephyp2v p_eqcomd e1_keephyp2v f0_keephyp2v f7_keephyp2v f0_keephyp2v f7_keephyp2v f9_keephyp2v a_cif a_wceq f2_keephyp2v f3_keephyp2v a_wb p_syl f0_keephyp2v f1_keephyp2v f2_keephyp2v f3_keephyp2v p_bitrd f0_keephyp2v f1_keephyp2v f3_keephyp2v p_mpbii e5_keephyp2v f0_keephyp2v f6_keephyp2v f8_keephyp2v p_iffalse f0_keephyp2v a_wn f0_keephyp2v f6_keephyp2v f8_keephyp2v a_cif f8_keephyp2v p_eqcomd e2_keephyp2v f0_keephyp2v a_wn f8_keephyp2v f0_keephyp2v f6_keephyp2v f8_keephyp2v a_cif a_wceq f4_keephyp2v f5_keephyp2v a_wb p_syl f0_keephyp2v f7_keephyp2v f9_keephyp2v p_iffalse f0_keephyp2v a_wn f0_keephyp2v f7_keephyp2v f9_keephyp2v a_cif f9_keephyp2v p_eqcomd e3_keephyp2v f0_keephyp2v a_wn f9_keephyp2v f0_keephyp2v f7_keephyp2v f9_keephyp2v a_cif a_wceq f5_keephyp2v f3_keephyp2v a_wb p_syl f0_keephyp2v a_wn f4_keephyp2v f5_keephyp2v f3_keephyp2v p_bitrd f0_keephyp2v a_wn f4_keephyp2v f3_keephyp2v p_mpbii f0_keephyp2v f3_keephyp2v p_pm2.61i $.
$}

$(Keep a hypothesis containing 3 class variables.  (Contributed by NM,
       27-Sep-1999.) $)

${
	$v ph ch th ta et ze si rh A B C D R S  $.
	f0_keephyp3v $f wff ph $.
	f1_keephyp3v $f wff ch $.
	f2_keephyp3v $f wff th $.
	f3_keephyp3v $f wff ta $.
	f4_keephyp3v $f wff et $.
	f5_keephyp3v $f wff ze $.
	f6_keephyp3v $f wff si $.
	f7_keephyp3v $f wff rh $.
	f8_keephyp3v $f class A $.
	f9_keephyp3v $f class B $.
	f10_keephyp3v $f class C $.
	f11_keephyp3v $f class D $.
	f12_keephyp3v $f class R $.
	f13_keephyp3v $f class S $.
	e0_keephyp3v $e |- ( A = if ( ph , A , D ) -> ( rh <-> ch ) ) $.
	e1_keephyp3v $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
	e2_keephyp3v $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
	e3_keephyp3v $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
	e4_keephyp3v $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
	e5_keephyp3v $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
	e6_keephyp3v $e |- rh $.
	e7_keephyp3v $e |- et $.
	p_keephyp3v $p |- ta $= e6_keephyp3v f0_keephyp3v f8_keephyp3v f11_keephyp3v p_iftrue f0_keephyp3v f0_keephyp3v f8_keephyp3v f11_keephyp3v a_cif f8_keephyp3v p_eqcomd e0_keephyp3v f0_keephyp3v f8_keephyp3v f0_keephyp3v f8_keephyp3v f11_keephyp3v a_cif a_wceq f7_keephyp3v f1_keephyp3v a_wb p_syl f0_keephyp3v f9_keephyp3v f12_keephyp3v p_iftrue f0_keephyp3v f0_keephyp3v f9_keephyp3v f12_keephyp3v a_cif f9_keephyp3v p_eqcomd e1_keephyp3v f0_keephyp3v f9_keephyp3v f0_keephyp3v f9_keephyp3v f12_keephyp3v a_cif a_wceq f1_keephyp3v f2_keephyp3v a_wb p_syl f0_keephyp3v f10_keephyp3v f13_keephyp3v p_iftrue f0_keephyp3v f0_keephyp3v f10_keephyp3v f13_keephyp3v a_cif f10_keephyp3v p_eqcomd e2_keephyp3v f0_keephyp3v f10_keephyp3v f0_keephyp3v f10_keephyp3v f13_keephyp3v a_cif a_wceq f2_keephyp3v f3_keephyp3v a_wb p_syl f0_keephyp3v f7_keephyp3v f1_keephyp3v f2_keephyp3v f3_keephyp3v p_3bitrd f0_keephyp3v f7_keephyp3v f3_keephyp3v p_mpbii e7_keephyp3v f0_keephyp3v f8_keephyp3v f11_keephyp3v p_iffalse f0_keephyp3v a_wn f0_keephyp3v f8_keephyp3v f11_keephyp3v a_cif f11_keephyp3v p_eqcomd e3_keephyp3v f0_keephyp3v a_wn f11_keephyp3v f0_keephyp3v f8_keephyp3v f11_keephyp3v a_cif a_wceq f4_keephyp3v f5_keephyp3v a_wb p_syl f0_keephyp3v f9_keephyp3v f12_keephyp3v p_iffalse f0_keephyp3v a_wn f0_keephyp3v f9_keephyp3v f12_keephyp3v a_cif f12_keephyp3v p_eqcomd e4_keephyp3v f0_keephyp3v a_wn f12_keephyp3v f0_keephyp3v f9_keephyp3v f12_keephyp3v a_cif a_wceq f5_keephyp3v f6_keephyp3v a_wb p_syl f0_keephyp3v f10_keephyp3v f13_keephyp3v p_iffalse f0_keephyp3v a_wn f0_keephyp3v f10_keephyp3v f13_keephyp3v a_cif f13_keephyp3v p_eqcomd e5_keephyp3v f0_keephyp3v a_wn f13_keephyp3v f0_keephyp3v f10_keephyp3v f13_keephyp3v a_cif a_wceq f6_keephyp3v f3_keephyp3v a_wb p_syl f0_keephyp3v a_wn f4_keephyp3v f5_keephyp3v f6_keephyp3v f3_keephyp3v p_3bitrd f0_keephyp3v a_wn f4_keephyp3v f3_keephyp3v p_mpbii f0_keephyp3v f3_keephyp3v p_pm2.61i $.
$}

$(Keep a membership hypothesis for weak deduction theorem, when special
       case ` B e. C ` is provable.  (Contributed by NM, 14-Aug-1999.) $)

${
	$v ph A B C  $.
	f0_keepel $f wff ph $.
	f1_keepel $f class A $.
	f2_keepel $f class B $.
	f3_keepel $f class C $.
	e0_keepel $e |- A e. C $.
	e1_keepel $e |- B e. C $.
	p_keepel $p |- if ( ph , A , B ) e. C $= f1_keepel f0_keepel f1_keepel f2_keepel a_cif f3_keepel p_eleq1 f2_keepel f0_keepel f1_keepel f2_keepel a_cif f3_keepel p_eleq1 e0_keepel e1_keepel f0_keepel f1_keepel f3_keepel a_wcel f2_keepel f3_keepel a_wcel f0_keepel f1_keepel f2_keepel a_cif f3_keepel a_wcel f1_keepel f2_keepel p_keephyp $.
$}

$(Conditional operator existence.  (Contributed by NM, 2-Sep-2004.) $)

${
	$v ph A B  $.
	f0_ifex $f wff ph $.
	f1_ifex $f class A $.
	f2_ifex $f class B $.
	e0_ifex $e |- A e. _V $.
	e1_ifex $e |- B e. _V $.
	p_ifex $p |- if ( ph , A , B ) e. _V $= e0_ifex e1_ifex f0_ifex f1_ifex f2_ifex a_cvv p_keepel $.
$}

$(Conditional operator existence.  (Contributed by NM, 21-Mar-2011.) $)

${
	$v ph A B V W  $.
	$d A x y  $.
	$d B y  $.
	$d ph x y  $.
	f0_ifexg $f wff ph $.
	f1_ifexg $f class A $.
	f2_ifexg $f class B $.
	f3_ifexg $f class V $.
	f4_ifexg $f class W $.
	i0_ifexg $f set x $.
	i1_ifexg $f set y $.
	p_ifexg $p |- ( ( A e. V /\ B e. W ) -> if ( ph , A , B ) e. _V ) $= f0_ifexg i0_ifexg a_sup_set_class f1_ifexg i1_ifexg a_sup_set_class p_ifeq1 i0_ifexg a_sup_set_class f1_ifexg a_wceq f0_ifexg i0_ifexg a_sup_set_class i1_ifexg a_sup_set_class a_cif f0_ifexg f1_ifexg i1_ifexg a_sup_set_class a_cif a_cvv p_eleq1d f0_ifexg i1_ifexg a_sup_set_class f2_ifexg f1_ifexg p_ifeq2 i1_ifexg a_sup_set_class f2_ifexg a_wceq f0_ifexg f1_ifexg i1_ifexg a_sup_set_class a_cif f0_ifexg f1_ifexg f2_ifexg a_cif a_cvv p_eleq1d i0_ifexg p_vex i1_ifexg p_vex f0_ifexg i0_ifexg a_sup_set_class i1_ifexg a_sup_set_class p_ifex f0_ifexg i0_ifexg a_sup_set_class i1_ifexg a_sup_set_class a_cif a_cvv a_wcel f0_ifexg f1_ifexg i1_ifexg a_sup_set_class a_cif a_cvv a_wcel f0_ifexg f1_ifexg f2_ifexg a_cif a_cvv a_wcel i0_ifexg i1_ifexg f1_ifexg f2_ifexg f3_ifexg f4_ifexg p_vtocl2g $.
$}


