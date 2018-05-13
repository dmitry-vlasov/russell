$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Equality_predicate__define_substitution.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Axiom scheme ax-9 (Existence)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Existence.  One of the equality and substitution axioms of
     predicate calculus with equality.  This axiom tells us is that at least
     one thing exists.  In this form (not requiring that ` x ` and ` y ` be
     distinct) it was used in an axiom system of Tarski (see Axiom B7' in
     footnote 1 of [KalishMontague] p. 81.)  It is equivalent to axiom scheme
     C10' in [Megill] p. 448 (p. 16 of the preprint); the equivalence is
     established by ~ ax9o and ~ ax9from9o .  A more convenient form of this
     axiom is ~ a9e , which has additional remarks.

     Raph Levien proved the independence of this axiom from the other logical
     axioms on 12-Apr-2005.  See item 16 at
     ~ http://us.metamath.org/award2003.html .

     ~ ax-9 can be proved from the weaker version ~ ax9v requiring that the
     variables be distinct; see theorem ~ ax9 .

     ~ ax-9 can also be proved from the Axiom of Separation (in the form that
     we use that axiom, where free variables are not universally quantified).
     See theorem ~ ax9vsep .

     Except by ~ ax9v , this axiom should not be referenced directly.  Instead,
     use theorem ~ ax9 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)

${
	$v x y  $.
	f0_ax-9 $f set x $.
	f1_ax-9 $f set y $.
	a_ax-9 $a |- -. A. x -. x = y $.
$}

$(Axiom B7 of [Tarski] p. 75, which requires that ` x ` and ` y ` be
       distinct.  This trivial proof is intended merely to weaken axiom ~ ax-9
       by adding a distinct variable restriction.  From here on, ~ ax-9 should
       not be referenced directly by any other proof, so that theorem ~ ax9
       will show that we can recover ~ ax-9 from this weaker version if it were
       an axiom (as it is in the case of Tarski).

       Note:  Introducing ` x y ` as a distinct variable group "out of the
       blue" with no apparent justification has puzzled some people, but it is
       perfectly sound.  All we are doing is adding an additional redundant
       requirement, no different from adding a redundant logical hypothesis,
       that results in a weakening of the theorem.  This means that any
       _future_ theorem that references ~ ax9v must have a $d specified for the
       two variables that get substituted for ` x ` and ` y ` .  The $d does
       not propagate "backwards" i.e. it does not impose a requirement on
       ~ ax-9 .

       When possible, use of this theorem rather than ~ ax9 is preferred since
       its derivation from axioms is much shorter.  (Contributed by NM,
       7-Aug-2015.) $)

${
	$v x y  $.
	$d x y  $.
	f0_ax9v $f set x $.
	f1_ax9v $f set y $.
	p_ax9v $p |- -. A. x -. x = y $= f0_ax9v f1_ax9v a_ax-9 $.
$}

$(At least one individual exists.  Weaker version of ~ a9e .  When
       possible, use of this theorem rather than ~ a9e is preferred since its
       derivation from axioms is much shorter.  (Contributed by NM,
       3-Aug-2017.) $)

${
	$v x y  $.
	$d x y  $.
	f0_a9ev $f set x $.
	f1_a9ev $f set y $.
	p_a9ev $p |- E. x x = y $= f0_a9ev f1_a9ev p_ax9v f0_a9ev a_sup_set_class f1_a9ev a_sup_set_class a_wceq f0_a9ev a_df-ex f0_a9ev a_sup_set_class f1_a9ev a_sup_set_class a_wceq f0_a9ev a_wex f0_a9ev a_sup_set_class f1_a9ev a_sup_set_class a_wceq a_wn f0_a9ev a_wal a_wn p_mpbir $.
$}

$(Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 7-Aug-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_spimw $f wff ph $.
	f1_spimw $f wff ps $.
	f2_spimw $f set x $.
	f3_spimw $f set y $.
	e0_spimw $e |- ( -. ps -> A. x -. ps ) $.
	e1_spimw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimw $p |- ( A. x ph -> ps ) $= f2_spimw f3_spimw p_ax9v e0_spimw e1_spimw f0_spimw f1_spimw f2_spimw f3_spimw p_spimfw f2_spimw a_sup_set_class f3_spimw a_sup_set_class a_wceq a_wn f2_spimw a_wal a_wn f0_spimw f2_spimw a_wal f1_spimw a_wi a_ax-mp $.
$}

$(Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d x ps  $.
	f0_spimvw $f wff ph $.
	f1_spimvw $f wff ps $.
	f2_spimvw $f set x $.
	f3_spimvw $f set y $.
	e0_spimvw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_spimvw $p |- ( A. x ph -> ps ) $= f1_spimvw a_wn f2_spimvw a_ax-17 e0_spimvw f0_spimvw f1_spimvw f2_spimvw f3_spimvw p_spimw $.
$}

$(Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       13-Aug-2017.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_spnfw $f wff ph $.
	f1_spnfw $f set x $.
	i0_spnfw $f set y $.
	e0_spnfw $e |- ( -. ph -> A. x -. ph ) $.
	p_spnfw $p |- ( A. x ph -> ph ) $= e0_spnfw f1_spnfw a_sup_set_class i0_spnfw a_sup_set_class a_wceq f0_spnfw p_idd f0_spnfw f0_spnfw f1_spnfw i0_spnfw p_spimw $.
$}

$(Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_cbvaliw $f wff ph $.
	f1_cbvaliw $f wff ps $.
	f2_cbvaliw $f set x $.
	f3_cbvaliw $f set y $.
	e0_cbvaliw $e |- ( A. x ph -> A. y A. x ph ) $.
	e1_cbvaliw $e |- ( -. ps -> A. x -. ps ) $.
	e2_cbvaliw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_cbvaliw $p |- ( A. x ph -> A. y ps ) $= e0_cbvaliw e1_cbvaliw e2_cbvaliw f0_cbvaliw f1_cbvaliw f2_cbvaliw f3_cbvaliw p_spimw f0_cbvaliw f2_cbvaliw a_wal f1_cbvaliw f3_cbvaliw p_alrimih $.
$}

$(Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_cbvalivw $f wff ph $.
	f1_cbvalivw $f wff ps $.
	f2_cbvalivw $f set x $.
	f3_cbvalivw $f set y $.
	e0_cbvalivw $e |- ( x = y -> ( ph -> ps ) ) $.
	p_cbvalivw $p |- ( A. x ph -> A. y ps ) $= e0_cbvalivw f0_cbvalivw f1_cbvalivw f2_cbvalivw f3_cbvalivw p_spimvw f0_cbvalivw f2_cbvalivw a_wal f1_cbvalivw f3_cbvalivw p_alrimiv $.
$}


