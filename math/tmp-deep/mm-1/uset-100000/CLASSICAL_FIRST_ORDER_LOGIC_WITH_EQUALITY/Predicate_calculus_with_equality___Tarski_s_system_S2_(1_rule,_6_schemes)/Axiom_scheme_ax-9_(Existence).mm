$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Equality_predicate__define_substitution.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Axiom scheme ax-9 (Existence)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Existence.  One of the equality and substitution axioms of
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
	$v x $.
	$v y $.
	fax-9_0 $f set x $.
	fax-9_1 $f set y $.
	ax-9 $a |- -. A. x -. x = y $.
$}
$( Axiom B7 of [Tarski] p. 75, which requires that ` x ` and ` y ` be
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
	$v x $.
	$v y $.
	$d x y $.
	fax9v_0 $f set x $.
	fax9v_1 $f set y $.
	ax9v $p |- -. A. x -. x = y $= fax9v_0 fax9v_1 ax-9 $.
$}
$( At least one individual exists.  Weaker version of ~ a9e .  When
       possible, use of this theorem rather than ~ a9e is preferred since its
       derivation from axioms is much shorter.  (Contributed by NM,
       3-Aug-2017.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fa9ev_0 $f set x $.
	fa9ev_1 $f set y $.
	a9ev $p |- E. x x = y $= fa9ev_0 sup_set_class fa9ev_1 sup_set_class wceq fa9ev_0 wex fa9ev_0 sup_set_class fa9ev_1 sup_set_class wceq wn fa9ev_0 wal wn fa9ev_0 fa9ev_1 ax9v fa9ev_0 sup_set_class fa9ev_1 sup_set_class wceq fa9ev_0 df-ex mpbir $.
$}
$( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.)  (Proof shortened
       by Wolf Lammen, 7-Aug-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	fspimw_0 $f wff ph $.
	fspimw_1 $f wff ps $.
	fspimw_2 $f set x $.
	fspimw_3 $f set y $.
	espimw_0 $e |- ( -. ps -> A. x -. ps ) $.
	espimw_1 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimw $p |- ( A. x ph -> ps ) $= fspimw_2 sup_set_class fspimw_3 sup_set_class wceq wn fspimw_2 wal wn fspimw_0 fspimw_2 wal fspimw_1 wi fspimw_2 fspimw_3 ax9v fspimw_0 fspimw_1 fspimw_2 fspimw_3 espimw_0 espimw_1 spimfw ax-mp $.
$}
$( Specialization.  Lemma 8 of [KalishMontague] p. 87.  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ps $.
	fspimvw_0 $f wff ph $.
	fspimvw_1 $f wff ps $.
	fspimvw_2 $f set x $.
	fspimvw_3 $f set y $.
	espimvw_0 $e |- ( x = y -> ( ph -> ps ) ) $.
	spimvw $p |- ( A. x ph -> ps ) $= fspimvw_0 fspimvw_1 fspimvw_2 fspimvw_3 fspimvw_1 wn fspimvw_2 ax-17 espimvw_0 spimw $.
$}
$( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.)  (Proof shortened by Wolf Lammen,
       13-Aug-2017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	ispnfw_0 $f set y $.
	fspnfw_0 $f wff ph $.
	fspnfw_1 $f set x $.
	espnfw_0 $e |- ( -. ph -> A. x -. ph ) $.
	spnfw $p |- ( A. x ph -> ph ) $= fspnfw_0 fspnfw_0 fspnfw_1 ispnfw_0 espnfw_0 fspnfw_1 sup_set_class ispnfw_0 sup_set_class wceq fspnfw_0 idd spimw $.
$}
$( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	fcbvaliw_0 $f wff ph $.
	fcbvaliw_1 $f wff ps $.
	fcbvaliw_2 $f set x $.
	fcbvaliw_3 $f set y $.
	ecbvaliw_0 $e |- ( A. x ph -> A. y A. x ph ) $.
	ecbvaliw_1 $e |- ( -. ps -> A. x -. ps ) $.
	ecbvaliw_2 $e |- ( x = y -> ( ph -> ps ) ) $.
	cbvaliw $p |- ( A. x ph -> A. y ps ) $= fcbvaliw_0 fcbvaliw_2 wal fcbvaliw_1 fcbvaliw_3 ecbvaliw_0 fcbvaliw_0 fcbvaliw_1 fcbvaliw_2 fcbvaliw_3 ecbvaliw_1 ecbvaliw_2 spimw alrimih $.
$}
$( Change bound variable.  Uses only Tarski's FOL axiom schemes.  Part of
       Lemma 7 of [KalishMontague] p. 86.  (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ps $.
	$d y ph $.
	fcbvalivw_0 $f wff ph $.
	fcbvalivw_1 $f wff ps $.
	fcbvalivw_2 $f set x $.
	fcbvalivw_3 $f set y $.
	ecbvalivw_0 $e |- ( x = y -> ( ph -> ps ) ) $.
	cbvalivw $p |- ( A. x ph -> A. y ps ) $= fcbvalivw_0 fcbvalivw_2 wal fcbvalivw_1 fcbvalivw_3 fcbvalivw_0 fcbvalivw_1 fcbvalivw_2 fcbvalivw_3 ecbvalivw_0 spimvw alrimiv $.
$}

