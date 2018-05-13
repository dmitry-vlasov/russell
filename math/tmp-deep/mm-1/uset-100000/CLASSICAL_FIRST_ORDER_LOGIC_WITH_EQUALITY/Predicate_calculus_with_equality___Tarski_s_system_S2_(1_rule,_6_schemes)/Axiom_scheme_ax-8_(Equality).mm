$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-9_(Existence).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-8 (Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Axiom of Equality.  One of the equality and substitution axioms of
     predicate calculus with equality.  This is similar to, but not quite, a
     transitive law for equality (proved later as ~ equtr ).  This axiom scheme
     is a sub-scheme of Axiom Scheme B8 of system S2 of [Tarski], p. 75, whose
     general form cannot be represented with our notation.  Also appears as
     Axiom C7 of [Monk2] p. 105 and Axiom Scheme C8' in [Megill] p. 448 (p. 16
     of the preprint).

     The equality symbol was invented in 1527 by Robert Recorde.  He chose a
     pair of parallel lines of the same length because "noe .2. thynges, can be
     moare equalle."

     Note that this axiom is still valid even when any two or all three of
     ` x ` , ` y ` , and ` z ` are replaced with the same variable since they
     do not have any distinct variable (Metamath's $d) restrictions.  Because
     of this, we say that these three variables are "bundled" (a term coined by
     Raph Levien).  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x y z  $.
	f0_ax-8 $f set x $.
	f1_ax-8 $f set y $.
	f2_ax-8 $f set z $.
	a_ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.
$}

$(Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.) $)

${
	$v x  $.
	$d x y  $.
	f0_equid $f set x $.
	i0_equid $f set y $.
	p_equid $p |- x = x $= i0_equid f0_equid p_ax9v i0_equid f0_equid f0_equid a_ax-8 i0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq p_pm2.43i i0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq p_con3i f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid p_alimi f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid a_wal i0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid a_wal p_mto f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid a_ax-17 f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq f0_equid a_sup_set_class f0_equid a_sup_set_class a_wceq a_wn i0_equid a_wal p_mt3 $.
$}

$(Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)

${
	$v x y  $.
	f0_nfequid $f set x $.
	f1_nfequid $f set y $.
	p_nfequid $p |- F/ y x = x $= f0_nfequid p_equid f0_nfequid a_sup_set_class f0_nfequid a_sup_set_class a_wceq f1_nfequid p_nfth $.
$}

$(Commutative law for equality.  Lemma 3 of [KalishMontague] p. 85.  See
       also Lemma 7 of [Tarski] p. 69.  (Contributed by NM, 5-Aug-1993.)
       (Revised by NM, 9-Apr-2017.) $)

${
	$v x y  $.
	$d x  $.
	f0_equcomi $f set x $.
	f1_equcomi $f set y $.
	p_equcomi $p |- ( x = y -> y = x ) $= f0_equcomi p_equid f0_equcomi f1_equcomi f0_equcomi a_ax-8 f0_equcomi a_sup_set_class f1_equcomi a_sup_set_class a_wceq f0_equcomi a_sup_set_class f0_equcomi a_sup_set_class a_wceq f1_equcomi a_sup_set_class f0_equcomi a_sup_set_class a_wceq p_mpi $.
$}

$(Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)

${
	$v x y  $.
	f0_equcom $f set x $.
	f1_equcom $f set y $.
	p_equcom $p |- ( x = y <-> y = x ) $= f0_equcom f1_equcom p_equcomi f1_equcom f0_equcom p_equcomi f0_equcom a_sup_set_class f1_equcom a_sup_set_class a_wceq f1_equcom a_sup_set_class f0_equcom a_sup_set_class a_wceq p_impbii $.
$}

$(An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	f0_equcoms $f wff ph $.
	f1_equcoms $f set x $.
	f2_equcoms $f set y $.
	e0_equcoms $e |- ( x = y -> ph ) $.
	p_equcoms $p |- ( y = x -> ph ) $= f2_equcoms f1_equcoms p_equcomi e0_equcoms f2_equcoms a_sup_set_class f1_equcoms a_sup_set_class a_wceq f1_equcoms a_sup_set_class f2_equcoms a_sup_set_class a_wceq f0_equcoms p_syl $.
$}

$(An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2017.) $)

${
	$v x y z  $.
	f0_equequ1 $f set x $.
	f1_equequ1 $f set y $.
	f2_equequ1 $f set z $.
	p_equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $= f0_equequ1 f1_equequ1 f2_equequ1 a_ax-8 f1_equequ1 f0_equequ1 f2_equequ1 a_ax-8 f1_equequ1 a_sup_set_class f2_equequ1 a_sup_set_class a_wceq f0_equequ1 a_sup_set_class f2_equequ1 a_sup_set_class a_wceq a_wi f1_equequ1 f0_equequ1 p_equcoms f0_equequ1 a_sup_set_class f1_equequ1 a_sup_set_class a_wceq f0_equequ1 a_sup_set_class f2_equequ1 a_sup_set_class a_wceq f1_equequ1 a_sup_set_class f2_equequ1 a_sup_set_class a_wceq p_impbid $.
$}

$(An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)

${
	$v x y z  $.
	f0_equequ1OLD $f set x $.
	f1_equequ1OLD $f set y $.
	f2_equequ1OLD $f set z $.
	p_equequ1OLD $p |- ( x = y -> ( x = z <-> y = z ) ) $= f0_equequ1OLD f1_equequ1OLD f2_equequ1OLD a_ax-8 f0_equequ1OLD f1_equequ1OLD p_equcomi f1_equequ1OLD f0_equequ1OLD f2_equequ1OLD a_ax-8 f0_equequ1OLD a_sup_set_class f1_equequ1OLD a_sup_set_class a_wceq f1_equequ1OLD a_sup_set_class f0_equequ1OLD a_sup_set_class a_wceq f1_equequ1OLD a_sup_set_class f2_equequ1OLD a_sup_set_class a_wceq f0_equequ1OLD a_sup_set_class f2_equequ1OLD a_sup_set_class a_wceq a_wi p_syl f0_equequ1OLD a_sup_set_class f1_equequ1OLD a_sup_set_class a_wceq f0_equequ1OLD a_sup_set_class f2_equequ1OLD a_sup_set_class a_wceq f1_equequ1OLD a_sup_set_class f2_equequ1OLD a_sup_set_class a_wceq p_impbid $.
$}

$(An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Aug-2017.) $)

${
	$v x y z  $.
	f0_equequ2 $f set x $.
	f1_equequ2 $f set y $.
	f2_equequ2 $f set z $.
	p_equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $= f0_equequ2 f1_equequ2 f2_equequ2 p_equequ1 f0_equequ2 f2_equequ2 p_equcom f1_equequ2 f2_equequ2 p_equcom f0_equequ2 a_sup_set_class f1_equequ2 a_sup_set_class a_wceq f0_equequ2 a_sup_set_class f2_equequ2 a_sup_set_class a_wceq f1_equequ2 a_sup_set_class f2_equequ2 a_sup_set_class a_wceq f2_equequ2 a_sup_set_class f0_equequ2 a_sup_set_class a_wceq f2_equequ2 a_sup_set_class f1_equequ2 a_sup_set_class a_wceq p_3bitr3g $.
$}

$(One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)

${
	$v x  $.
	f0_stdpc6 $f set x $.
	p_stdpc6 $p |- A. x x = x $= f0_stdpc6 p_equid f0_stdpc6 a_sup_set_class f0_stdpc6 a_sup_set_class a_wceq f0_stdpc6 a_ax-gen $.
$}

$(A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)

${
	$v x y z  $.
	f0_equtr $f set x $.
	f1_equtr $f set y $.
	f2_equtr $f set z $.
	p_equtr $p |- ( x = y -> ( y = z -> x = z ) ) $= f1_equtr f0_equtr f2_equtr a_ax-8 f1_equtr a_sup_set_class f2_equtr a_sup_set_class a_wceq f0_equtr a_sup_set_class f2_equtr a_sup_set_class a_wceq a_wi f1_equtr f0_equtr p_equcoms $.
$}

$(A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)

${
	$v x y z  $.
	f0_equtrr $f set x $.
	f1_equtrr $f set y $.
	f2_equtrr $f set z $.
	p_equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $= f2_equtrr f0_equtrr f1_equtrr p_equtr f2_equtrr a_sup_set_class f0_equtrr a_sup_set_class a_wceq f0_equtrr a_sup_set_class f1_equtrr a_sup_set_class a_wceq f2_equtrr a_sup_set_class f1_equtrr a_sup_set_class a_wceq p_com12 $.
$}

$(A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v x y z  $.
	f0_equtr2 $f set x $.
	f1_equtr2 $f set y $.
	f2_equtr2 $f set z $.
	p_equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $= f2_equtr2 f1_equtr2 f0_equtr2 p_equtrr f0_equtr2 a_sup_set_class f2_equtr2 a_sup_set_class a_wceq f0_equtr2 a_sup_set_class f1_equtr2 a_sup_set_class a_wceq a_wi f2_equtr2 f1_equtr2 p_equcoms f1_equtr2 a_sup_set_class f2_equtr2 a_sup_set_class a_wceq f0_equtr2 a_sup_set_class f2_equtr2 a_sup_set_class a_wceq f0_equtr2 a_sup_set_class f1_equtr2 a_sup_set_class a_wceq p_impcom $.
$}

$(Two equivalent ways of expressing ~ ax-12 .  See the comment for
     ~ ax-12 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 12-Aug-2017.) $)

${
	$v x y z  $.
	f0_ax12b $f set x $.
	f1_ax12b $f set y $.
	f2_ax12b $f set z $.
	p_ax12b $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) ) <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $= f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi p_id f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn p_a1dd f2_ax12b f1_ax12b f0_ax12b p_equtrr f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wi f2_ax12b f1_ax12b p_equcoms f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq p_con3rr3 f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi p_id f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal p_com4l f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi p_com23 f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi p_mpdd f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal p_com3r f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi f0_ax12b a_sup_set_class f1_ax12b a_sup_set_class a_wceq a_wn f0_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq a_wn f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f1_ax12b a_sup_set_class f2_ax12b a_sup_set_class a_wceq f0_ax12b a_wal a_wi a_wi a_wi p_impbii $.
$}

$(Obsolete version of ~ ax12b as of 12-Aug-2017.  (Contributed by NM,
     2-May-2017.)  (New usage is discouraged.) $)

${
	$v x y z  $.
	f0_ax12bOLD $f set x $.
	f1_ax12bOLD $f set y $.
	f2_ax12bOLD $f set z $.
	p_ax12bOLD $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) ) <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $= f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal p_bi2.04 f2_ax12bOLD f1_ax12bOLD f0_ax12bOLD p_equtrr f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wi f2_ax12bOLD f1_ax12bOLD p_equcoms f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq p_con3d f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn p_pm4.71d f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal p_imbi1d f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi p_pm5.74i f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi p_bitri f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal p_bi2.04 f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi p_bitri f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi p_impexp f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn a_wa f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi f0_ax12bOLD a_sup_set_class f1_ax12bOLD a_sup_set_class a_wceq a_wn f0_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq a_wn f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f1_ax12bOLD a_sup_set_class f2_ax12bOLD a_sup_set_class a_wceq f0_ax12bOLD a_wal a_wi a_wi a_wi p_bitri $.
$}

$(Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  TO DO:  Do we need this theorem?  If not,
       maybe it should be deleted.  (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_spfw $f wff ph $.
	f1_spfw $f wff ps $.
	f2_spfw $f set x $.
	f3_spfw $f set y $.
	e0_spfw $e |- ( -. ps -> A. x -. ps ) $.
	e1_spfw $e |- ( A. x ph -> A. y A. x ph ) $.
	e2_spfw $e |- ( -. ph -> A. y -. ph ) $.
	e3_spfw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_spfw $p |- ( A. x ph -> ph ) $= e1_spfw f0_spfw f2_spfw a_wal f1_spfw f3_spfw a_ax-5 e2_spfw e3_spfw f2_spfw a_sup_set_class f3_spfw a_sup_set_class a_wceq f0_spfw f1_spfw p_biimprd f1_spfw f0_spfw a_wi f2_spfw f3_spfw p_equcoms f1_spfw f0_spfw f3_spfw f2_spfw p_spimw f0_spfw f2_spfw a_wal f0_spfw f2_spfw a_wal f3_spfw a_wal f0_spfw f2_spfw a_wal f1_spfw a_wi f3_spfw a_wal f1_spfw f3_spfw a_wal f0_spfw p_syl56 e0_spfw e3_spfw f2_spfw a_sup_set_class f3_spfw a_sup_set_class a_wceq f0_spfw f1_spfw p_biimpd f0_spfw f1_spfw f2_spfw f3_spfw p_spimw f0_spfw f2_spfw a_wal f1_spfw a_wi f0_spfw f2_spfw a_wal f0_spfw a_wi f3_spfw p_mpg $.
$}

$(Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Obsolete
       version of ~ spnfw as of 13-Aug-2017.  (Contributed by NM, 1-Aug-2017.)
       (New usage is discouraged.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_spnfwOLD $f wff ph $.
	f1_spnfwOLD $f set x $.
	i0_spnfwOLD $f set y $.
	e0_spnfwOLD $e |- ( -. ph -> A. x -. ph ) $.
	p_spnfwOLD $p |- ( A. x ph -> ph ) $= e0_spnfwOLD f0_spnfwOLD f1_spnfwOLD a_wal i0_spnfwOLD a_ax-17 f0_spnfwOLD a_wn i0_spnfwOLD a_ax-17 f1_spnfwOLD a_sup_set_class i0_spnfwOLD a_sup_set_class a_wceq f0_spnfwOLD p_biidd f0_spnfwOLD f0_spnfwOLD f1_spnfwOLD i0_spnfwOLD p_spfw $.
$}

$(Weak version of ~ 19.8a .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.) $)

${
	$v ph x  $.
	f0_19.8w $f wff ph $.
	f1_19.8w $f set x $.
	e0_19.8w $e |- ( ph -> A. x ph ) $.
	p_19.8w $p |- ( ph -> E. x ph ) $= e0_19.8w f0_19.8w p_notnot f0_19.8w p_notnot f0_19.8w f0_19.8w a_wn a_wn f1_19.8w p_albii f0_19.8w f0_19.8w f1_19.8w a_wal f0_19.8w a_wn a_wn f0_19.8w a_wn a_wn f1_19.8w a_wal p_3imtr3i f0_19.8w a_wn f1_19.8w p_spnfw f0_19.8w a_wn f1_19.8w a_wal f0_19.8w p_con2i f0_19.8w f1_19.8w a_df-ex f0_19.8w f0_19.8w a_wn f1_19.8w a_wal a_wn f0_19.8w f1_19.8w a_wex p_sylibr $.
$}

$(Weak version of specialization scheme ~ sp .  Lemma 9 of
       [KalishMontague] p. 87.  While it appears that ~ sp in its general form
       does not follow from Tarski's FOL axiom schemes, from this theorem we
       can prove any instance of ~ sp having no wff metavariables and mutually
       distinct set variables (see ~ ax11wdemo for an example of the procedure
       to eliminate the hypothesis).  Other approximations of ~ sp are ~ spfw
       (minimal distinct variable requirements), ~ spnfw (when ` x ` is not
       free in ` -. ph ` ), ~ spvw (when ` x ` does not appear in ` ph ` ),
       ~ sptruw (when ` ph ` is true), and ~ spfalw (when ` ph ` is false).
       (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_spw $f wff ph $.
	f1_spw $f wff ps $.
	f2_spw $f set x $.
	f3_spw $f set y $.
	e0_spw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_spw $p |- ( A. x ph -> ph ) $= f0_spw f2_spw a_wal f3_spw a_ax-17 f0_spw f2_spw a_wal f1_spw f3_spw a_ax-5 e0_spw f2_spw a_sup_set_class f3_spw a_sup_set_class a_wceq f0_spw f1_spw p_biimprd f1_spw f0_spw a_wi f2_spw f3_spw p_equcoms f1_spw f0_spw f3_spw f2_spw p_spimvw f0_spw f2_spw a_wal f0_spw f2_spw a_wal f3_spw a_wal f0_spw f2_spw a_wal f1_spw a_wi f3_spw a_wal f1_spw f3_spw a_wal f0_spw p_syl56 e0_spw f2_spw a_sup_set_class f3_spw a_sup_set_class a_wceq f0_spw f1_spw p_biimpd f0_spw f1_spw f2_spw f3_spw p_spimvw f0_spw f2_spw a_wal f1_spw a_wi f0_spw f2_spw a_wal f0_spw a_wi f3_spw p_mpg $.
$}

$(Version of ~ sp when ` x ` does not occur in ` ph ` .  This provides the
       other direction of ~ ax-17 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)

${
	$v ph x  $.
	$d x y ph  $.
	f0_spvw $f wff ph $.
	f1_spvw $f set x $.
	i0_spvw $f set y $.
	p_spvw $p |- ( A. x ph -> ph ) $= f1_spvw a_sup_set_class i0_spvw a_sup_set_class a_wceq f0_spvw p_biidd f0_spvw f0_spvw f1_spvw i0_spvw p_spw $.
$}

$(Special case of Theorem 19.3 of [Margaris] p. 89.  (Contributed by NM,
       1-Aug-2017.) $)

${
	$v ph x  $.
	$d x ph  $.
	f0_19.3v $f wff ph $.
	f1_19.3v $f set x $.
	p_19.3v $p |- ( A. x ph <-> ph ) $= f0_19.3v f1_19.3v p_spvw f0_19.3v f1_19.3v a_ax-17 f0_19.3v f1_19.3v a_wal f0_19.3v p_impbii $.
$}

$(Special case of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-May-1995.)  (Revised by NM, 1-Aug-2017.) $)

${
	$v ph x  $.
	$d x ph  $.
	f0_19.9v $f wff ph $.
	f1_19.9v $f set x $.
	p_19.9v $p |- ( E. x ph <-> ph ) $= f0_19.9v f1_19.9v a_df-ex f0_19.9v a_wn f1_19.9v p_19.3v f0_19.9v a_wn f1_19.9v a_wal f0_19.9v p_con2bii f0_19.9v f1_19.9v a_wex f0_19.9v a_wn f1_19.9v a_wal a_wn f0_19.9v p_bitr4i $.
$}

$(Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)

${
	$v ph ps ch x  $.
	$d x ch  $.
	$d x ph  $.
	f0_exlimdv $f wff ph $.
	f1_exlimdv $f wff ps $.
	f2_exlimdv $f wff ch $.
	f3_exlimdv $f set x $.
	e0_exlimdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $= e0_exlimdv f0_exlimdv f1_exlimdv f2_exlimdv f3_exlimdv p_eximdv f2_exlimdv f3_exlimdv p_19.9v f0_exlimdv f1_exlimdv f3_exlimdv a_wex f2_exlimdv f3_exlimdv a_wex f2_exlimdv p_syl6ib $.
$}

$(Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 15-Jun-2016.) $)

${
	$v ph ps ch x  $.
	$d x ch  $.
	$d x ph  $.
	f0_exlimddv $f wff ph $.
	f1_exlimddv $f wff ps $.
	f2_exlimddv $f wff ch $.
	f3_exlimddv $f set x $.
	e0_exlimddv $e |- ( ph -> E. x ps ) $.
	e1_exlimddv $e |- ( ( ph /\ ps ) -> ch ) $.
	p_exlimddv $p |- ( ph -> ch ) $= e0_exlimddv e1_exlimddv f0_exlimddv f1_exlimddv f2_exlimddv p_ex f0_exlimddv f1_exlimddv f2_exlimddv f3_exlimddv p_exlimdv f0_exlimddv f1_exlimddv f3_exlimddv a_wex f2_exlimddv p_mpd $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.

       This inference, along with our many variants such as ~ rexlimdv , is
       used to implement a metatheorem called "Rule C" that is given in many
       logic textbooks.  See, for example, Rule C in [Mendelson] p. 81, Rule C
       in [Margaris] p. 40, or Rule C in Hirst and Hirst's _A Primer for Logic
       and Proof_ p. 59 (PDF p. 65) at
       ~ http://www.mathsci.appstate.edu/~~hirstjl/primer/hirst.pdf .

       In informal proofs, the statement "Let ` C ` be an element such that..."
       almost always means an implicit application of Rule C.

       In essence, Rule C states that if we can prove that some element ` x `
       exists satisfying a wff, i.e. ` E. x ph ( x ) ` where ` ph ( x ) ` has
       ` x ` free, then we can use ` ph ( C ) ` as a hypothesis for the proof
       where ` C ` is a new (ficticious) constant not appearing previously in
       the proof, nor in any axioms used, nor in the theorem to be proved.  The
       purpose of Rule C is to get rid of the existential quantifier.

       We cannot do this in Metamath directly.  Instead, we use the original
       ` ph ` (containing ` x ` ) as an antecedent for the main part of the
       proof.  We eventually arrive at ` ( ph -> ps ) ` where ` ps ` is the
       theorem to be proved and does not contain ` x ` .  Then we apply
       ~ exlimiv to arrive at ` ( E. x ph -> ps ) ` .  Finally, we separately
       prove ` E. x ph ` and detach it with modus ponens ~ ax-mp to arrive at
       the final theorem ` ps ` .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	$d x ps  $.
	f0_exlimiv $f wff ph $.
	f1_exlimiv $f wff ps $.
	f2_exlimiv $f set x $.
	e0_exlimiv $e |- ( ph -> ps ) $.
	p_exlimiv $p |- ( E. x ph -> ps ) $= e0_exlimiv f0_exlimiv f1_exlimiv f2_exlimiv p_eximi f1_exlimiv f2_exlimiv p_19.9v f0_exlimiv f2_exlimiv a_wex f1_exlimiv f2_exlimiv a_wex f1_exlimiv p_sylib $.
$}

$(Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       1-Aug-1995.) $)

${
	$v ph ps x y  $.
	$d x ps  $.
	$d y ps  $.
	f0_exlimivv $f wff ph $.
	f1_exlimivv $f wff ps $.
	f2_exlimivv $f set x $.
	f3_exlimivv $f set y $.
	e0_exlimivv $e |- ( ph -> ps ) $.
	p_exlimivv $p |- ( E. x E. y ph -> ps ) $= e0_exlimivv f0_exlimivv f1_exlimivv f3_exlimivv p_exlimiv f0_exlimivv f3_exlimivv a_wex f1_exlimivv f2_exlimivv p_exlimiv $.
$}

$(Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)

${
	$v ph ps ch x y  $.
	$d x ch  $.
	$d x ph  $.
	$d y ch  $.
	$d y ph  $.
	f0_exlimdvv $f wff ph $.
	f1_exlimdvv $f wff ps $.
	f2_exlimdvv $f wff ch $.
	f3_exlimdvv $f set x $.
	f4_exlimdvv $f set y $.
	e0_exlimdvv $e |- ( ph -> ( ps -> ch ) ) $.
	p_exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $= e0_exlimdvv f0_exlimdvv f1_exlimdvv f2_exlimdvv f4_exlimdvv p_exlimdv f0_exlimdvv f1_exlimdvv f4_exlimdvv a_wex f2_exlimdvv f3_exlimdvv p_exlimdv $.
$}

$(Version of ~ sp when ` ph ` is true.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)

${
	$v ph x  $.
	f0_sptruw $f wff ph $.
	f1_sptruw $f set x $.
	e0_sptruw $e |- ph $.
	p_sptruw $p |- ( A. x ph -> ph ) $= e0_sptruw f0_sptruw f0_sptruw f1_sptruw a_wal p_a1i $.
$}

$(Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_spfalw $f wff ph $.
	f1_spfalw $f set x $.
	i0_spfalw $f set y $.
	e0_spfalw $e |- -. ph $.
	p_spfalw $p |- ( A. x ph -> ph ) $= e0_spfalw f0_spfalw p_bifal f0_spfalw a_wfal a_wb f1_spfalw a_sup_set_class i0_spfalw a_sup_set_class a_wceq p_a1i f0_spfalw a_wfal f1_spfalw i0_spfalw p_spw $.
$}

$(Theorem 19.2 of [Margaris] p. 89.  Note:  This proof is very different
     from Margaris' because we only have Tarski's FOL axiom schemes available
     at this point.  See the later ~ 19.2g for a more conventional proof.
     (Contributed by NM, 2-Aug-2017.) $)

${
	$v ph x  $.
	f0_19.2 $f wff ph $.
	f1_19.2 $f set x $.
	p_19.2 $p |- ( A. x ph -> E. x ph ) $= f1_19.2 p_equid f1_19.2 p_equid f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq p_notnoti f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq a_wn f1_19.2 p_spfalw f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq a_wn f1_19.2 a_wal f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq p_mt2 f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq f0_19.2 p_idd f0_19.2 f0_19.2 f1_19.2 f1_19.2 p_speimfw f1_19.2 a_sup_set_class f1_19.2 a_sup_set_class a_wceq a_wn f1_19.2 a_wal a_wn f0_19.2 f1_19.2 a_wal f0_19.2 f1_19.2 a_wex a_wi a_ax-mp $.
$}

$(Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.39 $f wff ph $.
	f1_19.39 $f wff ps $.
	f2_19.39 $f set x $.
	p_19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $= f0_19.39 f2_19.39 p_19.2 f0_19.39 f2_19.39 a_wal f0_19.39 f2_19.39 a_wex f1_19.39 f2_19.39 a_wex p_imim1i f0_19.39 f1_19.39 f2_19.39 p_19.35 f0_19.39 f2_19.39 a_wex f1_19.39 f2_19.39 a_wex a_wi f0_19.39 f2_19.39 a_wal f1_19.39 f2_19.39 a_wex a_wi f0_19.39 f1_19.39 a_wi f2_19.39 a_wex p_sylibr $.
$}

$(Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.24 $f wff ph $.
	f1_19.24 $f wff ps $.
	f2_19.24 $f set x $.
	p_19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $= f1_19.24 f2_19.24 p_19.2 f1_19.24 f2_19.24 a_wal f1_19.24 f2_19.24 a_wex f0_19.24 f2_19.24 a_wal p_imim2i f0_19.24 f1_19.24 f2_19.24 p_19.35 f0_19.24 f2_19.24 a_wal f1_19.24 f2_19.24 a_wal a_wi f0_19.24 f2_19.24 a_wal f1_19.24 f2_19.24 a_wex a_wi f0_19.24 f1_19.24 a_wi f2_19.24 a_wex p_sylibr $.
$}

$(Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph ps x  $.
	f0_19.34 $f wff ph $.
	f1_19.34 $f wff ps $.
	f2_19.34 $f set x $.
	p_19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $= f0_19.34 f2_19.34 p_19.2 f0_19.34 f2_19.34 a_wal f0_19.34 f2_19.34 a_wex f1_19.34 f2_19.34 a_wex p_orim1i f0_19.34 f1_19.34 f2_19.34 p_19.43 f0_19.34 f2_19.34 a_wal f1_19.34 f2_19.34 a_wex a_wo f0_19.34 f2_19.34 a_wex f1_19.34 f2_19.34 a_wex a_wo f0_19.34 f1_19.34 a_wo f2_19.34 a_wex p_sylibr $.
$}

$(Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_cbvalw $f wff ph $.
	f1_cbvalw $f wff ps $.
	f2_cbvalw $f set x $.
	f3_cbvalw $f set y $.
	e0_cbvalw $e |- ( A. x ph -> A. y A. x ph ) $.
	e1_cbvalw $e |- ( -. ps -> A. x -. ps ) $.
	e2_cbvalw $e |- ( A. y ps -> A. x A. y ps ) $.
	e3_cbvalw $e |- ( -. ph -> A. y -. ph ) $.
	e4_cbvalw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvalw $p |- ( A. x ph <-> A. y ps ) $= e0_cbvalw e1_cbvalw e4_cbvalw f2_cbvalw a_sup_set_class f3_cbvalw a_sup_set_class a_wceq f0_cbvalw f1_cbvalw p_biimpd f0_cbvalw f1_cbvalw f2_cbvalw f3_cbvalw p_cbvaliw e2_cbvalw e3_cbvalw e4_cbvalw f2_cbvalw a_sup_set_class f3_cbvalw a_sup_set_class a_wceq f0_cbvalw f1_cbvalw p_biimprd f1_cbvalw f0_cbvalw a_wi f2_cbvalw f3_cbvalw p_equcoms f1_cbvalw f0_cbvalw f3_cbvalw f2_cbvalw p_cbvaliw f0_cbvalw f2_cbvalw a_wal f1_cbvalw f3_cbvalw a_wal p_impbii $.
$}

$(Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_cbvalvw $f wff ph $.
	f1_cbvalvw $f wff ps $.
	f2_cbvalvw $f set x $.
	f3_cbvalvw $f set y $.
	e0_cbvalvw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvalvw $p |- ( A. x ph <-> A. y ps ) $= e0_cbvalvw f2_cbvalvw a_sup_set_class f3_cbvalvw a_sup_set_class a_wceq f0_cbvalvw f1_cbvalvw p_biimpd f0_cbvalvw f1_cbvalvw f2_cbvalvw f3_cbvalvw p_cbvalivw e0_cbvalvw f2_cbvalvw a_sup_set_class f3_cbvalvw a_sup_set_class a_wceq f0_cbvalvw f1_cbvalvw p_biimprd f1_cbvalvw f0_cbvalvw a_wi f2_cbvalvw f3_cbvalvw p_equcoms f1_cbvalvw f0_cbvalvw f3_cbvalvw f2_cbvalvw p_cbvalivw f0_cbvalvw f2_cbvalvw a_wal f1_cbvalvw f3_cbvalvw a_wal p_impbii $.
$}

$(Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d x ps  $.
	$d y ph  $.
	f0_cbvexvw $f wff ph $.
	f1_cbvexvw $f wff ps $.
	f2_cbvexvw $f set x $.
	f3_cbvexvw $f set y $.
	e0_cbvexvw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvexvw $p |- ( E. x ph <-> E. y ps ) $= e0_cbvexvw f2_cbvexvw a_sup_set_class f3_cbvexvw a_sup_set_class a_wceq f0_cbvexvw f1_cbvexvw p_notbid f0_cbvexvw a_wn f1_cbvexvw a_wn f2_cbvexvw f3_cbvexvw p_cbvalvw f0_cbvexvw a_wn f2_cbvexvw a_wal f1_cbvexvw a_wn f3_cbvexvw a_wal p_notbii f0_cbvexvw f2_cbvexvw a_df-ex f1_cbvexvw f3_cbvexvw a_df-ex f0_cbvexvw a_wn f2_cbvexvw a_wal a_wn f1_cbvexvw a_wn f3_cbvexvw a_wal a_wn f0_cbvexvw f2_cbvexvw a_wex f1_cbvexvw f3_cbvexvw a_wex p_3bitr4i $.
$}

$(Weak version of ~ alcom .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)

${
	$v ph ps x y z  $.
	$d y z  $.
	$d x y  $.
	$d z ph  $.
	$d y ps  $.
	f0_alcomiw $f wff ph $.
	f1_alcomiw $f wff ps $.
	f2_alcomiw $f set x $.
	f3_alcomiw $f set y $.
	f4_alcomiw $f set z $.
	e0_alcomiw $e |- ( y = z -> ( ph <-> ps ) ) $.
	p_alcomiw $p |- ( A. x A. y ph -> A. y A. x ph ) $= e0_alcomiw f3_alcomiw a_sup_set_class f4_alcomiw a_sup_set_class a_wceq f0_alcomiw f1_alcomiw p_biimpd f0_alcomiw f1_alcomiw f3_alcomiw f4_alcomiw p_cbvalivw f0_alcomiw f3_alcomiw a_wal f1_alcomiw f4_alcomiw a_wal f2_alcomiw p_alimi f1_alcomiw f4_alcomiw a_wal f2_alcomiw a_wal f3_alcomiw a_ax-17 e0_alcomiw f3_alcomiw a_sup_set_class f4_alcomiw a_sup_set_class a_wceq f0_alcomiw f1_alcomiw p_biimprd f1_alcomiw f0_alcomiw a_wi f3_alcomiw f4_alcomiw p_equcoms f1_alcomiw f0_alcomiw f4_alcomiw f3_alcomiw p_spimvw f1_alcomiw f4_alcomiw a_wal f0_alcomiw f2_alcomiw p_alimi f1_alcomiw f4_alcomiw a_wal f2_alcomiw a_wal f0_alcomiw f2_alcomiw a_wal f3_alcomiw p_alimi f0_alcomiw f3_alcomiw a_wal f2_alcomiw a_wal f1_alcomiw f4_alcomiw a_wal f2_alcomiw a_wal f1_alcomiw f4_alcomiw a_wal f2_alcomiw a_wal f3_alcomiw a_wal f0_alcomiw f2_alcomiw a_wal f3_alcomiw a_wal p_3syl $.
$}

$(Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	f0_hbn1fw $f wff ph $.
	f1_hbn1fw $f wff ps $.
	f2_hbn1fw $f set x $.
	f3_hbn1fw $f set y $.
	e0_hbn1fw $e |- ( A. x ph -> A. y A. x ph ) $.
	e1_hbn1fw $e |- ( -. ps -> A. x -. ps ) $.
	e2_hbn1fw $e |- ( A. y ps -> A. x A. y ps ) $.
	e3_hbn1fw $e |- ( -. ph -> A. y -. ph ) $.
	e4_hbn1fw $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
	e5_hbn1fw $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $= e0_hbn1fw e1_hbn1fw e2_hbn1fw e3_hbn1fw e5_hbn1fw f0_hbn1fw f1_hbn1fw f2_hbn1fw f3_hbn1fw p_cbvalw f0_hbn1fw f2_hbn1fw a_wal f1_hbn1fw f3_hbn1fw a_wal p_biimpri f1_hbn1fw f3_hbn1fw a_wal f0_hbn1fw f2_hbn1fw a_wal p_con3i e4_hbn1fw e0_hbn1fw e1_hbn1fw e2_hbn1fw e3_hbn1fw e5_hbn1fw f0_hbn1fw f1_hbn1fw f2_hbn1fw f3_hbn1fw p_cbvalw f0_hbn1fw f2_hbn1fw a_wal f1_hbn1fw f3_hbn1fw a_wal p_biimpi f0_hbn1fw f2_hbn1fw a_wal f1_hbn1fw f3_hbn1fw a_wal p_con3i f1_hbn1fw f3_hbn1fw a_wal a_wn f0_hbn1fw f2_hbn1fw a_wal a_wn f2_hbn1fw p_alimi f0_hbn1fw f2_hbn1fw a_wal a_wn f1_hbn1fw f3_hbn1fw a_wal a_wn f1_hbn1fw f3_hbn1fw a_wal a_wn f2_hbn1fw a_wal f0_hbn1fw f2_hbn1fw a_wal a_wn f2_hbn1fw a_wal p_3syl $.
$}

$(Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	$d x y  $.
	f0_hbn1w $f wff ph $.
	f1_hbn1w $f wff ps $.
	f2_hbn1w $f set x $.
	f3_hbn1w $f set y $.
	e0_hbn1w $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $= f0_hbn1w f2_hbn1w a_wal f3_hbn1w a_ax-17 f1_hbn1w a_wn f2_hbn1w a_ax-17 f1_hbn1w f3_hbn1w a_wal f2_hbn1w a_ax-17 f0_hbn1w a_wn f3_hbn1w a_ax-17 f1_hbn1w f3_hbn1w a_wal a_wn f2_hbn1w a_ax-17 e0_hbn1w f0_hbn1w f1_hbn1w f2_hbn1w f3_hbn1w p_hbn1fw $.
$}

$(Weak version of ~ hba1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	$d x y  $.
	f0_hba1w $f wff ph $.
	f1_hba1w $f wff ps $.
	f2_hba1w $f set x $.
	f3_hba1w $f set y $.
	e0_hba1w $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_hba1w $p |- ( A. x ph -> A. x A. x ph ) $= e0_hba1w f0_hba1w f1_hba1w f2_hba1w f3_hba1w p_cbvalvw f0_hba1w f2_hba1w a_wal f1_hba1w f3_hba1w a_wal a_wb f2_hba1w a_sup_set_class f3_hba1w a_sup_set_class a_wceq p_a1i f2_hba1w a_sup_set_class f3_hba1w a_sup_set_class a_wceq f0_hba1w f2_hba1w a_wal f1_hba1w f3_hba1w a_wal p_notbid f0_hba1w f2_hba1w a_wal a_wn f1_hba1w f3_hba1w a_wal a_wn f2_hba1w f3_hba1w p_spw f0_hba1w f2_hba1w a_wal a_wn f2_hba1w a_wal f0_hba1w f2_hba1w a_wal p_con2i e0_hba1w f0_hba1w f1_hba1w f2_hba1w f3_hba1w p_cbvalvw f0_hba1w f2_hba1w a_wal f1_hba1w f3_hba1w a_wal a_wb f2_hba1w a_sup_set_class f3_hba1w a_sup_set_class a_wceq p_a1i f2_hba1w a_sup_set_class f3_hba1w a_sup_set_class a_wceq f0_hba1w f2_hba1w a_wal f1_hba1w f3_hba1w a_wal p_notbid f0_hba1w f2_hba1w a_wal a_wn f1_hba1w f3_hba1w a_wal a_wn f2_hba1w f3_hba1w p_hbn1w e0_hba1w f0_hba1w f1_hba1w f2_hba1w f3_hba1w p_hbn1w f0_hba1w f2_hba1w a_wal f0_hba1w f2_hba1w a_wal a_wn f2_hba1w a_wal p_con1i f0_hba1w f2_hba1w a_wal a_wn f2_hba1w a_wal a_wn f0_hba1w f2_hba1w a_wal f2_hba1w p_alimi f0_hba1w f2_hba1w a_wal f0_hba1w f2_hba1w a_wal a_wn f2_hba1w a_wal a_wn f0_hba1w f2_hba1w a_wal a_wn f2_hba1w a_wal a_wn f2_hba1w a_wal f0_hba1w f2_hba1w a_wal f2_hba1w a_wal p_3syl $.
$}

$(Weak version of ~ hbe1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	$d x ps  $.
	$d x y  $.
	f0_hbe1w $f wff ph $.
	f1_hbe1w $f wff ps $.
	f2_hbe1w $f set x $.
	f3_hbe1w $f set y $.
	e0_hbe1w $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_hbe1w $p |- ( E. x ph -> A. x E. x ph ) $= f0_hbe1w f2_hbe1w a_df-ex e0_hbe1w f2_hbe1w a_sup_set_class f3_hbe1w a_sup_set_class a_wceq f0_hbe1w f1_hbe1w p_notbid f0_hbe1w a_wn f1_hbe1w a_wn f2_hbe1w f3_hbe1w p_hbn1w f0_hbe1w f2_hbe1w a_wex f0_hbe1w a_wn f2_hbe1w a_wal a_wn f2_hbe1w p_hbxfrbi $.
$}

$(Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct i.e. are
       not bundled.  (Contributed by NM, 19-Apr-2017.) $)

${
	$v ph ps x y z  $.
	$d x z  $.
	$d x y  $.
	$d z ph  $.
	$d x ps  $.
	f0_hbalw $f wff ph $.
	f1_hbalw $f wff ps $.
	f2_hbalw $f set x $.
	f3_hbalw $f set y $.
	f4_hbalw $f set z $.
	e0_hbalw $e |- ( x = z -> ( ph <-> ps ) ) $.
	e1_hbalw $e |- ( ph -> A. x ph ) $.
	p_hbalw $p |- ( A. y ph -> A. x A. y ph ) $= e1_hbalw f0_hbalw f0_hbalw f2_hbalw a_wal f3_hbalw p_alimi e0_hbalw f0_hbalw f1_hbalw f3_hbalw f2_hbalw f4_hbalw p_alcomiw f0_hbalw f3_hbalw a_wal f0_hbalw f2_hbalw a_wal f3_hbalw a_wal f0_hbalw f3_hbalw a_wal f2_hbalw a_wal p_syl $.
$}


