$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_scheme_ax-9_(Existence).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Axiom scheme ax-8 (Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Equality.  One of the equality and substitution axioms of
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
	$v x $.
	$v y $.
	$v z $.
	fax-8_0 $f set x $.
	fax-8_1 $f set y $.
	fax-8_2 $f set z $.
	ax-8 $a |- ( x = y -> ( x = z -> y = z ) ) $.
$}
$( Identity law for equality.  Lemma 2 of [KalishMontague] p. 85.  See also
       Lemma 6 of [Tarski] p. 68.  (Contributed by NM, 1-Apr-2005.)  (Revised
       by NM, 9-Apr-2017.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	iequid_0 $f set y $.
	fequid_0 $f set x $.
	equid $p |- x = x $= fequid_0 sup_set_class fequid_0 sup_set_class wceq fequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 wal fequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 wal iequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 wal iequid_0 fequid_0 ax9v fequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 iequid_0 sup_set_class fequid_0 sup_set_class wceq fequid_0 sup_set_class fequid_0 sup_set_class wceq iequid_0 sup_set_class fequid_0 sup_set_class wceq fequid_0 sup_set_class fequid_0 sup_set_class wceq iequid_0 fequid_0 fequid_0 ax-8 pm2.43i con3i alimi mto fequid_0 sup_set_class fequid_0 sup_set_class wceq wn iequid_0 ax-17 mt3 $.
$}
$( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (Contributed by NM,
     13-Jan-2011.)  (Revised by NM, 21-Aug-2017.) $)
${
	$v x $.
	$v y $.
	fnfequid_0 $f set x $.
	fnfequid_1 $f set y $.
	nfequid $p |- F/ y x = x $= fnfequid_0 sup_set_class fnfequid_0 sup_set_class wceq fnfequid_1 fnfequid_0 equid nfth $.
$}
$( Commutative law for equality.  Lemma 3 of [KalishMontague] p. 85.  See
       also Lemma 7 of [Tarski] p. 69.  (Contributed by NM, 5-Aug-1993.)
       (Revised by NM, 9-Apr-2017.) $)
${
	$v x $.
	$v y $.
	fequcomi_0 $f set x $.
	fequcomi_1 $f set y $.
	equcomi $p |- ( x = y -> y = x ) $= fequcomi_0 sup_set_class fequcomi_1 sup_set_class wceq fequcomi_0 sup_set_class fequcomi_0 sup_set_class wceq fequcomi_1 sup_set_class fequcomi_0 sup_set_class wceq fequcomi_0 equid fequcomi_0 fequcomi_1 fequcomi_0 ax-8 mpi $.
$}
$( Commutative law for equality.  (Contributed by NM, 20-Aug-1993.) $)
${
	$v x $.
	$v y $.
	fequcom_0 $f set x $.
	fequcom_1 $f set y $.
	equcom $p |- ( x = y <-> y = x ) $= fequcom_0 sup_set_class fequcom_1 sup_set_class wceq fequcom_1 sup_set_class fequcom_0 sup_set_class wceq fequcom_0 fequcom_1 equcomi fequcom_1 fequcom_0 equcomi impbii $.
$}
$( An inference commuting equality in antecedent.  Used to eliminate the
       need for a syllogism.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	fequcoms_0 $f wff ph $.
	fequcoms_1 $f set x $.
	fequcoms_2 $f set y $.
	eequcoms_0 $e |- ( x = y -> ph ) $.
	equcoms $p |- ( y = x -> ph ) $= fequcoms_2 sup_set_class fequcoms_1 sup_set_class wceq fequcoms_1 sup_set_class fequcoms_2 sup_set_class wceq fequcoms_0 fequcoms_2 fequcoms_1 equcomi eequcoms_0 syl $.
$}
$( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 12-Nov-2017.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequequ1_0 $f set x $.
	fequequ1_1 $f set y $.
	fequequ1_2 $f set z $.
	equequ1 $p |- ( x = y -> ( x = z <-> y = z ) ) $= fequequ1_0 sup_set_class fequequ1_1 sup_set_class wceq fequequ1_0 sup_set_class fequequ1_2 sup_set_class wceq fequequ1_1 sup_set_class fequequ1_2 sup_set_class wceq fequequ1_0 fequequ1_1 fequequ1_2 ax-8 fequequ1_1 sup_set_class fequequ1_2 sup_set_class wceq fequequ1_0 sup_set_class fequequ1_2 sup_set_class wceq wi fequequ1_1 fequequ1_0 fequequ1_1 fequequ1_0 fequequ1_2 ax-8 equcoms impbid $.
$}
$( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequequ1OLD_0 $f set x $.
	fequequ1OLD_1 $f set y $.
	fequequ1OLD_2 $f set z $.
	equequ1OLD $p |- ( x = y -> ( x = z <-> y = z ) ) $= fequequ1OLD_0 sup_set_class fequequ1OLD_1 sup_set_class wceq fequequ1OLD_0 sup_set_class fequequ1OLD_2 sup_set_class wceq fequequ1OLD_1 sup_set_class fequequ1OLD_2 sup_set_class wceq fequequ1OLD_0 fequequ1OLD_1 fequequ1OLD_2 ax-8 fequequ1OLD_0 sup_set_class fequequ1OLD_1 sup_set_class wceq fequequ1OLD_1 sup_set_class fequequ1OLD_0 sup_set_class wceq fequequ1OLD_1 sup_set_class fequequ1OLD_2 sup_set_class wceq fequequ1OLD_0 sup_set_class fequequ1OLD_2 sup_set_class wceq wi fequequ1OLD_0 fequequ1OLD_1 equcomi fequequ1OLD_1 fequequ1OLD_0 fequequ1OLD_2 ax-8 syl impbid $.
$}
$( An equivalence law for equality.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Wolf Lammen, 4-Aug-2017.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequequ2_0 $f set x $.
	fequequ2_1 $f set y $.
	fequequ2_2 $f set z $.
	equequ2 $p |- ( x = y -> ( z = x <-> z = y ) ) $= fequequ2_0 sup_set_class fequequ2_1 sup_set_class wceq fequequ2_0 sup_set_class fequequ2_2 sup_set_class wceq fequequ2_1 sup_set_class fequequ2_2 sup_set_class wceq fequequ2_2 sup_set_class fequequ2_0 sup_set_class wceq fequequ2_2 sup_set_class fequequ2_1 sup_set_class wceq fequequ2_0 fequequ2_1 fequequ2_2 equequ1 fequequ2_0 fequequ2_2 equcom fequequ2_1 fequequ2_2 equcom 3bitr3g $.
$}
$( One of the two equality axioms of standard predicate calculus, called
     reflexivity of equality.  (The other one is ~ stdpc7 .)  Axiom 6 of
     [Mendelson] p. 95.  Mendelson doesn't say why he prepended the redundant
     quantifier, but it was probably to be compatible with free logic (which is
     valid in the empty domain).  (Contributed by NM, 16-Feb-2005.) $)
${
	$v x $.
	fstdpc6_0 $f set x $.
	stdpc6 $p |- A. x x = x $= fstdpc6_0 sup_set_class fstdpc6_0 sup_set_class wceq fstdpc6_0 fstdpc6_0 equid ax-gen $.
$}
$( A transitive law for equality.  (Contributed by NM, 23-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequtr_0 $f set x $.
	fequtr_1 $f set y $.
	fequtr_2 $f set z $.
	equtr $p |- ( x = y -> ( y = z -> x = z ) ) $= fequtr_1 sup_set_class fequtr_2 sup_set_class wceq fequtr_0 sup_set_class fequtr_2 sup_set_class wceq wi fequtr_1 fequtr_0 fequtr_1 fequtr_0 fequtr_2 ax-8 equcoms $.
$}
$( A transitive law for equality.  Lemma L17 in [Megill] p. 446 (p. 14 of the
     preprint).  (Contributed by NM, 23-Aug-1993.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequtrr_0 $f set x $.
	fequtrr_1 $f set y $.
	fequtrr_2 $f set z $.
	equtrr $p |- ( x = y -> ( z = x -> z = y ) ) $= fequtrr_2 sup_set_class fequtrr_0 sup_set_class wceq fequtrr_0 sup_set_class fequtrr_1 sup_set_class wceq fequtrr_2 sup_set_class fequtrr_1 sup_set_class wceq fequtrr_2 fequtrr_0 fequtrr_1 equtr com12 $.
$}
$( A transitive law for equality.  (Contributed by NM, 12-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fequtr2_0 $f set x $.
	fequtr2_1 $f set y $.
	fequtr2_2 $f set z $.
	equtr2 $p |- ( ( x = z /\ y = z ) -> x = y ) $= fequtr2_1 sup_set_class fequtr2_2 sup_set_class wceq fequtr2_0 sup_set_class fequtr2_2 sup_set_class wceq fequtr2_0 sup_set_class fequtr2_1 sup_set_class wceq fequtr2_0 sup_set_class fequtr2_2 sup_set_class wceq fequtr2_0 sup_set_class fequtr2_1 sup_set_class wceq wi fequtr2_2 fequtr2_1 fequtr2_2 fequtr2_1 fequtr2_0 equtrr equcoms impcom $.
$}
$( Two equivalent ways of expressing ~ ax-12 .  See the comment for
     ~ ax-12 .  (Contributed by NM, 2-May-2017.)  (Proof shortened by Wolf
     Lammen, 12-Aug-2017.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fax12b_0 $f set x $.
	fax12b_1 $f set y $.
	fax12b_2 $f set z $.
	ax12b $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) ) <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $= fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi id a1dd fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_1 sup_set_class wceq fax12b_0 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wi fax12b_2 fax12b_1 fax12b_2 fax12b_1 fax12b_0 equtrr equcoms con3rr3 fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal fax12b_0 sup_set_class fax12b_1 sup_set_class wceq wn fax12b_0 sup_set_class fax12b_2 sup_set_class wceq wn fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_1 sup_set_class fax12b_2 sup_set_class wceq fax12b_0 wal wi wi wi id com4l com23 mpdd com3r impbii $.
$}
$( Obsolete version of ~ ax12b as of 12-Aug-2017.  (Contributed by NM,
     2-May-2017.)  (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	fax12bOLD_0 $f set x $.
	fax12bOLD_1 $f set y $.
	fax12bOLD_2 $f set z $.
	ax12bOLD $p |- ( ( -. x = y -> ( y = z -> A. x y = z ) ) <-> ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ) $= fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal bi2.04 fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wi fax12bOLD_2 fax12bOLD_1 fax12bOLD_2 fax12bOLD_1 fax12bOLD_0 equtrr equcoms con3d pm4.71d imbi1d pm5.74i bitri fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn wa fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal bi2.04 bitri fax12bOLD_0 sup_set_class fax12bOLD_1 sup_set_class wceq wn fax12bOLD_0 sup_set_class fax12bOLD_2 sup_set_class wceq wn fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_1 sup_set_class fax12bOLD_2 sup_set_class wceq fax12bOLD_0 wal wi impexp bitri $.
$}
$( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Lemma 9
       of [KalishMontague] p. 87.  This may be the best we can do with minimal
       distinct variable conditions.  TO DO:  Do we need this theorem?  If not,
       maybe it should be deleted.  (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	fspfw_0 $f wff ph $.
	fspfw_1 $f wff ps $.
	fspfw_2 $f set x $.
	fspfw_3 $f set y $.
	espfw_0 $e |- ( -. ps -> A. x -. ps ) $.
	espfw_1 $e |- ( A. x ph -> A. y A. x ph ) $.
	espfw_2 $e |- ( -. ph -> A. y -. ph ) $.
	espfw_3 $e |- ( x = y -> ( ph <-> ps ) ) $.
	spfw $p |- ( A. x ph -> ph ) $= fspfw_0 fspfw_2 wal fspfw_1 wi fspfw_0 fspfw_2 wal fspfw_0 wi fspfw_3 fspfw_0 fspfw_2 wal fspfw_0 fspfw_2 wal fspfw_3 wal fspfw_0 fspfw_2 wal fspfw_1 wi fspfw_3 wal fspfw_1 fspfw_3 wal fspfw_0 espfw_1 fspfw_0 fspfw_2 wal fspfw_1 fspfw_3 ax-5 fspfw_1 fspfw_0 fspfw_3 fspfw_2 espfw_2 fspfw_1 fspfw_0 wi fspfw_2 fspfw_3 fspfw_2 sup_set_class fspfw_3 sup_set_class wceq fspfw_0 fspfw_1 espfw_3 biimprd equcoms spimw syl56 fspfw_0 fspfw_1 fspfw_2 fspfw_3 espfw_0 fspfw_2 sup_set_class fspfw_3 sup_set_class wceq fspfw_0 fspfw_1 espfw_3 biimpd spimw mpg $.
$}
$( Weak version of ~ sp .  Uses only Tarski's FOL axiom schemes.  Obsolete
       version of ~ spnfw as of 13-Aug-2017.  (Contributed by NM, 1-Aug-2017.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	ispnfwOLD_0 $f set y $.
	fspnfwOLD_0 $f wff ph $.
	fspnfwOLD_1 $f set x $.
	espnfwOLD_0 $e |- ( -. ph -> A. x -. ph ) $.
	spnfwOLD $p |- ( A. x ph -> ph ) $= fspnfwOLD_0 fspnfwOLD_0 fspnfwOLD_1 ispnfwOLD_0 espnfwOLD_0 fspnfwOLD_0 fspnfwOLD_1 wal ispnfwOLD_0 ax-17 fspnfwOLD_0 wn ispnfwOLD_0 ax-17 fspnfwOLD_1 sup_set_class ispnfwOLD_0 sup_set_class wceq fspnfwOLD_0 biidd spfw $.
$}
$( Weak version of ~ 19.8a .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 1-Aug-2017.) $)
${
	$v ph $.
	$v x $.
	f19.8w_0 $f wff ph $.
	f19.8w_1 $f set x $.
	e19.8w_0 $e |- ( ph -> A. x ph ) $.
	19.8w $p |- ( ph -> E. x ph ) $= f19.8w_0 f19.8w_0 wn f19.8w_1 wal wn f19.8w_0 f19.8w_1 wex f19.8w_0 wn f19.8w_1 wal f19.8w_0 f19.8w_0 wn f19.8w_1 f19.8w_0 f19.8w_0 f19.8w_1 wal f19.8w_0 wn wn f19.8w_0 wn wn f19.8w_1 wal e19.8w_0 f19.8w_0 notnot f19.8w_0 f19.8w_0 wn wn f19.8w_1 f19.8w_0 notnot albii 3imtr3i spnfw con2i f19.8w_0 f19.8w_1 df-ex sylibr $.
$}
$( Weak version of specialization scheme ~ sp .  Lemma 9 of
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
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ps $.
	$d y ph $.
	fspw_0 $f wff ph $.
	fspw_1 $f wff ps $.
	fspw_2 $f set x $.
	fspw_3 $f set y $.
	espw_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	spw $p |- ( A. x ph -> ph ) $= fspw_0 fspw_2 wal fspw_1 wi fspw_0 fspw_2 wal fspw_0 wi fspw_3 fspw_0 fspw_2 wal fspw_0 fspw_2 wal fspw_3 wal fspw_0 fspw_2 wal fspw_1 wi fspw_3 wal fspw_1 fspw_3 wal fspw_0 fspw_0 fspw_2 wal fspw_3 ax-17 fspw_0 fspw_2 wal fspw_1 fspw_3 ax-5 fspw_1 fspw_0 fspw_3 fspw_2 fspw_1 fspw_0 wi fspw_2 fspw_3 fspw_2 sup_set_class fspw_3 sup_set_class wceq fspw_0 fspw_1 espw_0 biimprd equcoms spimvw syl56 fspw_0 fspw_1 fspw_2 fspw_3 fspw_2 sup_set_class fspw_3 sup_set_class wceq fspw_0 fspw_1 espw_0 biimpd spimvw mpg $.
$}
$( Version of ~ sp when ` x ` does not occur in ` ph ` .  This provides the
       other direction of ~ ax-17 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y ph $.
	ispvw_0 $f set y $.
	fspvw_0 $f wff ph $.
	fspvw_1 $f set x $.
	spvw $p |- ( A. x ph -> ph ) $= fspvw_0 fspvw_0 fspvw_1 ispvw_0 fspvw_1 sup_set_class ispvw_0 sup_set_class wceq fspvw_0 biidd spw $.
$}
$( Special case of Theorem 19.3 of [Margaris] p. 89.  (Contributed by NM,
       1-Aug-2017.) $)
${
	$v ph $.
	$v x $.
	$d x ph $.
	f19.3v_0 $f wff ph $.
	f19.3v_1 $f set x $.
	19.3v $p |- ( A. x ph <-> ph ) $= f19.3v_0 f19.3v_1 wal f19.3v_0 f19.3v_0 f19.3v_1 spvw f19.3v_0 f19.3v_1 ax-17 impbii $.
$}
$( Special case of Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM,
       28-May-1995.)  (Revised by NM, 1-Aug-2017.) $)
${
	$v ph $.
	$v x $.
	$d x ph $.
	f19.9v_0 $f wff ph $.
	f19.9v_1 $f set x $.
	19.9v $p |- ( E. x ph <-> ph ) $= f19.9v_0 f19.9v_1 wex f19.9v_0 wn f19.9v_1 wal wn f19.9v_0 f19.9v_0 f19.9v_1 df-ex f19.9v_0 wn f19.9v_1 wal f19.9v_0 f19.9v_0 wn f19.9v_1 19.3v con2bii bitr4i $.
$}
$( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       27-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$d x ch $.
	$d x ph $.
	fexlimdv_0 $f wff ph $.
	fexlimdv_1 $f wff ps $.
	fexlimdv_2 $f wff ch $.
	fexlimdv_3 $f set x $.
	eexlimdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	exlimdv $p |- ( ph -> ( E. x ps -> ch ) ) $= fexlimdv_0 fexlimdv_1 fexlimdv_3 wex fexlimdv_2 fexlimdv_3 wex fexlimdv_2 fexlimdv_0 fexlimdv_1 fexlimdv_2 fexlimdv_3 eexlimdv_0 eximdv fexlimdv_2 fexlimdv_3 19.9v syl6ib $.
$}
$( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 15-Jun-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$d x ch $.
	$d x ph $.
	fexlimddv_0 $f wff ph $.
	fexlimddv_1 $f wff ps $.
	fexlimddv_2 $f wff ch $.
	fexlimddv_3 $f set x $.
	eexlimddv_0 $e |- ( ph -> E. x ps ) $.
	eexlimddv_1 $e |- ( ( ph /\ ps ) -> ch ) $.
	exlimddv $p |- ( ph -> ch ) $= fexlimddv_0 fexlimddv_1 fexlimddv_3 wex fexlimddv_2 eexlimddv_0 fexlimddv_0 fexlimddv_1 fexlimddv_2 fexlimddv_3 fexlimddv_0 fexlimddv_1 fexlimddv_2 eexlimddv_1 ex exlimdv mpd $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.

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
	$v ph $.
	$v ps $.
	$v x $.
	$d x ps $.
	fexlimiv_0 $f wff ph $.
	fexlimiv_1 $f wff ps $.
	fexlimiv_2 $f set x $.
	eexlimiv_0 $e |- ( ph -> ps ) $.
	exlimiv $p |- ( E. x ph -> ps ) $= fexlimiv_0 fexlimiv_2 wex fexlimiv_1 fexlimiv_2 wex fexlimiv_1 fexlimiv_0 fexlimiv_1 fexlimiv_2 eexlimiv_0 eximi fexlimiv_1 fexlimiv_2 19.9v sylib $.
$}
$( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       1-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x ps $.
	$d y ps $.
	fexlimivv_0 $f wff ph $.
	fexlimivv_1 $f wff ps $.
	fexlimivv_2 $f set x $.
	fexlimivv_3 $f set y $.
	eexlimivv_0 $e |- ( ph -> ps ) $.
	exlimivv $p |- ( E. x E. y ph -> ps ) $= fexlimivv_0 fexlimivv_3 wex fexlimivv_1 fexlimivv_2 fexlimivv_0 fexlimivv_1 fexlimivv_3 eexlimivv_0 exlimiv exlimiv $.
$}
$( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       31-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v y $.
	$d x ch $.
	$d x ph $.
	$d y ch $.
	$d y ph $.
	fexlimdvv_0 $f wff ph $.
	fexlimdvv_1 $f wff ps $.
	fexlimdvv_2 $f wff ch $.
	fexlimdvv_3 $f set x $.
	fexlimdvv_4 $f set y $.
	eexlimdvv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	exlimdvv $p |- ( ph -> ( E. x E. y ps -> ch ) ) $= fexlimdvv_0 fexlimdvv_1 fexlimdvv_4 wex fexlimdvv_2 fexlimdvv_3 fexlimdvv_0 fexlimdvv_1 fexlimdvv_2 fexlimdvv_4 eexlimdvv_0 exlimdv exlimdv $.
$}
$( Version of ~ sp when ` ph ` is true.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)
${
	$v ph $.
	$v x $.
	fsptruw_0 $f wff ph $.
	fsptruw_1 $f set x $.
	esptruw_0 $e |- ph $.
	sptruw $p |- ( A. x ph -> ph ) $= fsptruw_0 fsptruw_0 fsptruw_1 wal esptruw_0 a1i $.
$}
$( Version of ~ sp when ` ph ` is false.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 23-Apr-1017.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	$d y ph $.
	ispfalw_0 $f set y $.
	fspfalw_0 $f wff ph $.
	fspfalw_1 $f set x $.
	espfalw_0 $e |- -. ph $.
	spfalw $p |- ( A. x ph -> ph ) $= fspfalw_0 wfal fspfalw_1 ispfalw_0 fspfalw_0 wfal wb fspfalw_1 sup_set_class ispfalw_0 sup_set_class wceq fspfalw_0 espfalw_0 bifal a1i spw $.
$}
$( Theorem 19.2 of [Margaris] p. 89.  Note:  This proof is very different
     from Margaris' because we only have Tarski's FOL axiom schemes available
     at this point.  See the later ~ 19.2g for a more conventional proof.
     (Contributed by NM, 2-Aug-2017.) $)
${
	$v ph $.
	$v x $.
	f19.2_0 $f wff ph $.
	f19.2_1 $f set x $.
	19.2 $p |- ( A. x ph -> E. x ph ) $= f19.2_1 sup_set_class f19.2_1 sup_set_class wceq wn f19.2_1 wal wn f19.2_0 f19.2_1 wal f19.2_0 f19.2_1 wex wi f19.2_1 sup_set_class f19.2_1 sup_set_class wceq wn f19.2_1 wal f19.2_1 sup_set_class f19.2_1 sup_set_class wceq f19.2_1 equid f19.2_1 sup_set_class f19.2_1 sup_set_class wceq wn f19.2_1 f19.2_1 sup_set_class f19.2_1 sup_set_class wceq f19.2_1 equid notnoti spfalw mt2 f19.2_0 f19.2_0 f19.2_1 f19.2_1 f19.2_1 sup_set_class f19.2_1 sup_set_class wceq f19.2_0 idd speimfw ax-mp $.
$}
$( Theorem 19.39 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.39_0 $f wff ph $.
	f19.39_1 $f wff ps $.
	f19.39_2 $f set x $.
	19.39 $p |- ( ( E. x ph -> E. x ps ) -> E. x ( ph -> ps ) ) $= f19.39_0 f19.39_2 wex f19.39_1 f19.39_2 wex wi f19.39_0 f19.39_2 wal f19.39_1 f19.39_2 wex wi f19.39_0 f19.39_1 wi f19.39_2 wex f19.39_0 f19.39_2 wal f19.39_0 f19.39_2 wex f19.39_1 f19.39_2 wex f19.39_0 f19.39_2 19.2 imim1i f19.39_0 f19.39_1 f19.39_2 19.35 sylibr $.
$}
$( Theorem 19.24 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.24_0 $f wff ph $.
	f19.24_1 $f wff ps $.
	f19.24_2 $f set x $.
	19.24 $p |- ( ( A. x ph -> A. x ps ) -> E. x ( ph -> ps ) ) $= f19.24_0 f19.24_2 wal f19.24_1 f19.24_2 wal wi f19.24_0 f19.24_2 wal f19.24_1 f19.24_2 wex wi f19.24_0 f19.24_1 wi f19.24_2 wex f19.24_1 f19.24_2 wal f19.24_1 f19.24_2 wex f19.24_0 f19.24_2 wal f19.24_1 f19.24_2 19.2 imim2i f19.24_0 f19.24_1 f19.24_2 19.35 sylibr $.
$}
$( Theorem 19.34 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	f19.34_0 $f wff ph $.
	f19.34_1 $f wff ps $.
	f19.34_2 $f set x $.
	19.34 $p |- ( ( A. x ph \/ E. x ps ) -> E. x ( ph \/ ps ) ) $= f19.34_0 f19.34_2 wal f19.34_1 f19.34_2 wex wo f19.34_0 f19.34_2 wex f19.34_1 f19.34_2 wex wo f19.34_0 f19.34_1 wo f19.34_2 wex f19.34_0 f19.34_2 wal f19.34_0 f19.34_2 wex f19.34_1 f19.34_2 wex f19.34_0 f19.34_2 19.2 orim1i f19.34_0 f19.34_1 f19.34_2 19.43 sylibr $.
$}
$( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	fcbvalw_0 $f wff ph $.
	fcbvalw_1 $f wff ps $.
	fcbvalw_2 $f set x $.
	fcbvalw_3 $f set y $.
	ecbvalw_0 $e |- ( A. x ph -> A. y A. x ph ) $.
	ecbvalw_1 $e |- ( -. ps -> A. x -. ps ) $.
	ecbvalw_2 $e |- ( A. y ps -> A. x A. y ps ) $.
	ecbvalw_3 $e |- ( -. ph -> A. y -. ph ) $.
	ecbvalw_4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvalw $p |- ( A. x ph <-> A. y ps ) $= fcbvalw_0 fcbvalw_2 wal fcbvalw_1 fcbvalw_3 wal fcbvalw_0 fcbvalw_1 fcbvalw_2 fcbvalw_3 ecbvalw_0 ecbvalw_1 fcbvalw_2 sup_set_class fcbvalw_3 sup_set_class wceq fcbvalw_0 fcbvalw_1 ecbvalw_4 biimpd cbvaliw fcbvalw_1 fcbvalw_0 fcbvalw_3 fcbvalw_2 ecbvalw_2 ecbvalw_3 fcbvalw_1 fcbvalw_0 wi fcbvalw_2 fcbvalw_3 fcbvalw_2 sup_set_class fcbvalw_3 sup_set_class wceq fcbvalw_0 fcbvalw_1 ecbvalw_4 biimprd equcoms cbvaliw impbii $.
$}
$( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ps $.
	$d y ph $.
	fcbvalvw_0 $f wff ph $.
	fcbvalvw_1 $f wff ps $.
	fcbvalvw_2 $f set x $.
	fcbvalvw_3 $f set y $.
	ecbvalvw_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvalvw $p |- ( A. x ph <-> A. y ps ) $= fcbvalvw_0 fcbvalvw_2 wal fcbvalvw_1 fcbvalvw_3 wal fcbvalvw_0 fcbvalvw_1 fcbvalvw_2 fcbvalvw_3 fcbvalvw_2 sup_set_class fcbvalvw_3 sup_set_class wceq fcbvalvw_0 fcbvalvw_1 ecbvalvw_0 biimpd cbvalivw fcbvalvw_1 fcbvalvw_0 fcbvalvw_3 fcbvalvw_2 fcbvalvw_1 fcbvalvw_0 wi fcbvalvw_2 fcbvalvw_3 fcbvalvw_2 sup_set_class fcbvalvw_3 sup_set_class wceq fcbvalvw_0 fcbvalvw_1 ecbvalvw_0 biimprd equcoms cbvalivw impbii $.
$}
$( Change bound variable.  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d x ps $.
	$d y ph $.
	fcbvexvw_0 $f wff ph $.
	fcbvexvw_1 $f wff ps $.
	fcbvexvw_2 $f set x $.
	fcbvexvw_3 $f set y $.
	ecbvexvw_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvexvw $p |- ( E. x ph <-> E. y ps ) $= fcbvexvw_0 wn fcbvexvw_2 wal wn fcbvexvw_1 wn fcbvexvw_3 wal wn fcbvexvw_0 fcbvexvw_2 wex fcbvexvw_1 fcbvexvw_3 wex fcbvexvw_0 wn fcbvexvw_2 wal fcbvexvw_1 wn fcbvexvw_3 wal fcbvexvw_0 wn fcbvexvw_1 wn fcbvexvw_2 fcbvexvw_3 fcbvexvw_2 sup_set_class fcbvexvw_3 sup_set_class wceq fcbvexvw_0 fcbvexvw_1 ecbvexvw_0 notbid cbvalvw notbii fcbvexvw_0 fcbvexvw_2 df-ex fcbvexvw_1 fcbvexvw_3 df-ex 3bitr4i $.
$}
$( Weak version of ~ alcom .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 10-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d y z $.
	$d x y $.
	$d z ph $.
	$d y ps $.
	falcomiw_0 $f wff ph $.
	falcomiw_1 $f wff ps $.
	falcomiw_2 $f set x $.
	falcomiw_3 $f set y $.
	falcomiw_4 $f set z $.
	ealcomiw_0 $e |- ( y = z -> ( ph <-> ps ) ) $.
	alcomiw $p |- ( A. x A. y ph -> A. y A. x ph ) $= falcomiw_0 falcomiw_3 wal falcomiw_2 wal falcomiw_1 falcomiw_4 wal falcomiw_2 wal falcomiw_1 falcomiw_4 wal falcomiw_2 wal falcomiw_3 wal falcomiw_0 falcomiw_2 wal falcomiw_3 wal falcomiw_0 falcomiw_3 wal falcomiw_1 falcomiw_4 wal falcomiw_2 falcomiw_0 falcomiw_1 falcomiw_3 falcomiw_4 falcomiw_3 sup_set_class falcomiw_4 sup_set_class wceq falcomiw_0 falcomiw_1 ealcomiw_0 biimpd cbvalivw alimi falcomiw_1 falcomiw_4 wal falcomiw_2 wal falcomiw_3 ax-17 falcomiw_1 falcomiw_4 wal falcomiw_2 wal falcomiw_0 falcomiw_2 wal falcomiw_3 falcomiw_1 falcomiw_4 wal falcomiw_0 falcomiw_2 falcomiw_1 falcomiw_0 falcomiw_4 falcomiw_3 falcomiw_1 falcomiw_0 wi falcomiw_3 falcomiw_4 falcomiw_3 sup_set_class falcomiw_4 sup_set_class wceq falcomiw_0 falcomiw_1 ealcomiw_0 biimprd equcoms spimvw alimi alimi 3syl $.
$}
$( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	fhbn1fw_0 $f wff ph $.
	fhbn1fw_1 $f wff ps $.
	fhbn1fw_2 $f set x $.
	fhbn1fw_3 $f set y $.
	ehbn1fw_0 $e |- ( A. x ph -> A. y A. x ph ) $.
	ehbn1fw_1 $e |- ( -. ps -> A. x -. ps ) $.
	ehbn1fw_2 $e |- ( A. y ps -> A. x A. y ps ) $.
	ehbn1fw_3 $e |- ( -. ph -> A. y -. ph ) $.
	ehbn1fw_4 $e |- ( -. A. y ps -> A. x -. A. y ps ) $.
	ehbn1fw_5 $e |- ( x = y -> ( ph <-> ps ) ) $.
	hbn1fw $p |- ( -. A. x ph -> A. x -. A. x ph ) $= fhbn1fw_0 fhbn1fw_2 wal wn fhbn1fw_1 fhbn1fw_3 wal wn fhbn1fw_1 fhbn1fw_3 wal wn fhbn1fw_2 wal fhbn1fw_0 fhbn1fw_2 wal wn fhbn1fw_2 wal fhbn1fw_1 fhbn1fw_3 wal fhbn1fw_0 fhbn1fw_2 wal fhbn1fw_0 fhbn1fw_2 wal fhbn1fw_1 fhbn1fw_3 wal fhbn1fw_0 fhbn1fw_1 fhbn1fw_2 fhbn1fw_3 ehbn1fw_0 ehbn1fw_1 ehbn1fw_2 ehbn1fw_3 ehbn1fw_5 cbvalw biimpri con3i ehbn1fw_4 fhbn1fw_1 fhbn1fw_3 wal wn fhbn1fw_0 fhbn1fw_2 wal wn fhbn1fw_2 fhbn1fw_0 fhbn1fw_2 wal fhbn1fw_1 fhbn1fw_3 wal fhbn1fw_0 fhbn1fw_2 wal fhbn1fw_1 fhbn1fw_3 wal fhbn1fw_0 fhbn1fw_1 fhbn1fw_2 fhbn1fw_3 ehbn1fw_0 ehbn1fw_1 ehbn1fw_2 ehbn1fw_3 ehbn1fw_5 cbvalw biimpi con3i alimi 3syl $.
$}
$( Weak version of ~ hbn1 .  Uses only Tarski's FOL axiom schemes.
       (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d y ph $.
	$d x ps $.
	$d x y $.
	fhbn1w_0 $f wff ph $.
	fhbn1w_1 $f wff ps $.
	fhbn1w_2 $f set x $.
	fhbn1w_3 $f set y $.
	ehbn1w_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	hbn1w $p |- ( -. A. x ph -> A. x -. A. x ph ) $= fhbn1w_0 fhbn1w_1 fhbn1w_2 fhbn1w_3 fhbn1w_0 fhbn1w_2 wal fhbn1w_3 ax-17 fhbn1w_1 wn fhbn1w_2 ax-17 fhbn1w_1 fhbn1w_3 wal fhbn1w_2 ax-17 fhbn1w_0 wn fhbn1w_3 ax-17 fhbn1w_1 fhbn1w_3 wal wn fhbn1w_2 ax-17 ehbn1w_0 hbn1fw $.
$}
$( Weak version of ~ hba1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 9-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d y ph $.
	$d x ps $.
	$d x y $.
	fhba1w_0 $f wff ph $.
	fhba1w_1 $f wff ps $.
	fhba1w_2 $f set x $.
	fhba1w_3 $f set y $.
	ehba1w_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	hba1w $p |- ( A. x ph -> A. x A. x ph ) $= fhba1w_0 fhba1w_2 wal fhba1w_0 fhba1w_2 wal wn fhba1w_2 wal wn fhba1w_0 fhba1w_2 wal wn fhba1w_2 wal wn fhba1w_2 wal fhba1w_0 fhba1w_2 wal fhba1w_2 wal fhba1w_0 fhba1w_2 wal wn fhba1w_2 wal fhba1w_0 fhba1w_2 wal fhba1w_0 fhba1w_2 wal wn fhba1w_1 fhba1w_3 wal wn fhba1w_2 fhba1w_3 fhba1w_2 sup_set_class fhba1w_3 sup_set_class wceq fhba1w_0 fhba1w_2 wal fhba1w_1 fhba1w_3 wal fhba1w_0 fhba1w_2 wal fhba1w_1 fhba1w_3 wal wb fhba1w_2 sup_set_class fhba1w_3 sup_set_class wceq fhba1w_0 fhba1w_1 fhba1w_2 fhba1w_3 ehba1w_0 cbvalvw a1i notbid spw con2i fhba1w_0 fhba1w_2 wal wn fhba1w_1 fhba1w_3 wal wn fhba1w_2 fhba1w_3 fhba1w_2 sup_set_class fhba1w_3 sup_set_class wceq fhba1w_0 fhba1w_2 wal fhba1w_1 fhba1w_3 wal fhba1w_0 fhba1w_2 wal fhba1w_1 fhba1w_3 wal wb fhba1w_2 sup_set_class fhba1w_3 sup_set_class wceq fhba1w_0 fhba1w_1 fhba1w_2 fhba1w_3 ehba1w_0 cbvalvw a1i notbid hbn1w fhba1w_0 fhba1w_2 wal wn fhba1w_2 wal wn fhba1w_0 fhba1w_2 wal fhba1w_2 fhba1w_0 fhba1w_2 wal fhba1w_0 fhba1w_2 wal wn fhba1w_2 wal fhba1w_0 fhba1w_1 fhba1w_2 fhba1w_3 ehba1w_0 hbn1w con1i alimi 3syl $.
$}
$( Weak version of ~ hbe1 .  See comments for ~ ax6w .  Uses only Tarski's
       FOL axiom schemes.  (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d y ph $.
	$d x ps $.
	$d x y $.
	fhbe1w_0 $f wff ph $.
	fhbe1w_1 $f wff ps $.
	fhbe1w_2 $f set x $.
	fhbe1w_3 $f set y $.
	ehbe1w_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	hbe1w $p |- ( E. x ph -> A. x E. x ph ) $= fhbe1w_0 fhbe1w_2 wex fhbe1w_0 wn fhbe1w_2 wal wn fhbe1w_2 fhbe1w_0 fhbe1w_2 df-ex fhbe1w_0 wn fhbe1w_1 wn fhbe1w_2 fhbe1w_3 fhbe1w_2 sup_set_class fhbe1w_3 sup_set_class wceq fhbe1w_0 fhbe1w_1 ehbe1w_0 notbid hbn1w hbxfrbi $.
$}
$( Weak version of ~ hbal .  Uses only Tarski's FOL axiom schemes.  Unlike
       ~ hbal , this theorem requires that ` x ` and ` y ` be distinct i.e. are
       not bundled.  (Contributed by NM, 19-Apr-2017.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d x y $.
	$d z ph $.
	$d x ps $.
	fhbalw_0 $f wff ph $.
	fhbalw_1 $f wff ps $.
	fhbalw_2 $f set x $.
	fhbalw_3 $f set y $.
	fhbalw_4 $f set z $.
	ehbalw_0 $e |- ( x = z -> ( ph <-> ps ) ) $.
	ehbalw_1 $e |- ( ph -> A. x ph ) $.
	hbalw $p |- ( A. y ph -> A. x A. y ph ) $= fhbalw_0 fhbalw_3 wal fhbalw_0 fhbalw_2 wal fhbalw_3 wal fhbalw_0 fhbalw_3 wal fhbalw_2 wal fhbalw_0 fhbalw_0 fhbalw_2 wal fhbalw_3 ehbalw_1 alimi fhbalw_0 fhbalw_1 fhbalw_3 fhbalw_2 fhbalw_4 ehbalw_0 alcomiw syl $.
$}

