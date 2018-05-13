$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Axiom_of_Separation.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Derive the Null Set Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Show the uniqueness of the empty set (using the Axiom of Extensionality
       via ~ bm1.1 to strengthen the hypothesis in the form of ~ axnul ).
       (Contributed by NM, 22-Dec-2007.) $)

${
	$v x y  $.
	$d x y  $.
	f0_zfnuleu $f set x $.
	f1_zfnuleu $f set y $.
	e0_zfnuleu $e |- E. x A. y -. y e. x $.
	p_zfnuleu $p |- E! x A. y -. y e. x $= e0_zfnuleu f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel p_nbfal f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu p_albii f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_wal f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu p_exbii f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_wal f0_zfnuleu a_wex f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu a_wex p_mpbi a_wfal f0_zfnuleu p_nfv a_wfal f0_zfnuleu f1_zfnuleu p_bm1.1 f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu a_wex f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu a_weu a_ax-mp f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel p_nbfal f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu p_albii f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_wal f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu p_eubii f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wn f1_zfnuleu a_wal f0_zfnuleu a_weu f1_zfnuleu a_sup_set_class f0_zfnuleu a_sup_set_class a_wcel a_wfal a_wb f1_zfnuleu a_wal f0_zfnuleu a_weu p_mpbir $.
$}

$(Prove ~ axnul directly from ~ ax-rep using none of the equality axioms
       ~ ax-8 through ~ ax-15 provided we accept ~ sp as an axiom.  Replace
       ~ sp with the obsolete ~ ax-4 to see this in 'show trace_back'.
       (Contributed by Jeff Hoffman, 3-Feb-2008.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v x y  $.
	$d x y z w  $.
	f0_axnulALT $f set x $.
	f1_axnulALT $f set y $.
	i0_axnulALT $f set z $.
	i1_axnulALT $f set w $.
	p_axnulALT $p |- E. x A. y -. y e. x $= a_wfal i0_axnulALT f0_axnulALT f1_axnulALT i1_axnulALT a_ax-rep a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal a_wn f0_axnulALT p_sp a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal a_wn f0_axnulALT a_wal a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal p_con2i a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal f0_axnulALT a_df-ex a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal a_wn f0_axnulALT a_wal a_wn a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal f0_axnulALT a_wex p_sylibr p_fal a_wfal f0_axnulALT p_sp a_wfal f0_axnulALT a_wal a_wfal p_mto a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq p_pm2.21i a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal f0_axnulALT a_wex f1_axnulALT p_mpg a_wfal f0_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wceq a_wi f1_axnulALT a_wal f0_axnulALT a_wex f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT a_wex a_wb f1_axnulALT a_wal f0_axnulALT a_wex i1_axnulALT p_mpg p_fal a_wfal f0_axnulALT p_sp a_wfal f0_axnulALT a_wal a_wfal p_mto a_wfal f0_axnulALT a_wal i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel p_intnan i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT p_nex i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT a_wex f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel p_nbn f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel a_wn f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT a_wex a_wb f1_axnulALT p_albii f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel a_wn f1_axnulALT a_wal f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT a_wex a_wb f1_axnulALT a_wal f0_axnulALT p_exbii f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel a_wn f1_axnulALT a_wal f0_axnulALT a_wex f1_axnulALT a_sup_set_class f0_axnulALT a_sup_set_class a_wcel i1_axnulALT a_sup_set_class i0_axnulALT a_sup_set_class a_wcel a_wfal f0_axnulALT a_wal a_wa i1_axnulALT a_wex a_wb f1_axnulALT a_wal f0_axnulALT a_wex p_mpbir $.
$}

$(The Null Set Axiom of ZF set theory: there exists a set with no
       elements.  Axiom of Empty Set of [Enderton] p. 18.  In some textbooks,
       this is presented as a separate axiom; here we show it can be derived
       from Separation ~ ax-sep .  This version of the Null Set Axiom tells us
       that at least one empty set exists, but does not tell us that it is
       unique - we need the Axiom of Extensionality to do that (see
       ~ zfnuleu ).

       This proof, suggested by Jeff Hoffman, uses only ~ ax-5 and ~ ax-gen
       from predicate calculus, which are valid in "free logic" i.e. logic
       holding in an empty domain (see Axiom A5 and Rule R2 of [LeBlanc]
       p. 277).  Thus, our ~ ax-sep implies the existence of at least one set.
       Note that Kunen's version of ~ ax-sep (Axiom 3 of [Kunen] p. 11) does
       not imply the existence of a set because his is universally closed i.e.
       prefixed with universal quantifiers to eliminate all free variables.
       His existence is provided by a separate axiom stating ` E. x x = x `
       (Axiom 0 of [Kunen] p. 10).

       See ~ axnulALT for a proof directly from ~ ax-rep .

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-nul below so that the uses of the Null Set Axiom can be more easily
       identified.  (Contributed by Jeff Hoffman, 3-Feb-2008.)  (Revised by NM,
       4-Feb-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_axnul $f set x $.
	f1_axnul $f set y $.
	i0_axnul $f set z $.
	p_axnul $p |- E. x A. y -. y e. x $= f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa f1_axnul f0_axnul i0_axnul a_ax-sep f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel p_pm3.24 f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel p_intnan f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa a_wb p_id f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa a_wb f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa p_mtbiri f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa a_wb f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel a_wn f1_axnul p_alimi f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa a_wb f1_axnul a_wal f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel a_wn f1_axnul a_wal f0_axnul p_eximi f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class i0_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel f1_axnul a_sup_set_class f1_axnul a_sup_set_class a_wcel a_wn a_wa a_wa a_wb f1_axnul a_wal f0_axnul a_wex f1_axnul a_sup_set_class f0_axnul a_sup_set_class a_wcel a_wn f1_axnul a_wal f0_axnul a_wex a_ax-mp $.
$}

$(The Null Set Axiom of ZF set theory.  It was derived as ~ axnul above
       and is therefore redundant, but we state it as a separate axiom here so
       that its uses can be identified more easily.  (Contributed by NM,
       7-Aug-2003.) $)

${
	$v x y  $.
	$d x y  $.
	f0_ax-nul $f set x $.
	f1_ax-nul $f set y $.
	a_ax-nul $a |- E. x A. y -. y e. x $.
$}

$(The Null Set Axiom of ZF set theory: the empty set exists.  Corollary
       5.16 of [TakeutiZaring] p. 20.  For the unabbreviated version, see
       ~ ax-nul .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)

${
	$v  $.
	$d x y  $.
	i0_0ex $f set x $.
	i1_0ex $f set y $.
	p_0ex $p |- (/) e. _V $= i0_0ex i1_0ex a_ax-nul i1_0ex i0_0ex a_sup_set_class p_eq0 i0_0ex a_sup_set_class a_c0 a_wceq i1_0ex a_sup_set_class i0_0ex a_sup_set_class a_wcel a_wn i1_0ex a_wal i0_0ex p_exbii i0_0ex a_sup_set_class a_c0 a_wceq i0_0ex a_wex i1_0ex a_sup_set_class i0_0ex a_sup_set_class a_wcel a_wn i1_0ex a_wal i0_0ex a_wex p_mpbir i0_0ex a_c0 p_issetri $.
$}


