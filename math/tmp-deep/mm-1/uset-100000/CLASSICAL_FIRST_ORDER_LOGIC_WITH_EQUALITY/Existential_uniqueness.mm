$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes).mm $]

$(#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(Declare new symbols needed for uniqueness notation. $)

$c E! $.

$(Backwards E exclamation point. $)

$c E* $.

$(Backwards E superscript *. $)

$(Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)

${
	$v ph x  $.
	f0_weu $f wff ph $.
	f1_weu $f set x $.
	a_weu $a wff E! x ph $.
$}

$(Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)

${
	$v ph x  $.
	f0_wmo $f wff ph $.
	f1_wmo $f set x $.
	a_wmo $a wff E* x ph $.
$}

$(A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x y z  $.
	$d w x y  $.
	$d x z  $.
	$d y ph  $.
	$d w z ph  $.
	f0_eujust $f wff ph $.
	f1_eujust $f set x $.
	f2_eujust $f set y $.
	f3_eujust $f set z $.
	i0_eujust $f set w $.
	p_eujust $p |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) ) $= f2_eujust i0_eujust f1_eujust p_equequ2 f2_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq f1_eujust a_sup_set_class f2_eujust a_sup_set_class a_wceq f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq f0_eujust p_bibi2d f2_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq f0_eujust f1_eujust a_sup_set_class f2_eujust a_sup_set_class a_wceq a_wb f0_eujust f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq a_wb f1_eujust p_albidv f0_eujust f1_eujust a_sup_set_class f2_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal f0_eujust f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal f2_eujust i0_eujust p_cbvexv i0_eujust f3_eujust f1_eujust p_equequ2 i0_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq f1_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq f0_eujust p_bibi2d i0_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq f0_eujust f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq a_wb f0_eujust f1_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq a_wb f1_eujust p_albidv f0_eujust f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal f0_eujust f1_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal i0_eujust f3_eujust p_cbvexv f0_eujust f1_eujust a_sup_set_class f2_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal f2_eujust a_wex f0_eujust f1_eujust a_sup_set_class i0_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal i0_eujust a_wex f0_eujust f1_eujust a_sup_set_class f3_eujust a_sup_set_class a_wceq a_wb f1_eujust a_wal f3_eujust a_wex p_bitri $.
$}

$(A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim .  (Contributed by
       NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph x y z  $.
	$d w x y  $.
	$d x z  $.
	$d y ph  $.
	$d w z ph  $.
	f0_eujustALT $f wff ph $.
	f1_eujustALT $f set x $.
	f2_eujustALT $f set y $.
	f3_eujustALT $f set z $.
	i0_eujustALT $f set w $.
	p_eujustALT $p |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) ) $= f2_eujustALT f3_eujustALT f1_eujustALT p_equequ2 f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT p_bibi2d f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT p_albidv f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wb f2_eujustALT p_sps f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f2_eujustALT f3_eujustALT p_drex1 f2_eujustALT f3_eujustALT f2_eujustALT p_hbnae f2_eujustALT f3_eujustALT f3_eujustALT p_hbnae f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f3_eujustALT a_wal f2_eujustALT p_alrimih f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT a_ax-17 i0_eujustALT f2_eujustALT f1_eujustALT p_equequ2 i0_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f0_eujustALT p_bibi2d i0_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT p_albidv i0_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal p_notbid f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT f2_eujustALT i0_eujustALT p_dvelim f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT a_wal a_wi f3_eujustALT f2_eujustALT p_naecoms f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT a_ax-17 i0_eujustALT f3_eujustALT f1_eujustALT p_equequ2 i0_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT p_bibi2d i0_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT p_albidv i0_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal p_notbid f0_eujustALT f1_eujustALT a_sup_set_class i0_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT f3_eujustALT i0_eujustALT p_dvelim f2_eujustALT f3_eujustALT f1_eujustALT p_equequ2 f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT p_bibi2d f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT p_albidv f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal p_notbid f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn a_wb a_wi f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn p_a1i f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT f3_eujustALT p_cbv2h f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f3_eujustALT a_wal f2_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT a_wal a_wb p_syl f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT a_wal p_notbid f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f2_eujustALT a_df-ex f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f3_eujustALT a_df-ex f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f2_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal a_wn f3_eujustALT a_wal a_wn f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f2_eujustALT a_wex f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f3_eujustALT a_wex p_3bitr4g f2_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq f2_eujustALT a_wal f0_eujustALT f1_eujustALT a_sup_set_class f2_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f2_eujustALT a_wex f0_eujustALT f1_eujustALT a_sup_set_class f3_eujustALT a_sup_set_class a_wceq a_wb f1_eujustALT a_wal f3_eujustALT a_wex a_wb p_pm2.61i $.
$}

$(Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d y ph  $.
	f0_df-eu $f wff ph $.
	f1_df-eu $f set x $.
	f2_df-eu $f set y $.
	a_df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
$}

$(Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)

${
	$v ph x  $.
	f0_df-mo $f wff ph $.
	f1_df-mo $f set x $.
	a_df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.
$}

$(A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.) $)

${
	$v ph x y  $.
	$d x y z  $.
	$d ph z  $.
	f0_euf $f wff ph $.
	f1_euf $f set x $.
	f2_euf $f set y $.
	i0_euf $f set z $.
	e0_euf $e |- F/ y ph $.
	p_euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $= f0_euf f1_euf i0_euf a_df-eu e0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq f2_euf p_nfv f0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq f2_euf p_nfbi f0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq a_wb f2_euf f1_euf p_nfal f0_euf i0_euf p_nfv f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq i0_euf p_nfv f0_euf f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq i0_euf p_nfbi f0_euf f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq a_wb i0_euf f1_euf p_nfal i0_euf f2_euf f1_euf p_equequ2 i0_euf a_sup_set_class f2_euf a_sup_set_class a_wceq f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq f0_euf p_bibi2d i0_euf a_sup_set_class f2_euf a_sup_set_class a_wceq f0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq a_wb f0_euf f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq a_wb f1_euf p_albidv f0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq a_wb f1_euf a_wal f0_euf f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq a_wb f1_euf a_wal i0_euf f2_euf p_cbvex f0_euf f1_euf a_weu f0_euf f1_euf a_sup_set_class i0_euf a_sup_set_class a_wceq a_wb f1_euf a_wal i0_euf a_wex f0_euf f1_euf a_sup_set_class f2_euf a_sup_set_class a_wceq a_wb f1_euf a_wal f2_euf a_wex p_bitri $.
$}

$(Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)

${
	$v ph ps ch x  $.
	$d x y  $.
	$d y ph  $.
	$d y ps  $.
	$d y ch  $.
	f0_eubid $f wff ph $.
	f1_eubid $f wff ps $.
	f2_eubid $f wff ch $.
	f3_eubid $f set x $.
	i0_eubid $f set y $.
	e0_eubid $e |- F/ x ph $.
	e1_eubid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $= e0_eubid e1_eubid f0_eubid f1_eubid f2_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq p_bibi1d f0_eubid f1_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f2_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f3_eubid p_albid f0_eubid f1_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f3_eubid a_wal f2_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f3_eubid a_wal i0_eubid p_exbidv f1_eubid f3_eubid i0_eubid a_df-eu f2_eubid f3_eubid i0_eubid a_df-eu f0_eubid f1_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f3_eubid a_wal i0_eubid a_wex f2_eubid f3_eubid a_sup_set_class i0_eubid a_sup_set_class a_wceq a_wb f3_eubid a_wal i0_eubid a_wex f1_eubid f3_eubid a_weu f2_eubid f3_eubid a_weu p_3bitr4g $.
$}

$(Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_eubidv $f wff ph $.
	f1_eubidv $f wff ps $.
	f2_eubidv $f wff ch $.
	f3_eubidv $f set x $.
	e0_eubidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $= f0_eubidv f3_eubidv p_nfv e0_eubidv f0_eubidv f1_eubidv f2_eubidv f3_eubidv p_eubid $.
$}

$(Introduce uniqueness quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)

${
	$v ph ps x  $.
	f0_eubii $f wff ph $.
	f1_eubii $f wff ps $.
	f2_eubii $f set x $.
	e0_eubii $e |- ( ph <-> ps ) $.
	p_eubii $p |- ( E! x ph <-> E! x ps ) $= e0_eubii f0_eubii f1_eubii a_wb a_wtru p_a1i a_wtru f0_eubii f1_eubii f2_eubii p_eubidv f0_eubii f2_eubii a_weu f1_eubii f2_eubii a_weu a_wb p_trud $.
$}

$(Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_nfeu1 $f wff ph $.
	f1_nfeu1 $f set x $.
	i0_nfeu1 $f set y $.
	p_nfeu1 $p |- F/ x E! x ph $= f0_nfeu1 f1_nfeu1 i0_nfeu1 a_df-eu f0_nfeu1 f1_nfeu1 a_sup_set_class i0_nfeu1 a_sup_set_class a_wceq a_wb f1_nfeu1 p_nfa1 f0_nfeu1 f1_nfeu1 a_sup_set_class i0_nfeu1 a_sup_set_class a_wceq a_wb f1_nfeu1 a_wal f1_nfeu1 i0_nfeu1 p_nfex f0_nfeu1 f1_nfeu1 a_weu f0_nfeu1 f1_nfeu1 a_sup_set_class i0_nfeu1 a_sup_set_class a_wceq a_wb f1_nfeu1 a_wal i0_nfeu1 a_wex f1_nfeu1 p_nfxfr $.
$}

$(Bound-variable hypothesis builder for "at most one."  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x  $.
	f0_nfmo1 $f wff ph $.
	f1_nfmo1 $f set x $.
	p_nfmo1 $p |- F/ x E* x ph $= f0_nfmo1 f1_nfmo1 a_df-mo f0_nfmo1 f1_nfmo1 p_nfe1 f0_nfmo1 f1_nfmo1 p_nfeu1 f0_nfmo1 f1_nfmo1 a_wex f0_nfmo1 f1_nfmo1 a_weu f1_nfmo1 p_nfim f0_nfmo1 f1_nfmo1 a_wmo f0_nfmo1 f1_nfmo1 a_wex f0_nfmo1 f1_nfmo1 a_weu a_wi f1_nfmo1 p_nfxfr $.
$}

$(Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)

${
	$v ph ps x y  $.
	$d y z  $.
	$d z ph  $.
	$d z ps  $.
	f0_nfeud2 $f wff ph $.
	f1_nfeud2 $f wff ps $.
	f2_nfeud2 $f set x $.
	f3_nfeud2 $f set y $.
	i0_nfeud2 $f set z $.
	e0_nfeud2 $e |- F/ y ph $.
	e1_nfeud2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	p_nfeud2 $p |- ( ph -> F/ x E! y ps ) $= f1_nfeud2 f3_nfeud2 i0_nfeud2 a_df-eu f0_nfeud2 i0_nfeud2 p_nfv e0_nfeud2 f2_nfeud2 i0_nfeud2 f3_nfeud2 p_nfnae f0_nfeud2 f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f3_nfeud2 p_nfan e1_nfeud2 f0_nfeud2 f2_nfeud2 a_sup_set_class f3_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f1_nfeud2 f2_nfeud2 a_wnf f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn p_adantlr f3_nfeud2 i0_nfeud2 f2_nfeud2 p_nfeqf f2_nfeud2 a_sup_set_class f3_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wnf p_ancoms f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f2_nfeud2 a_sup_set_class f3_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wnf f0_nfeud2 p_adantll f0_nfeud2 f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn a_wa f2_nfeud2 a_sup_set_class f3_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn a_wa f1_nfeud2 f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 p_nfbid f0_nfeud2 f2_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq f2_nfeud2 a_wal a_wn a_wa f1_nfeud2 f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq a_wb f2_nfeud2 f3_nfeud2 p_nfald2 f0_nfeud2 f1_nfeud2 f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq a_wb f3_nfeud2 a_wal f2_nfeud2 i0_nfeud2 p_nfexd2 f1_nfeud2 f3_nfeud2 a_weu f1_nfeud2 f3_nfeud2 a_sup_set_class i0_nfeud2 a_sup_set_class a_wceq a_wb f3_nfeud2 a_wal i0_nfeud2 a_wex f0_nfeud2 f2_nfeud2 p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)

${
	$v ph ps x y  $.
	$d y  $.
	$d ph  $.
	$d ps  $.
	f0_nfmod2 $f wff ph $.
	f1_nfmod2 $f wff ps $.
	f2_nfmod2 $f set x $.
	f3_nfmod2 $f set y $.
	e0_nfmod2 $e |- F/ y ph $.
	e1_nfmod2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	p_nfmod2 $p |- ( ph -> F/ x E* y ps ) $= f1_nfmod2 f3_nfmod2 a_df-mo e0_nfmod2 e1_nfmod2 f0_nfmod2 f1_nfmod2 f2_nfmod2 f3_nfmod2 p_nfexd2 e0_nfmod2 e1_nfmod2 f0_nfmod2 f1_nfmod2 f2_nfmod2 f3_nfmod2 p_nfeud2 f0_nfmod2 f1_nfmod2 f3_nfmod2 a_wex f1_nfmod2 f3_nfmod2 a_weu f2_nfmod2 p_nfimd f1_nfmod2 f3_nfmod2 a_wmo f1_nfmod2 f3_nfmod2 a_wex f1_nfmod2 f3_nfmod2 a_weu a_wi f0_nfmod2 f2_nfmod2 p_nfxfrd $.
$}

$(Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_nfeud $f wff ph $.
	f1_nfeud $f wff ps $.
	f2_nfeud $f set x $.
	f3_nfeud $f set y $.
	e0_nfeud $e |- F/ y ph $.
	e1_nfeud $e |- ( ph -> F/ x ps ) $.
	p_nfeud $p |- ( ph -> F/ x E! y ps ) $= e0_nfeud e1_nfeud f0_nfeud f1_nfeud f2_nfeud a_wnf f2_nfeud a_sup_set_class f3_nfeud a_sup_set_class a_wceq f2_nfeud a_wal a_wn p_adantr f0_nfeud f1_nfeud f2_nfeud f3_nfeud p_nfeud2 $.
$}

$(Bound-variable hypothesis builder for "at most one."  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)

${
	$v ph ps x y  $.
	f0_nfmod $f wff ph $.
	f1_nfmod $f wff ps $.
	f2_nfmod $f set x $.
	f3_nfmod $f set y $.
	e0_nfmod $e |- F/ y ph $.
	e1_nfmod $e |- ( ph -> F/ x ps ) $.
	p_nfmod $p |- ( ph -> F/ x E* y ps ) $= e0_nfmod e1_nfmod f0_nfmod f1_nfmod f2_nfmod a_wnf f2_nfmod a_sup_set_class f3_nfmod a_sup_set_class a_wceq f2_nfmod a_wal a_wn p_adantr f0_nfmod f1_nfmod f2_nfmod f3_nfmod p_nfmod2 $.
$}

$(Bound-variable hypothesis builder for "at most one."  Note that ` x `
       and ` y ` needn't be distinct (this makes the proof more difficult).
       (Contributed by NM, 8-Mar-1995.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph x y  $.
	$d y  $.
	$d x  $.
	$d ph  $.
	f0_nfeu $f wff ph $.
	f1_nfeu $f set x $.
	f2_nfeu $f set y $.
	e0_nfeu $e |- F/ x ph $.
	p_nfeu $p |- F/ x E! y ph $= f2_nfeu p_nftru e0_nfeu f0_nfeu f1_nfeu a_wnf a_wtru p_a1i a_wtru f0_nfeu f1_nfeu f2_nfeu p_nfeud f0_nfeu f2_nfeu a_weu f1_nfeu a_wnf p_trud $.
$}

$(Bound-variable hypothesis builder for "at most one."  (Contributed by
       NM, 9-Mar-1995.) $)

${
	$v ph x y  $.
	$d y  $.
	$d x  $.
	$d ph  $.
	f0_nfmo $f wff ph $.
	f1_nfmo $f set x $.
	f2_nfmo $f set y $.
	e0_nfmo $e |- F/ x ph $.
	p_nfmo $p |- F/ x E* y ph $= f2_nfmo p_nftru e0_nfmo f0_nfmo f1_nfmo a_wnf a_wtru p_a1i a_wtru f0_nfmo f1_nfmo f2_nfmo p_nfmod f0_nfmo f2_nfmo a_wmo f1_nfmo a_wnf p_trud $.
$}

$(Variable substitution in uniqueness quantifier.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x y  $.
	$d w y z  $.
	$d ph z w  $.
	$d w x z  $.
	f0_sb8eu $f wff ph $.
	f1_sb8eu $f set x $.
	f2_sb8eu $f set y $.
	i0_sb8eu $f set z $.
	i1_sb8eu $f set w $.
	e0_sb8eu $e |- F/ y ph $.
	p_sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $= f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb i1_sb8eu p_nfv f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu i1_sb8eu p_sb8 f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f1_sb8eu i1_sb8eu p_sbbi e0_sb8eu f0_sb8eu f1_sb8eu i1_sb8eu f2_sb8eu p_nfsb i1_sb8eu f1_sb8eu i0_sb8eu p_equsb3 i1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f2_sb8eu p_nfv f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f1_sb8eu i1_sb8eu a_wsb i1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f2_sb8eu p_nfxfr f0_sb8eu f1_sb8eu i1_sb8eu a_wsb f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f1_sb8eu i1_sb8eu a_wsb f2_sb8eu p_nfbi f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu i1_sb8eu a_wsb f0_sb8eu f1_sb8eu i1_sb8eu a_wsb f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f1_sb8eu i1_sb8eu a_wsb a_wb f2_sb8eu p_nfxfr f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu f2_sb8eu a_wsb i1_sb8eu p_nfv f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb i1_sb8eu f2_sb8eu f1_sb8eu p_sbequ f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu i1_sb8eu a_wsb f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu f2_sb8eu a_wsb i1_sb8eu f2_sb8eu p_cbval f2_sb8eu f1_sb8eu i0_sb8eu p_equsb3 f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f2_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq f0_sb8eu f1_sb8eu f2_sb8eu p_sblbis f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu f2_sb8eu a_wsb f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f2_sb8eu p_albii f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu a_wal f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu i1_sb8eu a_wsb i1_sb8eu a_wal f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_wal f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f2_sb8eu a_wal p_3bitri f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu a_wal f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f2_sb8eu a_wal i0_sb8eu p_exbii f0_sb8eu f1_sb8eu i0_sb8eu a_df-eu f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu i0_sb8eu a_df-eu f0_sb8eu f1_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f1_sb8eu a_wal i0_sb8eu a_wex f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_sup_set_class i0_sb8eu a_sup_set_class a_wceq a_wb f2_sb8eu a_wal i0_sb8eu a_wex f0_sb8eu f1_sb8eu a_weu f0_sb8eu f1_sb8eu f2_sb8eu a_wsb f2_sb8eu a_weu p_3bitr4i $.
$}

$(Variable substitution in uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)

${
	$v ph x y  $.
	$d y  $.
	$d ph  $.
	$d x  $.
	f0_sb8mo $f wff ph $.
	f1_sb8mo $f set x $.
	f2_sb8mo $f set y $.
	e0_sb8mo $e |- F/ y ph $.
	p_sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $= e0_sb8mo f0_sb8mo f1_sb8mo f2_sb8mo p_sb8e e0_sb8mo f0_sb8mo f1_sb8mo f2_sb8mo p_sb8eu f0_sb8mo f1_sb8mo a_wex f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_wex f0_sb8mo f1_sb8mo a_weu f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_weu p_imbi12i f0_sb8mo f1_sb8mo a_df-mo f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_df-mo f0_sb8mo f1_sb8mo a_wex f0_sb8mo f1_sb8mo a_weu a_wi f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_wex f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_weu a_wi f0_sb8mo f1_sb8mo a_wmo f0_sb8mo f1_sb8mo f2_sb8mo a_wsb f2_sb8mo a_wmo p_3bitr4i $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 25-Nov-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)

${
	$v ph ps x y  $.
	f0_cbveu $f wff ph $.
	f1_cbveu $f wff ps $.
	f2_cbveu $f set x $.
	f3_cbveu $f set y $.
	e0_cbveu $e |- F/ y ph $.
	e1_cbveu $e |- F/ x ps $.
	e2_cbveu $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbveu $p |- ( E! x ph <-> E! y ps ) $= e0_cbveu f0_cbveu f2_cbveu f3_cbveu p_sb8eu e1_cbveu e2_cbveu f0_cbveu f1_cbveu f2_cbveu f3_cbveu p_sbie f0_cbveu f2_cbveu f3_cbveu a_wsb f1_cbveu f3_cbveu p_eubii f0_cbveu f2_cbveu a_weu f0_cbveu f2_cbveu f3_cbveu a_wsb f3_cbveu a_weu f1_cbveu f3_cbveu a_weu p_bitri $.
$}

$(An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_eu1 $f wff ph $.
	f1_eu1 $f set x $.
	f2_eu1 $f set y $.
	e0_eu1 $e |- F/ y ph $.
	p_eu1 $p |- ( E! x ph <-> E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $= f0_eu1 f1_eu1 f2_eu1 p_nfs1v f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 f1_eu1 p_euf e0_eu1 f0_eu1 f1_eu1 f2_eu1 p_sb8eu f1_eu1 f2_eu1 p_equcom f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq f0_eu1 f1_eu1 f2_eu1 a_wsb p_imbi2i f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wi f2_eu1 p_albii e0_eu1 f0_eu1 f1_eu1 f2_eu1 p_sb6rf f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal f0_eu1 f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq f0_eu1 f1_eu1 f2_eu1 a_wsb a_wi f2_eu1 a_wal p_anbi12i f0_eu1 f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal p_ancom f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq f2_eu1 p_albiim f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal f0_eu1 a_wa f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq f0_eu1 f1_eu1 f2_eu1 a_wsb a_wi f2_eu1 a_wal a_wa f0_eu1 f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal a_wa f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wb f2_eu1 a_wal p_3bitr4i f0_eu1 f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal a_wa f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wb f2_eu1 a_wal f1_eu1 p_exbii f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_weu f0_eu1 f1_eu1 f2_eu1 a_wsb f2_eu1 a_sup_set_class f1_eu1 a_sup_set_class a_wceq a_wb f2_eu1 a_wal f1_eu1 a_wex f0_eu1 f1_eu1 a_weu f0_eu1 f0_eu1 f1_eu1 f2_eu1 a_wsb f1_eu1 a_sup_set_class f2_eu1 a_sup_set_class a_wceq a_wi f2_eu1 a_wal a_wa f1_eu1 a_wex p_3bitr4i $.
$}

$(Equivalent definitions of "there exists at most one."  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x y  $.
	$d x y z  $.
	$d ph z  $.
	f0_mo $f wff ph $.
	f1_mo $f set x $.
	f2_mo $f set y $.
	i0_mo $f set z $.
	e0_mo $e |- F/ y ph $.
	p_mo $p |- ( E. y A. x ( ph -> x = y ) <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= e0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfv f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfim f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f2_mo f1_mo p_nfal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal i0_mo p_nfv i0_mo f2_mo f1_mo p_equequ2 i0_mo a_sup_set_class f2_mo a_sup_set_class a_wceq f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq f0_mo p_imbi2d i0_mo a_sup_set_class f2_mo a_sup_set_class a_wceq f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo p_albidv f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal i0_mo f2_mo p_cbvex e0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfv f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfim e0_mo f0_mo f1_mo f2_mo p_nfs1 f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f1_mo p_nfv f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f1_mo p_nfim f0_mo f1_mo f2_mo p_sbequ2 f1_mo f2_mo i0_mo a_ax-8 f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq f0_mo f1_mo f2_mo a_wsb f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq p_imim12d f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo f2_mo p_cbv3 f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f2_mo a_wal p_ancli e0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfv f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo p_nfim e0_mo f0_mo f1_mo f2_mo p_nfs1 f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f1_mo p_nfv f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f1_mo p_nfim f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo f2_mo p_aaan f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f2_mo a_wal a_wa f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi a_wa f2_mo a_wal f1_mo a_wal p_sylibr f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq p_prth f1_mo f2_mo i0_mo p_equtr2 f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi a_wa f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq p_syl6 f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi a_wa f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo f2_mo p_2alimi f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f0_mo f1_mo f2_mo a_wsb f2_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi a_wa f2_mo a_wal f1_mo a_wal f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal p_syl f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal i0_mo p_exlimiv f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo a_wex f0_mo f1_mo a_sup_set_class i0_mo a_sup_set_class a_wceq a_wi f1_mo a_wal i0_mo a_wex f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal p_sylbir f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo f1_mo p_nfa2 e0_mo f0_mo f1_mo f2_mo p_nfs1 f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo p_sp f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f0_mo f0_mo f1_mo f2_mo a_wsb f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq p_exp3a f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f0_mo f0_mo f1_mo f2_mo a_wsb f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq p_com3r f0_mo f1_mo f2_mo a_wsb f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo p_alimd f0_mo f1_mo f2_mo a_wsb f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal p_com12 f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal f0_mo f1_mo f2_mo a_wsb f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo p_eximd f0_mo f1_mo f2_mo a_wsb f2_mo p_alnex e0_mo f0_mo f1_mo f2_mo p_nfs1 f0_mo f1_mo f2_mo a_wsb f1_mo p_nfn e0_mo f0_mo f2_mo p_nfn f0_mo f1_mo f2_mo p_sbequ1 f0_mo f0_mo f1_mo f2_mo a_wsb a_wi f1_mo f2_mo p_equcoms f2_mo a_sup_set_class f1_mo a_sup_set_class a_wceq f0_mo f0_mo f1_mo f2_mo a_wsb p_con3d f0_mo f1_mo f2_mo a_wsb a_wn f0_mo a_wn f2_mo f1_mo p_cbv3 f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq p_pm2.21 f0_mo a_wn f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo p_alimi f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo p_19.8a f0_mo f1_mo f2_mo a_wsb a_wn f2_mo a_wal f0_mo a_wn f1_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo a_wex p_3syl f0_mo f1_mo f2_mo a_wsb f2_mo a_wex a_wn f0_mo f1_mo f2_mo a_wsb a_wn f2_mo a_wal f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo a_wex p_sylbir f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal f0_mo f1_mo f2_mo a_wsb f2_mo a_wex f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo a_wex p_pm2.61d1 f0_mo f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f1_mo a_wal f2_mo a_wex f0_mo f0_mo f1_mo f2_mo a_wsb a_wa f1_mo a_sup_set_class f2_mo a_sup_set_class a_wceq a_wi f2_mo a_wal f1_mo a_wal p_impbii $.
$}

$(Existential uniqueness implies existence.  (Contributed by NM,
       15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x  $.
	$d x y  $.
	$d ph y  $.
	f0_euex $f wff ph $.
	f1_euex $f set x $.
	i0_euex $f set y $.
	p_euex $p |- ( E! x ph -> E. x ph ) $= f0_euex i0_euex p_nfv f0_euex f1_euex i0_euex p_eu1 f0_euex f0_euex f1_euex i0_euex a_wsb f1_euex a_sup_set_class i0_euex a_sup_set_class a_wceq a_wi i0_euex a_wal f1_euex p_exsimpl f0_euex f1_euex a_weu f0_euex f0_euex f1_euex i0_euex a_wsb f1_euex a_sup_set_class i0_euex a_sup_set_class a_wceq a_wi i0_euex a_wal a_wa f1_euex a_wex f0_euex f1_euex a_wex p_sylbi $.
$}

$(Existential uniqueness implies "at most one."  (Contributed by NM,
       8-Jul-1994.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_eumo0 $f wff ph $.
	f1_eumo0 $f set x $.
	f2_eumo0 $f set y $.
	e0_eumo0 $e |- F/ y ph $.
	p_eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $= e0_eumo0 f0_eumo0 f1_eumo0 f2_eumo0 p_euf f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq p_bi1 f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wb f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wi f1_eumo0 p_alimi f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wb f1_eumo0 a_wal f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wi f1_eumo0 a_wal f2_eumo0 p_eximi f0_eumo0 f1_eumo0 a_weu f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wb f1_eumo0 a_wal f2_eumo0 a_wex f0_eumo0 f1_eumo0 a_sup_set_class f2_eumo0 a_sup_set_class a_wceq a_wi f1_eumo0 a_wal f2_eumo0 a_wex p_sylbi $.
$}

$(An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_eu2 $f wff ph $.
	f1_eu2 $f set x $.
	f2_eu2 $f set y $.
	e0_eu2 $e |- F/ y ph $.
	p_eu2 $p |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $= f0_eu2 f1_eu2 p_euex e0_eu2 f0_eu2 f1_eu2 f2_eu2 p_eumo0 e0_eu2 f0_eu2 f1_eu2 f2_eu2 p_mo f0_eu2 f1_eu2 a_weu f0_eu2 f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f1_eu2 a_wal f2_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 a_wal p_sylib f0_eu2 f1_eu2 a_weu f0_eu2 f1_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 a_wal p_jca f0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 p_19.29r f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq p_impexp f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi a_wi f2_eu2 p_albii e0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 p_19.21 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi a_wi f2_eu2 a_wal f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wi p_bitri f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wi f0_eu2 p_anbi2i f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal p_abai f0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wi a_wa f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa p_bitr4i f0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f1_eu2 p_exbii f0_eu2 f1_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 a_wal a_wa f0_eu2 f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f1_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f1_eu2 a_wex p_sylib e0_eu2 f0_eu2 f1_eu2 f2_eu2 p_eu1 f0_eu2 f1_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 a_wal a_wa f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal a_wa f1_eu2 a_wex f0_eu2 f1_eu2 a_weu p_sylibr f0_eu2 f1_eu2 a_weu f0_eu2 f1_eu2 a_wex f0_eu2 f0_eu2 f1_eu2 f2_eu2 a_wsb a_wa f1_eu2 a_sup_set_class f2_eu2 a_sup_set_class a_wceq a_wi f2_eu2 a_wal f1_eu2 a_wal a_wa p_impbii $.
$}

$(An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_eu3 $f wff ph $.
	f1_eu3 $f set x $.
	f2_eu3 $f set y $.
	e0_eu3 $e |- F/ y ph $.
	p_eu3 $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $= e0_eu3 f0_eu3 f1_eu3 f2_eu3 p_eu2 e0_eu3 f0_eu3 f1_eu3 f2_eu3 p_mo f0_eu3 f1_eu3 a_sup_set_class f2_eu3 a_sup_set_class a_wceq a_wi f1_eu3 a_wal f2_eu3 a_wex f0_eu3 f0_eu3 f1_eu3 f2_eu3 a_wsb a_wa f1_eu3 a_sup_set_class f2_eu3 a_sup_set_class a_wceq a_wi f2_eu3 a_wal f1_eu3 a_wal f0_eu3 f1_eu3 a_wex p_anbi2i f0_eu3 f1_eu3 a_weu f0_eu3 f1_eu3 a_wex f0_eu3 f0_eu3 f1_eu3 f2_eu3 a_wsb a_wa f1_eu3 a_sup_set_class f2_eu3 a_sup_set_class a_wceq a_wi f2_eu3 a_wal f1_eu3 a_wal a_wa f0_eu3 f1_eu3 a_wex f0_eu3 f1_eu3 a_sup_set_class f2_eu3 a_sup_set_class a_wceq a_wi f1_eu3 a_wal f2_eu3 a_wex a_wa p_bitr4i $.
$}

$(Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       21-Oct-2005.) $)

${
	$v ph ps x  $.
	f0_euor $f wff ph $.
	f1_euor $f wff ps $.
	f2_euor $f set x $.
	e0_euor $e |- F/ x ph $.
	p_euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $= e0_euor f0_euor f2_euor p_nfn f0_euor f1_euor p_biorf f0_euor a_wn f1_euor f0_euor f1_euor a_wo f2_euor p_eubid f0_euor a_wn f1_euor f2_euor a_weu f0_euor f1_euor a_wo f2_euor a_weu p_biimpa $.
$}

$(Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       23-Mar-1995.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_euorv $f wff ph $.
	f1_euorv $f wff ps $.
	f2_euorv $f set x $.
	p_euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $= f0_euorv f2_euorv p_nfv f0_euorv f1_euorv f2_euorv p_euor $.
$}

$(Alternate definition of "at most one."  (Contributed by NM,
       8-Mar-1995.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_mo2 $f wff ph $.
	f1_mo2 $f set x $.
	f2_mo2 $f set y $.
	e0_mo2 $e |- F/ y ph $.
	p_mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $= f0_mo2 f1_mo2 a_df-mo f0_mo2 f1_mo2 p_alnex f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq p_pm2.21 f0_mo2 a_wn f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 p_alimi f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 p_19.8a f0_mo2 a_wn f1_mo2 a_wal f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_syl f0_mo2 f1_mo2 a_wex a_wn f0_mo2 a_wn f1_mo2 a_wal f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_sylbir e0_mo2 f0_mo2 f1_mo2 f2_mo2 p_eumo0 f0_mo2 f1_mo2 a_wex f0_mo2 f1_mo2 a_weu f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_ja e0_mo2 f0_mo2 f1_mo2 f2_mo2 p_eu3 f0_mo2 f1_mo2 a_weu f0_mo2 f1_mo2 a_wex f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_simplbi2com f0_mo2 f1_mo2 a_wex f0_mo2 f1_mo2 a_weu a_wi f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_impbii f0_mo2 f1_mo2 a_wmo f0_mo2 f1_mo2 a_wex f0_mo2 f1_mo2 a_weu a_wi f0_mo2 f1_mo2 a_sup_set_class f2_mo2 a_sup_set_class a_wceq a_wi f1_mo2 a_wal f2_mo2 a_wex p_bitri $.
$}

$(Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)

${
	$v ph x y z  $.
	$d w x z  $.
	$d w y z  $.
	$d w ph  $.
	f0_sbmo $f wff ph $.
	f1_sbmo $f set x $.
	f2_sbmo $f set y $.
	f3_sbmo $f set z $.
	i0_sbmo $f set w $.
	p_sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $= f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo f1_sbmo f2_sbmo p_sbex f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq f1_sbmo p_nfv f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq f1_sbmo f2_sbmo p_sblim f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f1_sbmo f2_sbmo f3_sbmo p_sbalv f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal f1_sbmo f2_sbmo a_wsb f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo p_exbii f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo a_wex f1_sbmo f2_sbmo a_wsb f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal f1_sbmo f2_sbmo a_wsb i0_sbmo a_wex f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo a_wex p_bitri f0_sbmo i0_sbmo p_nfv f0_sbmo f3_sbmo i0_sbmo p_mo2 f0_sbmo f3_sbmo a_wmo f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo a_wex f1_sbmo f2_sbmo p_sbbii f0_sbmo f1_sbmo f2_sbmo a_wsb i0_sbmo p_nfv f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo i0_sbmo p_mo2 f0_sbmo f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo a_wex f1_sbmo f2_sbmo a_wsb f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo a_sup_set_class i0_sbmo a_sup_set_class a_wceq a_wi f3_sbmo a_wal i0_sbmo a_wex f0_sbmo f3_sbmo a_wmo f1_sbmo f2_sbmo a_wsb f0_sbmo f1_sbmo f2_sbmo a_wsb f3_sbmo a_wmo p_3bitr4i $.
$}

$(Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_mo3 $f wff ph $.
	f1_mo3 $f set x $.
	f2_mo3 $f set y $.
	e0_mo3 $e |- F/ y ph $.
	p_mo3 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= e0_mo3 f0_mo3 f1_mo3 f2_mo3 p_mo2 e0_mo3 f0_mo3 f1_mo3 f2_mo3 p_mo f0_mo3 f1_mo3 a_wmo f0_mo3 f1_mo3 a_sup_set_class f2_mo3 a_sup_set_class a_wceq a_wi f1_mo3 a_wal f2_mo3 a_wex f0_mo3 f0_mo3 f1_mo3 f2_mo3 a_wsb a_wa f1_mo3 a_sup_set_class f2_mo3 a_sup_set_class a_wceq a_wi f2_mo3 a_wal f1_mo3 a_wal p_bitri $.
$}

$("At most one" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d y ph  $.
	f0_mo4f $f wff ph $.
	f1_mo4f $f wff ps $.
	f2_mo4f $f set x $.
	f3_mo4f $f set y $.
	e0_mo4f $e |- F/ x ps $.
	e1_mo4f $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $= f0_mo4f f3_mo4f p_nfv f0_mo4f f2_mo4f f3_mo4f p_mo3 e0_mo4f e1_mo4f f0_mo4f f1_mo4f f2_mo4f f3_mo4f p_sbie f0_mo4f f2_mo4f f3_mo4f a_wsb f1_mo4f f0_mo4f p_anbi2i f0_mo4f f0_mo4f f2_mo4f f3_mo4f a_wsb a_wa f0_mo4f f1_mo4f a_wa f2_mo4f a_sup_set_class f3_mo4f a_sup_set_class a_wceq p_imbi1i f0_mo4f f0_mo4f f2_mo4f f3_mo4f a_wsb a_wa f2_mo4f a_sup_set_class f3_mo4f a_sup_set_class a_wceq a_wi f0_mo4f f1_mo4f a_wa f2_mo4f a_sup_set_class f3_mo4f a_sup_set_class a_wceq a_wi f2_mo4f f3_mo4f p_2albii f0_mo4f f2_mo4f a_wmo f0_mo4f f0_mo4f f2_mo4f f3_mo4f a_wsb a_wa f2_mo4f a_sup_set_class f3_mo4f a_sup_set_class a_wceq a_wi f3_mo4f a_wal f2_mo4f a_wal f0_mo4f f1_mo4f a_wa f2_mo4f a_sup_set_class f3_mo4f a_sup_set_class a_wceq a_wi f3_mo4f a_wal f2_mo4f a_wal p_bitri $.
$}

$("At most one" expressed using implicit substitution.  (Contributed by
       NM, 26-Jul-1995.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_mo4 $f wff ph $.
	f1_mo4 $f wff ps $.
	f2_mo4 $f set x $.
	f3_mo4 $f set y $.
	e0_mo4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $= f1_mo4 f2_mo4 p_nfv e0_mo4 f0_mo4 f1_mo4 f2_mo4 f3_mo4 p_mo4f $.
$}

$(Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by NM, 8-Mar-1995.) $)

${
	$v ph ps ch x  $.
	f0_mobid $f wff ph $.
	f1_mobid $f wff ps $.
	f2_mobid $f wff ch $.
	f3_mobid $f set x $.
	e0_mobid $e |- F/ x ph $.
	e1_mobid $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $= e0_mobid e1_mobid f0_mobid f1_mobid f2_mobid f3_mobid p_exbid e0_mobid e1_mobid f0_mobid f1_mobid f2_mobid f3_mobid p_eubid f0_mobid f1_mobid f3_mobid a_wex f2_mobid f3_mobid a_wex f1_mobid f3_mobid a_weu f2_mobid f3_mobid a_weu p_imbi12d f1_mobid f3_mobid a_df-mo f2_mobid f3_mobid a_df-mo f0_mobid f1_mobid f3_mobid a_wex f1_mobid f3_mobid a_weu a_wi f2_mobid f3_mobid a_wex f2_mobid f3_mobid a_weu a_wi f1_mobid f3_mobid a_wmo f2_mobid f3_mobid a_wmo p_3bitr4g $.
$}

$(Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_mobidv $f wff ph $.
	f1_mobidv $f wff ps $.
	f2_mobidv $f wff ch $.
	f3_mobidv $f set x $.
	e0_mobidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $= f0_mobidv f3_mobidv p_nfv e0_mobidv f0_mobidv f1_mobidv f2_mobidv f3_mobidv p_mobid $.
$}

$(Formula-building rule for "at most one" quantifier (inference rule).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)

${
	$v ps ch x  $.
	f0_mobii $f wff ps $.
	f1_mobii $f wff ch $.
	f2_mobii $f set x $.
	e0_mobii $e |- ( ps <-> ch ) $.
	p_mobii $p |- ( E* x ps <-> E* x ch ) $= e0_mobii f0_mobii f1_mobii a_wb a_wtru p_a1i a_wtru f0_mobii f1_mobii f2_mobii p_mobidv f0_mobii f2_mobii a_wmo f1_mobii f2_mobii a_wmo a_wb p_trud $.
$}

$(Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 9-Mar-1995.)  (Revised by Andrew Salmon,
       8-Jun-2011.) $)

${
	$v ph ps x y  $.
	f0_cbvmo $f wff ph $.
	f1_cbvmo $f wff ps $.
	f2_cbvmo $f set x $.
	f3_cbvmo $f set y $.
	e0_cbvmo $e |- F/ y ph $.
	e1_cbvmo $e |- F/ x ps $.
	e2_cbvmo $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvmo $p |- ( E* x ph <-> E* y ps ) $= e0_cbvmo e1_cbvmo e2_cbvmo f0_cbvmo f1_cbvmo f2_cbvmo f3_cbvmo p_cbvex e0_cbvmo e1_cbvmo e2_cbvmo f0_cbvmo f1_cbvmo f2_cbvmo f3_cbvmo p_cbveu f0_cbvmo f2_cbvmo a_wex f1_cbvmo f3_cbvmo a_wex f0_cbvmo f2_cbvmo a_weu f1_cbvmo f3_cbvmo a_weu p_imbi12i f0_cbvmo f2_cbvmo a_df-mo f1_cbvmo f3_cbvmo a_df-mo f0_cbvmo f2_cbvmo a_wex f0_cbvmo f2_cbvmo a_weu a_wi f1_cbvmo f3_cbvmo a_wex f1_cbvmo f3_cbvmo a_weu a_wi f0_cbvmo f2_cbvmo a_wmo f1_cbvmo f3_cbvmo a_wmo p_3bitr4i $.
$}

$(Uniqueness in terms of "at most one."  (Contributed by NM,
       23-Mar-1995.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	f0_eu5 $f wff ph $.
	f1_eu5 $f set x $.
	i0_eu5 $f set y $.
	p_eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $= f0_eu5 i0_eu5 p_nfv f0_eu5 f1_eu5 i0_eu5 p_eu3 f0_eu5 i0_eu5 p_nfv f0_eu5 f1_eu5 i0_eu5 p_mo2 f0_eu5 f1_eu5 a_wmo f0_eu5 f1_eu5 a_sup_set_class i0_eu5 a_sup_set_class a_wceq a_wi f1_eu5 a_wal i0_eu5 a_wex f0_eu5 f1_eu5 a_wex p_anbi2i f0_eu5 f1_eu5 a_weu f0_eu5 f1_eu5 a_wex f0_eu5 f1_eu5 a_sup_set_class i0_eu5 a_sup_set_class a_wceq a_wi f1_eu5 a_wal i0_eu5 a_wex a_wa f0_eu5 f1_eu5 a_wex f0_eu5 f1_eu5 a_wmo a_wa p_bitr4i $.
$}

$(Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)

${
	$v ph ps x y  $.
	$d x y  $.
	$d y ph  $.
	$d x ps  $.
	f0_eu4 $f wff ph $.
	f1_eu4 $f wff ps $.
	f2_eu4 $f set x $.
	f3_eu4 $f set y $.
	e0_eu4 $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_eu4 $p |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $= f0_eu4 f2_eu4 p_eu5 e0_eu4 f0_eu4 f1_eu4 f2_eu4 f3_eu4 p_mo4 f0_eu4 f2_eu4 a_wmo f0_eu4 f1_eu4 a_wa f2_eu4 a_sup_set_class f3_eu4 a_sup_set_class a_wceq a_wi f3_eu4 a_wal f2_eu4 a_wal f0_eu4 f2_eu4 a_wex p_anbi2i f0_eu4 f2_eu4 a_weu f0_eu4 f2_eu4 a_wex f0_eu4 f2_eu4 a_wmo a_wa f0_eu4 f2_eu4 a_wex f0_eu4 f1_eu4 a_wa f2_eu4 a_sup_set_class f3_eu4 a_sup_set_class a_wceq a_wi f3_eu4 a_wal f2_eu4 a_wal a_wa p_bitri $.
$}

$(Existential uniqueness implies "at most one."  (Contributed by NM,
     23-Mar-1995.) $)

${
	$v ph x  $.
	f0_eumo $f wff ph $.
	f1_eumo $f set x $.
	p_eumo $p |- ( E! x ph -> E* x ph ) $= f0_eumo f1_eumo p_eu5 f0_eumo f1_eumo a_weu f0_eumo f1_eumo a_wex f0_eumo f1_eumo a_wmo p_simprbi $.
$}

$("At most one" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)

${
	$v ph x  $.
	f0_eumoi $f wff ph $.
	f1_eumoi $f set x $.
	e0_eumoi $e |- E! x ph $.
	p_eumoi $p |- E* x ph $= e0_eumoi f0_eumoi f1_eumoi p_eumo f0_eumoi f1_eumoi a_weu f0_eumoi f1_eumoi a_wmo a_ax-mp $.
$}

$(Existence in terms of "at most one" and uniqueness.  (Contributed by NM,
     5-Apr-2004.) $)

${
	$v ph x  $.
	f0_exmoeu $f wff ph $.
	f1_exmoeu $f set x $.
	p_exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $= f0_exmoeu f1_exmoeu a_df-mo f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu a_wi p_biimpi f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu p_com12 f0_exmoeu f1_exmoeu a_df-mo f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu a_wi p_biimpri f0_exmoeu f1_exmoeu p_euex f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu a_wi f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_weu f0_exmoeu f1_exmoeu a_wex p_imim12i f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu p_peirce f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_weu a_wi f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_weu a_wi f0_exmoeu f1_exmoeu a_wex a_wi f0_exmoeu f1_exmoeu a_wex p_syl f0_exmoeu f1_exmoeu a_wex f0_exmoeu f1_exmoeu a_wmo f0_exmoeu f1_exmoeu a_weu a_wi p_impbii $.
$}

$(Existence implies "at most one" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)

${
	$v ph x  $.
	f0_exmoeu2 $f wff ph $.
	f1_exmoeu2 $f set x $.
	p_exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $= f0_exmoeu2 f1_exmoeu2 p_eu5 f0_exmoeu2 f1_exmoeu2 a_weu f0_exmoeu2 f1_exmoeu2 a_wex f0_exmoeu2 f1_exmoeu2 a_wmo p_baibr $.
$}

$(Absorption of existence condition by "at most one."  (Contributed by NM,
     4-Nov-2002.) $)

${
	$v ph x  $.
	f0_moabs $f wff ph $.
	f1_moabs $f set x $.
	p_moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $= f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_weu p_pm5.4 f0_moabs f1_moabs a_df-mo f0_moabs f1_moabs a_wmo f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_weu a_wi f0_moabs f1_moabs a_wex p_imbi2i f0_moabs f1_moabs a_df-mo f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_weu a_wi a_wi f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_weu a_wi f0_moabs f1_moabs a_wex f0_moabs f1_moabs a_wmo a_wi f0_moabs f1_moabs a_wmo p_3bitr4ri $.
$}

$(Something exists or at most one exists.  (Contributed by NM,
     8-Mar-1995.) $)

${
	$v ph x  $.
	f0_exmo $f wff ph $.
	f1_exmo $f set x $.
	p_exmo $p |- ( E. x ph \/ E* x ph ) $= f0_exmo f1_exmo a_wex f0_exmo f1_exmo a_weu p_pm2.21 f0_exmo f1_exmo a_df-mo f0_exmo f1_exmo a_wex a_wn f0_exmo f1_exmo a_wex f0_exmo f1_exmo a_weu a_wi f0_exmo f1_exmo a_wmo p_sylibr f0_exmo f1_exmo a_wex f0_exmo f1_exmo a_wmo p_orri $.
$}

$("At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d y ph  $.
	$d y ps  $.
	f0_moim $f wff ph $.
	f1_moim $f wff ps $.
	f2_moim $f set x $.
	i0_moim $f set y $.
	p_moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $= f0_moim f1_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq p_imim1 f0_moim f1_moim a_wi f1_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f0_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f2_moim p_al2imi f0_moim f1_moim a_wi f2_moim a_wal f1_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f2_moim a_wal f0_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f2_moim a_wal i0_moim p_eximdv f1_moim i0_moim p_nfv f1_moim f2_moim i0_moim p_mo2 f0_moim i0_moim p_nfv f0_moim f2_moim i0_moim p_mo2 f0_moim f1_moim a_wi f2_moim a_wal f1_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f2_moim a_wal i0_moim a_wex f0_moim f2_moim a_sup_set_class i0_moim a_sup_set_class a_wceq a_wi f2_moim a_wal i0_moim a_wex f1_moim f2_moim a_wmo f0_moim f2_moim a_wmo p_3imtr4g $.
$}

$("At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)

${
	$v ph ps x  $.
	f0_moimi $f wff ph $.
	f1_moimi $f wff ps $.
	f2_moimi $f set x $.
	e0_moimi $e |- ( ph -> ps ) $.
	p_moimi $p |- ( E* x ps -> E* x ph ) $= f0_moimi f1_moimi f2_moimi p_moim e0_moimi f0_moimi f1_moimi a_wi f1_moimi f2_moimi a_wmo f0_moimi f2_moimi a_wmo a_wi f2_moimi p_mpg $.
$}

$(Move antecedent outside of "at most one."  (Contributed by NM,
       28-Jul-1995.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d x y ph  $.
	$d y ps  $.
	f0_morimv $f wff ph $.
	f1_morimv $f wff ps $.
	f2_morimv $f set x $.
	i0_morimv $f set y $.
	p_morimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $= f1_morimv f0_morimv a_ax-1 f1_morimv f0_morimv f1_morimv a_wi a_wi f0_morimv p_a1i f0_morimv f1_morimv f0_morimv f1_morimv a_wi f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq p_imim1d f0_morimv f0_morimv f1_morimv a_wi f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f1_morimv f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f2_morimv p_alimdv f0_morimv f0_morimv f1_morimv a_wi f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f2_morimv a_wal f1_morimv f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f2_morimv a_wal i0_morimv p_eximdv f0_morimv f1_morimv a_wi i0_morimv p_nfv f0_morimv f1_morimv a_wi f2_morimv i0_morimv p_mo2 f1_morimv i0_morimv p_nfv f1_morimv f2_morimv i0_morimv p_mo2 f0_morimv f0_morimv f1_morimv a_wi f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f2_morimv a_wal i0_morimv a_wex f1_morimv f2_morimv a_sup_set_class i0_morimv a_sup_set_class a_wceq a_wi f2_morimv a_wal i0_morimv a_wex f0_morimv f1_morimv a_wi f2_morimv a_wmo f1_morimv f2_morimv a_wmo p_3imtr4g f0_morimv f0_morimv f1_morimv a_wi f2_morimv a_wmo f1_morimv f2_morimv a_wmo p_com12 $.
$}

$(Uniqueness implies "at most one" through implication.  (Contributed by NM,
     22-Apr-1995.) $)

${
	$v ph ps x  $.
	f0_euimmo $f wff ph $.
	f1_euimmo $f wff ps $.
	f2_euimmo $f set x $.
	p_euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $= f1_euimmo f2_euimmo p_eumo f0_euimmo f1_euimmo f2_euimmo p_moim f1_euimmo f2_euimmo a_weu f1_euimmo f2_euimmo a_wmo f0_euimmo f1_euimmo a_wi f2_euimmo a_wal f0_euimmo f2_euimmo a_wmo p_syl5 $.
$}

$(Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)

${
	$v ph ps x  $.
	f0_euim $f wff ph $.
	f1_euim $f wff ps $.
	f2_euim $f set x $.
	p_euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $= f0_euim f2_euim a_wex f1_euim f2_euim a_weu a_ax-1 f0_euim f1_euim f2_euim p_euimmo f0_euim f2_euim a_wex f1_euim f2_euim a_weu f0_euim f2_euim a_wex f0_euim f1_euim a_wi f2_euim a_wal f0_euim f2_euim a_wmo p_anim12ii f0_euim f2_euim p_eu5 f0_euim f2_euim a_wex f0_euim f1_euim a_wi f2_euim a_wal a_wa f1_euim f2_euim a_weu f0_euim f2_euim a_wex f0_euim f2_euim a_wmo a_wa f0_euim f2_euim a_weu p_syl6ibr $.
$}

$("At most one" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)

${
	$v ph ps x  $.
	f0_moan $f wff ph $.
	f1_moan $f wff ps $.
	f2_moan $f set x $.
	p_moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $= f1_moan f0_moan p_simpr f1_moan f0_moan a_wa f0_moan f2_moan p_moimi $.
$}

$("At most one" is still true when a conjunct is added.  (Contributed by
       NM, 9-Mar-1995.) $)

${
	$v ph ps x  $.
	f0_moani $f wff ph $.
	f1_moani $f wff ps $.
	f2_moani $f set x $.
	e0_moani $e |- E* x ph $.
	p_moani $p |- E* x ( ps /\ ph ) $= e0_moani f0_moani f1_moani f2_moani p_moan f0_moani f2_moani a_wmo f1_moani f0_moani a_wa f2_moani a_wmo a_ax-mp $.
$}

$("At most one" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)

${
	$v ph ps x  $.
	f0_moor $f wff ph $.
	f1_moor $f wff ps $.
	f2_moor $f set x $.
	p_moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $= f0_moor f1_moor p_orc f0_moor f0_moor f1_moor a_wo f2_moor p_moimi $.
$}

$("At most one" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph ps x  $.
	f0_mooran1 $f wff ph $.
	f1_mooran1 $f wff ps $.
	f2_mooran1 $f set x $.
	p_mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $= f0_mooran1 f1_mooran1 p_simpl f0_mooran1 f1_mooran1 a_wa f0_mooran1 f2_mooran1 p_moimi f1_mooran1 f0_mooran1 f2_mooran1 p_moan f0_mooran1 f2_mooran1 a_wmo f0_mooran1 f1_mooran1 a_wa f2_mooran1 a_wmo f1_mooran1 f2_mooran1 a_wmo p_jaoi $.
$}

$("At most one" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph ps x  $.
	f0_mooran2 $f wff ph $.
	f1_mooran2 $f wff ps $.
	f2_mooran2 $f set x $.
	p_mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $= f0_mooran2 f1_mooran2 f2_mooran2 p_moor f1_mooran2 f0_mooran2 p_olc f1_mooran2 f0_mooran2 f1_mooran2 a_wo f2_mooran2 p_moimi f0_mooran2 f1_mooran2 a_wo f2_mooran2 a_wmo f0_mooran2 f2_mooran2 a_wmo f1_mooran2 f2_mooran2 a_wmo p_jca $.
$}

$(Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 3-Dec-2001.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d y ph  $.
	$d y ps  $.
	f0_moanim $f wff ph $.
	f1_moanim $f wff ps $.
	f2_moanim $f set x $.
	i0_moanim $f set y $.
	e0_moanim $e |- F/ x ph $.
	p_moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $= f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq p_impexp f0_moanim f1_moanim a_wa f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi a_wi f2_moanim p_albii e0_moanim f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim p_19.21 f0_moanim f1_moanim a_wa f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi a_wi f2_moanim a_wal f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal a_wi p_bitri f0_moanim f1_moanim a_wa f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal a_wi i0_moanim p_exbii f0_moanim f1_moanim a_wa i0_moanim p_nfv f0_moanim f1_moanim a_wa f2_moanim i0_moanim p_mo2 f1_moanim i0_moanim p_nfv f1_moanim f2_moanim i0_moanim p_mo2 f1_moanim f2_moanim a_wmo f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal i0_moanim a_wex f0_moanim p_imbi2i f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal i0_moanim p_19.37v f0_moanim f1_moanim f2_moanim a_wmo a_wi f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal i0_moanim a_wex a_wi f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal a_wi i0_moanim a_wex p_bitr4i f0_moanim f1_moanim a_wa f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal i0_moanim a_wex f0_moanim f1_moanim f2_moanim a_sup_set_class i0_moanim a_sup_set_class a_wceq a_wi f2_moanim a_wal a_wi i0_moanim a_wex f0_moanim f1_moanim a_wa f2_moanim a_wmo f0_moanim f1_moanim f2_moanim a_wmo a_wi p_3bitr4i $.
$}

$(Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph ps x  $.
	$d x  $.
	$d ph  $.
	$d ps  $.
	f0_euan $f wff ph $.
	f1_euan $f wff ps $.
	f2_euan $f set x $.
	e0_euan $e |- F/ x ph $.
	p_euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $= e0_euan f0_euan f1_euan p_simpl f0_euan f1_euan a_wa f0_euan f2_euan p_exlimi f0_euan f1_euan a_wa f2_euan a_wex f0_euan f0_euan f1_euan a_wa f2_euan a_wmo p_adantr f0_euan f1_euan p_simpr f0_euan f1_euan a_wa f1_euan f2_euan p_eximi f0_euan f1_euan a_wa f2_euan a_wex f1_euan f2_euan a_wex f0_euan f1_euan a_wa f2_euan a_wmo p_adantr f0_euan f1_euan a_wa f2_euan p_nfe1 f0_euan f1_euan p_simpr e0_euan f0_euan f1_euan p_simpl f0_euan f1_euan a_wa f0_euan f2_euan p_exlimi f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan p_a1d f0_euan f1_euan a_wa f2_euan a_wex f1_euan f0_euan p_ancrd f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan a_wa f1_euan p_impbid2 f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan a_wa f1_euan f2_euan p_mobid f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan a_wa f2_euan a_wmo f1_euan f2_euan a_wmo p_biimpa f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan a_wa f2_euan a_wmo a_wa f0_euan f1_euan f2_euan a_wex f1_euan f2_euan a_wmo p_jca32 f0_euan f1_euan a_wa f2_euan p_eu5 f1_euan f2_euan p_eu5 f1_euan f2_euan a_weu f1_euan f2_euan a_wex f1_euan f2_euan a_wmo a_wa f0_euan p_anbi2i f0_euan f1_euan a_wa f2_euan a_wex f0_euan f1_euan a_wa f2_euan a_wmo a_wa f0_euan f1_euan f2_euan a_wex f1_euan f2_euan a_wmo a_wa a_wa f0_euan f1_euan a_wa f2_euan a_weu f0_euan f1_euan f2_euan a_weu a_wa p_3imtr4i e0_euan f0_euan f1_euan p_ibar f0_euan f1_euan f0_euan f1_euan a_wa f2_euan p_eubid f0_euan f1_euan f2_euan a_weu f0_euan f1_euan a_wa f2_euan a_weu p_biimpa f0_euan f1_euan a_wa f2_euan a_weu f0_euan f1_euan f2_euan a_weu a_wa p_impbii $.
$}

$(Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	$d ps  $.
	f0_moanimv $f wff ph $.
	f1_moanimv $f wff ps $.
	f2_moanimv $f set x $.
	p_moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $= f0_moanimv f2_moanimv p_nfv f0_moanimv f1_moanimv f2_moanimv p_moanim $.
$}

$(Nested "at most one" and uniqueness quantifiers.  (Contributed by NM,
     25-Jan-2006.) $)

${
	$v ph x  $.
	f0_moaneu $f wff ph $.
	f1_moaneu $f set x $.
	p_moaneu $p |- E* x ( ph /\ E! x ph ) $= f0_moaneu f1_moaneu p_eumo f0_moaneu f1_moaneu p_nfeu1 f0_moaneu f1_moaneu a_weu f0_moaneu f1_moaneu p_moanim f0_moaneu f1_moaneu a_weu f0_moaneu a_wa f1_moaneu a_wmo f0_moaneu f1_moaneu a_weu f0_moaneu f1_moaneu a_wmo a_wi p_mpbir f0_moaneu f0_moaneu f1_moaneu a_weu p_ancom f0_moaneu f0_moaneu f1_moaneu a_weu a_wa f0_moaneu f1_moaneu a_weu f0_moaneu a_wa f1_moaneu p_mobii f0_moaneu f0_moaneu f1_moaneu a_weu a_wa f1_moaneu a_wmo f0_moaneu f1_moaneu a_weu f0_moaneu a_wa f1_moaneu a_wmo p_mpbir $.
$}

$(Nested "at most one" quantifiers.  (Contributed by NM, 25-Jan-2006.) $)

${
	$v ph x  $.
	f0_moanmo $f wff ph $.
	f1_moanmo $f set x $.
	p_moanmo $p |- E* x ( ph /\ E* x ph ) $= f0_moanmo f1_moanmo a_wmo p_id f0_moanmo f1_moanmo p_nfmo1 f0_moanmo f1_moanmo a_wmo f0_moanmo f1_moanmo p_moanim f0_moanmo f1_moanmo a_wmo f0_moanmo a_wa f1_moanmo a_wmo f0_moanmo f1_moanmo a_wmo f0_moanmo f1_moanmo a_wmo a_wi p_mpbir f0_moanmo f0_moanmo f1_moanmo a_wmo p_ancom f0_moanmo f0_moanmo f1_moanmo a_wmo a_wa f0_moanmo f1_moanmo a_wmo f0_moanmo a_wa f1_moanmo p_mobii f0_moanmo f0_moanmo f1_moanmo a_wmo a_wa f1_moanmo a_wmo f0_moanmo f1_moanmo a_wmo f0_moanmo a_wa f1_moanmo a_wmo p_mpbir $.
$}

$(Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)

${
	$v ph ps x  $.
	$d x ph  $.
	f0_euanv $f wff ph $.
	f1_euanv $f wff ps $.
	f2_euanv $f set x $.
	p_euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $= f0_euanv f2_euanv p_nfv f0_euanv f1_euanv f2_euanv p_euan $.
$}

$("At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d y ph  $.
	$d y ps  $.
	f0_mopick $f wff ph $.
	f1_mopick $f wff ps $.
	f2_mopick $f set x $.
	i0_mopick $f set y $.
	p_mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $= f0_mopick f1_mopick a_wa i0_mopick p_nfv f0_mopick f2_mopick i0_mopick p_nfs1v f1_mopick f2_mopick i0_mopick p_nfs1v f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb f2_mopick p_nfan f0_mopick f2_mopick i0_mopick p_sbequ12 f1_mopick f2_mopick i0_mopick p_sbequ12 f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq f0_mopick f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f1_mopick f2_mopick i0_mopick a_wsb p_anbi12d f0_mopick f1_mopick a_wa f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick i0_mopick p_cbvex f0_mopick i0_mopick p_nfv f0_mopick f2_mopick i0_mopick p_mo3 f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi i0_mopick p_sp f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi i0_mopick a_wal f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi f2_mopick p_sps f0_mopick f2_mopick a_wmo f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi i0_mopick a_wal f2_mopick a_wal f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi p_sylbi f1_mopick f2_mopick i0_mopick p_sbequ2 f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq f1_mopick f2_mopick i0_mopick a_wsb f1_mopick a_wi f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa p_imim2i f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi f0_mopick f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb f1_mopick a_wi p_exp3a f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi f0_mopick f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb f1_mopick p_com4t f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi f0_mopick f1_mopick a_wi a_wi p_imp f0_mopick f2_mopick a_wmo f0_mopick f0_mopick f2_mopick i0_mopick a_wsb a_wa f2_mopick a_sup_set_class i0_mopick a_sup_set_class a_wceq a_wi f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb a_wa f0_mopick f1_mopick a_wi p_syl5 f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb a_wa f0_mopick f2_mopick a_wmo f0_mopick f1_mopick a_wi a_wi i0_mopick p_exlimiv f0_mopick f1_mopick a_wa f2_mopick a_wex f0_mopick f2_mopick i0_mopick a_wsb f1_mopick f2_mopick i0_mopick a_wsb a_wa i0_mopick a_wex f0_mopick f2_mopick a_wmo f0_mopick f1_mopick a_wi a_wi p_sylbi f0_mopick f1_mopick a_wa f2_mopick a_wex f0_mopick f2_mopick a_wmo f0_mopick f1_mopick a_wi p_impcom $.
$}

$(Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)

${
	$v ph ps x  $.
	f0_eupick $f wff ph $.
	f1_eupick $f wff ps $.
	f2_eupick $f set x $.
	p_eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $= f0_eupick f2_eupick p_eumo f0_eupick f1_eupick f2_eupick p_mopick f0_eupick f2_eupick a_weu f0_eupick f2_eupick a_wmo f0_eupick f1_eupick a_wa f2_eupick a_wex f0_eupick f1_eupick a_wi p_sylan $.
$}

$(Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)

${
	$v ph ps x  $.
	f0_eupicka $f wff ph $.
	f1_eupicka $f wff ps $.
	f2_eupicka $f set x $.
	p_eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $= f0_eupicka f2_eupicka p_nfeu1 f0_eupicka f1_eupicka a_wa f2_eupicka p_nfe1 f0_eupicka f2_eupicka a_weu f0_eupicka f1_eupicka a_wa f2_eupicka a_wex f2_eupicka p_nfan f0_eupicka f1_eupicka f2_eupicka p_eupick f0_eupicka f2_eupicka a_weu f0_eupicka f1_eupicka a_wa f2_eupicka a_wex a_wa f0_eupicka f1_eupicka a_wi f2_eupicka p_alrimi $.
$}

$(Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.) $)

${
	$v ph ps x  $.
	f0_eupickb $f wff ph $.
	f1_eupickb $f wff ps $.
	f2_eupickb $f set x $.
	p_eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) -> ( ph <-> ps ) ) $= f0_eupickb f1_eupickb f2_eupickb p_eupick f0_eupickb f2_eupickb a_weu f0_eupickb f1_eupickb a_wa f2_eupickb a_wex f0_eupickb f1_eupickb a_wi f1_eupickb f2_eupickb a_weu p_3adant2 f0_eupickb f2_eupickb a_weu f1_eupickb f2_eupickb a_weu f0_eupickb f1_eupickb a_wa f2_eupickb a_wex p_3simpc f0_eupickb f1_eupickb p_pm3.22 f0_eupickb f1_eupickb a_wa f1_eupickb f0_eupickb a_wa f2_eupickb p_eximi f0_eupickb f1_eupickb a_wa f2_eupickb a_wex f1_eupickb f0_eupickb a_wa f2_eupickb a_wex f1_eupickb f2_eupickb a_weu p_anim2i f1_eupickb f0_eupickb f2_eupickb p_eupick f0_eupickb f2_eupickb a_weu f1_eupickb f2_eupickb a_weu f0_eupickb f1_eupickb a_wa f2_eupickb a_wex a_w3a f1_eupickb f2_eupickb a_weu f0_eupickb f1_eupickb a_wa f2_eupickb a_wex a_wa f1_eupickb f2_eupickb a_weu f1_eupickb f0_eupickb a_wa f2_eupickb a_wex a_wa f1_eupickb f0_eupickb a_wi p_3syl f0_eupickb f2_eupickb a_weu f1_eupickb f2_eupickb a_weu f0_eupickb f1_eupickb a_wa f2_eupickb a_wex a_w3a f0_eupickb f1_eupickb p_impbid $.
$}

$(Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)

${
	$v ph ps x  $.
	f0_eupickbi $f wff ph $.
	f1_eupickbi $f wff ps $.
	f2_eupickbi $f set x $.
	p_eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $= f0_eupickbi f1_eupickbi f2_eupickbi p_eupicka f0_eupickbi f2_eupickbi a_weu f0_eupickbi f1_eupickbi a_wa f2_eupickbi a_wex f0_eupickbi f1_eupickbi a_wi f2_eupickbi a_wal p_ex f0_eupickbi f1_eupickbi a_wi f2_eupickbi p_nfa1 f0_eupickbi f1_eupickbi p_ancl f0_eupickbi f1_eupickbi p_simpl f0_eupickbi f1_eupickbi a_wi f0_eupickbi f0_eupickbi f1_eupickbi a_wa p_impbid1 f0_eupickbi f1_eupickbi a_wi f0_eupickbi f0_eupickbi f1_eupickbi a_wa a_wb f2_eupickbi p_sps f0_eupickbi f1_eupickbi a_wi f2_eupickbi a_wal f0_eupickbi f0_eupickbi f1_eupickbi a_wa f2_eupickbi p_eubid f0_eupickbi f1_eupickbi a_wa f2_eupickbi p_euex f0_eupickbi f1_eupickbi a_wi f2_eupickbi a_wal f0_eupickbi f2_eupickbi a_weu f0_eupickbi f1_eupickbi a_wa f2_eupickbi a_weu f0_eupickbi f1_eupickbi a_wa f2_eupickbi a_wex p_syl6bi f0_eupickbi f1_eupickbi a_wi f2_eupickbi a_wal f0_eupickbi f2_eupickbi a_weu f0_eupickbi f1_eupickbi a_wa f2_eupickbi a_wex p_com12 f0_eupickbi f2_eupickbi a_weu f0_eupickbi f1_eupickbi a_wa f2_eupickbi a_wex f0_eupickbi f1_eupickbi a_wi f2_eupickbi a_wal p_impbid $.
$}

$("At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph ps ch x  $.
	f0_mopick2 $f wff ph $.
	f1_mopick2 $f wff ps $.
	f2_mopick2 $f wff ch $.
	f3_mopick2 $f set x $.
	p_mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) -> E. x ( ph /\ ps /\ ch ) ) $= f0_mopick2 f3_mopick2 p_nfmo1 f0_mopick2 f1_mopick2 a_wa f3_mopick2 p_nfe1 f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex f3_mopick2 p_nfan f0_mopick2 f1_mopick2 f3_mopick2 p_mopick f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex a_wa f0_mopick2 f1_mopick2 p_ancld f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex a_wa f0_mopick2 f0_mopick2 f1_mopick2 a_wa f2_mopick2 p_anim1d f0_mopick2 f1_mopick2 f2_mopick2 a_df-3an f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex a_wa f0_mopick2 f2_mopick2 a_wa f0_mopick2 f1_mopick2 a_wa f2_mopick2 a_wa f0_mopick2 f1_mopick2 f2_mopick2 a_w3a p_syl6ibr f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex a_wa f0_mopick2 f2_mopick2 a_wa f0_mopick2 f1_mopick2 f2_mopick2 a_w3a f3_mopick2 p_eximd f0_mopick2 f3_mopick2 a_wmo f0_mopick2 f1_mopick2 a_wa f3_mopick2 a_wex f0_mopick2 f2_mopick2 a_wa f3_mopick2 a_wex f0_mopick2 f1_mopick2 f2_mopick2 a_w3a f3_mopick2 a_wex p_3impia $.
$}

$(Introduce or eliminate a disjunct in a uniqueness quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.) $)

${
	$v ph ps x  $.
	f0_euor2 $f wff ph $.
	f1_euor2 $f wff ps $.
	f2_euor2 $f set x $.
	p_euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $= f0_euor2 f2_euor2 p_nfe1 f0_euor2 f2_euor2 a_wex f2_euor2 p_nfn f0_euor2 f2_euor2 p_19.8a f0_euor2 f0_euor2 f2_euor2 a_wex p_con3i f0_euor2 f1_euor2 p_orel1 f1_euor2 f0_euor2 p_olc f0_euor2 a_wn f0_euor2 f1_euor2 a_wo f1_euor2 p_impbid1 f0_euor2 f2_euor2 a_wex a_wn f0_euor2 a_wn f0_euor2 f1_euor2 a_wo f1_euor2 a_wb p_syl f0_euor2 f2_euor2 a_wex a_wn f0_euor2 f1_euor2 a_wo f1_euor2 f2_euor2 p_eubid $.
$}

$("At most one" double quantification.  (Contributed by NM,
       3-Dec-2001.) $)

${
	$v ph ps x y  $.
	f0_moexex $f wff ph $.
	f1_moexex $f wff ps $.
	f2_moexex $f set x $.
	f3_moexex $f set y $.
	e0_moexex $e |- F/ y ph $.
	p_moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $= f0_moexex f2_moexex p_nfmo1 f1_moexex f3_moexex a_wmo f2_moexex p_nfa1 f0_moexex f1_moexex a_wa f2_moexex p_nfe1 f0_moexex f1_moexex a_wa f2_moexex a_wex f2_moexex f3_moexex p_nfmo f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo f2_moexex p_nfim f0_moexex f2_moexex a_wmo f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo a_wi f2_moexex p_nfim e0_moexex e0_moexex f0_moexex f3_moexex f2_moexex p_nfmo f0_moexex f1_moexex f2_moexex p_mopick f0_moexex f2_moexex a_wmo f0_moexex f1_moexex a_wa f2_moexex a_wex f0_moexex f1_moexex a_wi p_ex f0_moexex f2_moexex a_wmo f0_moexex f1_moexex a_wa f2_moexex a_wex f0_moexex f1_moexex p_com3r f0_moexex f0_moexex f2_moexex a_wmo f0_moexex f1_moexex a_wa f2_moexex a_wex f1_moexex a_wi f3_moexex p_alrimd f0_moexex f1_moexex a_wa f2_moexex a_wex f1_moexex f3_moexex p_moim f0_moexex f1_moexex a_wa f2_moexex a_wex f1_moexex a_wi f3_moexex a_wal f1_moexex f3_moexex a_wmo f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo f2_moexex p_spsd f0_moexex f0_moexex f2_moexex a_wmo f0_moexex f1_moexex a_wa f2_moexex a_wex f1_moexex a_wi f3_moexex a_wal f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo a_wi p_syl6 f0_moexex f0_moexex f2_moexex a_wmo f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo a_wi a_wi f2_moexex p_exlimi e0_moexex f0_moexex f3_moexex f2_moexex p_nfex f0_moexex f1_moexex f2_moexex p_exsimpl f0_moexex f1_moexex a_wa f2_moexex a_wex f0_moexex f2_moexex a_wex f3_moexex p_exlimi f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wex f0_moexex f2_moexex a_wex p_con3i f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex p_exmo f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wex f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo p_ori f0_moexex f2_moexex a_wex a_wn f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wex a_wn f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo p_syl f0_moexex f2_moexex a_wex a_wn f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo f1_moexex f3_moexex a_wmo f2_moexex a_wal p_a1d f0_moexex f2_moexex a_wex a_wn f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo a_wi f0_moexex f2_moexex a_wmo p_a1d f0_moexex f2_moexex a_wex f0_moexex f2_moexex a_wmo f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo a_wi a_wi p_pm2.61i f0_moexex f2_moexex a_wmo f1_moexex f3_moexex a_wmo f2_moexex a_wal f0_moexex f1_moexex a_wa f2_moexex a_wex f3_moexex a_wmo p_imp $.
$}

$("At most one" double quantification.  (Contributed by NM,
       26-Jan-1997.) $)

${
	$v ph ps x y  $.
	$d y ph  $.
	f0_moexexv $f wff ph $.
	f1_moexexv $f wff ps $.
	f2_moexexv $f set x $.
	f3_moexexv $f set y $.
	p_moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $= f0_moexexv f3_moexexv p_nfv f0_moexexv f1_moexexv f2_moexexv f3_moexexv p_moexex $.
$}

$(Double quantification with "at most one."  (Contributed by NM,
     3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2moex $f wff ph $.
	f1_2moex $f set x $.
	f2_2moex $f set y $.
	p_2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $= f0_2moex f2_2moex p_nfe1 f0_2moex f2_2moex a_wex f2_2moex f1_2moex p_nfmo f0_2moex f2_2moex p_19.8a f0_2moex f0_2moex f2_2moex a_wex f1_2moex p_moimi f0_2moex f2_2moex a_wex f1_2moex a_wmo f0_2moex f1_2moex a_wmo f2_2moex p_alrimi $.
$}

$(Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x y  $.
	f0_2euex $f wff ph $.
	f1_2euex $f set x $.
	f2_2euex $f set y $.
	p_2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $= f0_2euex f2_2euex a_wex f1_2euex p_eu5 f0_2euex f1_2euex f2_2euex p_excom f0_2euex f2_2euex p_nfe1 f0_2euex f2_2euex a_wex f2_2euex f1_2euex p_nfmo f0_2euex f2_2euex p_19.8a f0_2euex f0_2euex f2_2euex a_wex f1_2euex p_moimi f0_2euex f1_2euex a_df-mo f0_2euex f2_2euex a_wex f1_2euex a_wmo f0_2euex f1_2euex a_wmo f0_2euex f1_2euex a_wex f0_2euex f1_2euex a_weu a_wi p_sylib f0_2euex f2_2euex a_wex f1_2euex a_wmo f0_2euex f1_2euex a_wex f0_2euex f1_2euex a_weu f2_2euex p_eximd f0_2euex f2_2euex a_wex f1_2euex a_wex f0_2euex f1_2euex a_wex f2_2euex a_wex f0_2euex f2_2euex a_wex f1_2euex a_wmo f0_2euex f1_2euex a_weu f2_2euex a_wex p_syl5bi f0_2euex f2_2euex a_wex f1_2euex a_wmo f0_2euex f2_2euex a_wex f1_2euex a_wex f0_2euex f1_2euex a_weu f2_2euex a_wex p_impcom f0_2euex f2_2euex a_wex f1_2euex a_weu f0_2euex f2_2euex a_wex f1_2euex a_wex f0_2euex f2_2euex a_wex f1_2euex a_wmo a_wa f0_2euex f1_2euex a_weu f2_2euex a_wex p_sylbi $.
$}

$(Double quantification with existential uniqueness and "at most one."
     (Contributed by NM, 3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2eumo $f wff ph $.
	f1_2eumo $f set x $.
	f2_2eumo $f set y $.
	p_2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $= f0_2eumo f2_2eumo a_weu f0_2eumo f2_2eumo a_wmo f1_2eumo p_euimmo f0_2eumo f2_2eumo p_eumo f0_2eumo f2_2eumo a_weu f0_2eumo f2_2eumo a_wmo a_wi f0_2eumo f2_2eumo a_wmo f1_2eumo a_weu f0_2eumo f2_2eumo a_weu f1_2eumo a_wmo a_wi f1_2eumo p_mpg $.
$}

$(Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2eu2ex $f wff ph $.
	f1_2eu2ex $f set x $.
	f2_2eu2ex $f set y $.
	p_2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $= f0_2eu2ex f2_2eu2ex a_weu f1_2eu2ex p_euex f0_2eu2ex f2_2eu2ex p_euex f0_2eu2ex f2_2eu2ex a_weu f0_2eu2ex f2_2eu2ex a_wex f1_2eu2ex p_eximi f0_2eu2ex f2_2eu2ex a_weu f1_2eu2ex a_weu f0_2eu2ex f2_2eu2ex a_weu f1_2eu2ex a_wex f0_2eu2ex f2_2eu2ex a_wex f1_2eu2ex a_wex p_syl $.
$}

$(A condition allowing swap of "at most one" and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)

${
	$v ph x y  $.
	f0_2moswap $f wff ph $.
	f1_2moswap $f set x $.
	f2_2moswap $f set y $.
	p_2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $= f0_2moswap f2_2moswap p_nfe1 f0_2moswap f2_2moswap a_wex f0_2moswap f1_2moswap f2_2moswap p_moexex f0_2moswap f2_2moswap a_wex f1_2moswap a_wmo f0_2moswap f2_2moswap a_wmo f1_2moswap a_wal f0_2moswap f2_2moswap a_wex f0_2moswap a_wa f1_2moswap a_wex f2_2moswap a_wmo p_expcom f0_2moswap f2_2moswap p_19.8a f0_2moswap f0_2moswap f2_2moswap a_wex p_pm4.71ri f0_2moswap f0_2moswap f2_2moswap a_wex f0_2moswap a_wa f1_2moswap p_exbii f0_2moswap f1_2moswap a_wex f0_2moswap f2_2moswap a_wex f0_2moswap a_wa f1_2moswap a_wex f2_2moswap p_mobii f0_2moswap f2_2moswap a_wmo f1_2moswap a_wal f0_2moswap f2_2moswap a_wex f1_2moswap a_wmo f0_2moswap f2_2moswap a_wex f0_2moswap a_wa f1_2moswap a_wex f2_2moswap a_wmo f0_2moswap f1_2moswap a_wex f2_2moswap a_wmo p_syl6ibr $.
$}

$(A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)

${
	$v ph x y  $.
	f0_2euswap $f wff ph $.
	f1_2euswap $f set x $.
	f2_2euswap $f set y $.
	p_2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $= f0_2euswap f1_2euswap f2_2euswap p_excomim f0_2euswap f2_2euswap a_wex f1_2euswap a_wex f0_2euswap f1_2euswap a_wex f2_2euswap a_wex a_wi f0_2euswap f2_2euswap a_wmo f1_2euswap a_wal p_a1i f0_2euswap f1_2euswap f2_2euswap p_2moswap f0_2euswap f2_2euswap a_wmo f1_2euswap a_wal f0_2euswap f2_2euswap a_wex f1_2euswap a_wex f0_2euswap f1_2euswap a_wex f2_2euswap a_wex f0_2euswap f2_2euswap a_wex f1_2euswap a_wmo f0_2euswap f1_2euswap a_wex f2_2euswap a_wmo p_anim12d f0_2euswap f2_2euswap a_wex f1_2euswap p_eu5 f0_2euswap f1_2euswap a_wex f2_2euswap p_eu5 f0_2euswap f2_2euswap a_wmo f1_2euswap a_wal f0_2euswap f2_2euswap a_wex f1_2euswap a_wex f0_2euswap f2_2euswap a_wex f1_2euswap a_wmo a_wa f0_2euswap f1_2euswap a_wex f2_2euswap a_wex f0_2euswap f1_2euswap a_wex f2_2euswap a_wmo a_wa f0_2euswap f2_2euswap a_wex f1_2euswap a_weu f0_2euswap f1_2euswap a_wex f2_2euswap a_weu p_3imtr4g $.
$}

$(Double existential uniqueness implies double uniqueness quantification.
     (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro,
     22-Dec-2016.) $)

${
	$v ph x y  $.
	f0_2exeu $f wff ph $.
	f1_2exeu $f set x $.
	f2_2exeu $f set y $.
	p_2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $= f0_2exeu f2_2exeu a_wex f1_2exeu p_eumo f0_2exeu f2_2exeu p_euex f0_2exeu f2_2exeu a_weu f0_2exeu f2_2exeu a_wex f1_2exeu p_moimi f0_2exeu f2_2exeu a_wex f1_2exeu a_weu f0_2exeu f2_2exeu a_wex f1_2exeu a_wmo f0_2exeu f2_2exeu a_weu f1_2exeu a_wmo p_syl f0_2exeu f2_2exeu f1_2exeu p_2euex f0_2exeu f2_2exeu a_wex f1_2exeu a_weu f0_2exeu f2_2exeu a_weu f1_2exeu a_wmo f0_2exeu f1_2exeu a_wex f2_2exeu a_weu f0_2exeu f2_2exeu a_weu f1_2exeu a_wex p_anim12ci f0_2exeu f2_2exeu a_weu f1_2exeu p_eu5 f0_2exeu f2_2exeu a_wex f1_2exeu a_weu f0_2exeu f1_2exeu a_wex f2_2exeu a_weu a_wa f0_2exeu f2_2exeu a_weu f1_2exeu a_wex f0_2exeu f2_2exeu a_weu f1_2exeu a_wmo a_wa f0_2exeu f2_2exeu a_weu f1_2exeu a_weu p_sylibr $.
$}

$(Two equivalent expressions for double "at most one."  (Contributed by
       NM, 2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.) $)

${
	$v ph x y z w  $.
	$d x y z w v u  $.
	$d z w v u ph  $.
	f0_2mo $f wff ph $.
	f1_2mo $f set x $.
	f2_2mo $f set y $.
	f3_2mo $f set z $.
	f4_2mo $f set w $.
	i0_2mo $f set v $.
	i1_2mo $f set u $.
	p_2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) -> ( x = z /\ y = w ) ) ) $= i0_2mo f3_2mo f1_2mo p_equequ2 i1_2mo f4_2mo f2_2mo p_equequ2 i0_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq i1_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq p_bi2anan9 i0_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq i1_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa f0_2mo p_imbi2d i0_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq i1_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f1_2mo f2_2mo p_2albidv f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal i0_2mo i1_2mo f3_2mo f4_2mo p_cbvex2v f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f3_2mo p_nfv f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_nfs1v f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f1_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f1_2mo p_nfim f0_2mo f2_2mo f4_2mo p_nfs1v f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo f2_2mo p_nfsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f2_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f2_2mo p_nfim f0_2mo f2_2mo f4_2mo p_sbequ12 f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_sbequ12 f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb p_sylan9bbr f1_2mo f3_2mo i0_2mo p_equequ1 f2_2mo f4_2mo i1_2mo p_equequ1 f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq p_bi2anan9 f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa p_imbi12d f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f1_2mo f2_2mo f3_2mo f4_2mo p_cbval2 f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal p_biimpi f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal p_ancli f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f2_2mo f3_2mo p_alcom f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo p_nfv f0_2mo f2_2mo f4_2mo p_nfs1v f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo f2_2mo p_nfsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f2_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f2_2mo p_nfim f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo f4_2mo p_aaan f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f2_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal a_wa f3_2mo p_albii f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f2_2mo a_wal f3_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal a_wa f3_2mo a_wal p_bitri f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal a_wa f3_2mo a_wal f1_2mo p_albii f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f3_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_nfs1v f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f1_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f1_2mo p_nfim f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f1_2mo f4_2mo p_nfal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f1_2mo f3_2mo p_aaan f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal a_wa f3_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal a_wa p_bitri f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal a_wa f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal p_sylibr f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa p_prth f1_2mo f3_2mo i0_2mo p_equtr2 f2_2mo f4_2mo i1_2mo p_equtr2 f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq p_anim12i f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa p_an4s f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa p_syl6 f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f3_2mo f4_2mo p_2alimi f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f1_2mo f2_2mo p_2alimi f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f3_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f4_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi a_wa f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal p_syl f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal i0_2mo i1_2mo p_exlimivv f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex f0_2mo f1_2mo a_sup_set_class i0_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class i1_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal i1_2mo a_wex i0_2mo a_wex f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal p_sylbir f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f1_2mo f2_2mo f3_2mo f4_2mo p_alrot4 f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_nfs1v f0_2mo f2_2mo f4_2mo p_nfs1v f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo f2_2mo p_nfsb f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo p_pm3.21 f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa p_imim1d f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo p_alimd f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo p_alimd f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal p_com12 f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal a_wi f4_2mo p_alimi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo p_exim f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal a_wi f4_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex a_wi p_syl f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex a_wi f3_2mo p_alimi f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wal f3_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex a_wi f3_2mo a_wal p_sylbi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo p_exim f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex a_wi f3_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f3_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex a_wi p_syl f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo p_alnex f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f4_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex a_wn f3_2mo p_albii f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f3_2mo p_alnex f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f4_2mo a_wal f3_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex a_wn f3_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f3_2mo a_wex a_wn p_bitri f0_2mo a_wn f3_2mo p_nfv f0_2mo a_wn f4_2mo p_nfv f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_nfs1v f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f1_2mo p_nfn f0_2mo f2_2mo f4_2mo p_nfs1v f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo f2_2mo p_nfsb f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f2_2mo p_nfn f0_2mo f2_2mo f4_2mo p_sbequ12 f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo p_sbequ12 f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb p_sylan9bbr f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb p_notbid f0_2mo a_wn f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f1_2mo f2_2mo f3_2mo f4_2mo p_cbval2 f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa p_pm2.21 f0_2mo a_wn f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f1_2mo f2_2mo p_2alimi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f4_2mo a_wal f3_2mo a_wal f0_2mo a_wn f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal p_sylbir f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo p_19.8a f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex f4_2mo p_19.23bi f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f4_2mo a_wal f3_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex p_syl f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f3_2mo a_wex a_wn f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wn f4_2mo a_wal f3_2mo a_wal f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex p_sylbir f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb f4_2mo a_wex f3_2mo a_wex f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex p_pm2.61d1 f0_2mo f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f2_2mo a_wal f1_2mo a_wal f4_2mo a_wex f3_2mo a_wex f0_2mo f0_2mo f2_2mo f4_2mo a_wsb f1_2mo f3_2mo a_wsb a_wa f1_2mo a_sup_set_class f3_2mo a_sup_set_class a_wceq f2_2mo a_sup_set_class f4_2mo a_sup_set_class a_wceq a_wa a_wi f4_2mo a_wal f3_2mo a_wal f2_2mo a_wal f1_2mo a_wal p_impbii $.
$}

$(Double "exists at most one", using implicit substitution.  (Contributed
       by NM, 10-Feb-2005.) $)

${
	$v ph ps x y z w  $.
	$d z w ph  $.
	$d x y ps  $.
	$d x y z w  $.
	f0_2mos $f wff ph $.
	f1_2mos $f wff ps $.
	f2_2mos $f set x $.
	f3_2mos $f set y $.
	f4_2mos $f set z $.
	f5_2mos $f set w $.
	e0_2mos $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	p_2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $= f0_2mos f2_2mos f3_2mos f4_2mos f5_2mos p_2mo f1_2mos f2_2mos p_nfv f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos p_nfv f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos f3_2mos f5_2mos p_sbrim f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f1_2mos a_wi f3_2mos p_nfv e0_2mos f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq f0_2mos f1_2mos a_wb p_expcom f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos f1_2mos p_pm5.74d f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos a_wi f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f1_2mos a_wi f3_2mos f5_2mos p_sbie f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos f3_2mos f5_2mos a_wsb a_wi f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos a_wi f3_2mos f5_2mos a_wsb f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f1_2mos a_wi p_bitr3i f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f0_2mos f3_2mos f5_2mos a_wsb f1_2mos p_pm5.74ri f0_2mos f3_2mos f5_2mos a_wsb f1_2mos f2_2mos f4_2mos p_sbie f0_2mos f3_2mos f5_2mos a_wsb f2_2mos f4_2mos a_wsb f1_2mos f0_2mos p_anbi2i f0_2mos f0_2mos f3_2mos f5_2mos a_wsb f2_2mos f4_2mos a_wsb a_wa f0_2mos f1_2mos a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa p_imbi1i f0_2mos f0_2mos f3_2mos f5_2mos a_wsb f2_2mos f4_2mos a_wsb a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f0_2mos f1_2mos a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f4_2mos f5_2mos p_2albii f0_2mos f0_2mos f3_2mos f5_2mos a_wsb f2_2mos f4_2mos a_wsb a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f5_2mos a_wal f4_2mos a_wal f0_2mos f1_2mos a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f5_2mos a_wal f4_2mos a_wal f2_2mos f3_2mos p_2albii f0_2mos f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f3_2mos a_wal f2_2mos a_wal f5_2mos a_wex f4_2mos a_wex f0_2mos f0_2mos f3_2mos f5_2mos a_wsb f2_2mos f4_2mos a_wsb a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f5_2mos a_wal f4_2mos a_wal f3_2mos a_wal f2_2mos a_wal f0_2mos f1_2mos a_wa f2_2mos a_sup_set_class f4_2mos a_sup_set_class a_wceq f3_2mos a_sup_set_class f5_2mos a_sup_set_class a_wceq a_wa a_wi f5_2mos a_wal f4_2mos a_wal f3_2mos a_wal f2_2mos a_wal p_bitri $.
$}

$(Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one.  (Contributed by NM,
     3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2eu1 $f wff ph $.
	f1_2eu1 $f set x $.
	f2_2eu1 $f set y $.
	p_2eu1 $p |- ( A. x E* y ph -> ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $= f0_2eu1 f2_2eu1 a_weu f1_2eu1 p_eu5 f0_2eu1 f2_2eu1 p_eu5 f0_2eu1 f2_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 p_exbii f0_2eu1 f2_2eu1 p_eu5 f0_2eu1 f2_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 p_mobii f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo p_anbi12i f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_wmo a_wa f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo a_wa p_bitri f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo p_simprbi f0_2eu1 f2_2eu1 a_wmo f1_2eu1 p_sp f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wex p_anim2i f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa p_ancoms f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex a_wa f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 p_moimi f0_2eu1 f2_2eu1 a_wmo f1_2eu1 p_nfa1 f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 p_moanim f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex a_wa f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo a_wi p_sylib f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo p_ancrd f0_2eu1 f1_2eu1 f2_2eu1 p_2moswap f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo p_com12 f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo p_imdistani f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa p_syl6 f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f0_2eu1 f2_2eu1 a_wmo a_wa f1_2eu1 a_wmo f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa a_wi p_syl f0_2eu1 f1_2eu1 f2_2eu1 p_2eu2ex f0_2eu1 f1_2eu1 f2_2eu1 p_2eu2ex f0_2eu1 f1_2eu1 f2_2eu1 p_excom f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex p_sylib f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex p_jca f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex a_wa p_jctild f0_2eu1 f2_2eu1 a_wex f1_2eu1 p_eu5 f0_2eu1 f1_2eu1 a_wex f2_2eu1 p_eu5 f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo a_wa f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_weu f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa p_anbi12i f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo p_an4 f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_weu f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_weu a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo a_wa f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa a_wa p_bitri f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wex f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wex a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_wmo f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_wmo a_wa a_wa f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_weu f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_weu a_wa p_syl6ibr f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_weu f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_weu a_wa p_com12 f0_2eu1 f1_2eu1 f2_2eu1 p_2exeu f0_2eu1 f2_2eu1 a_wmo f1_2eu1 a_wal f0_2eu1 f2_2eu1 a_weu f1_2eu1 a_weu f0_2eu1 f2_2eu1 a_wex f1_2eu1 a_weu f0_2eu1 f1_2eu1 a_wex f2_2eu1 a_weu a_wa p_impbid1 $.
$}

$(Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2eu2 $f wff ph $.
	f1_2eu2 $f set x $.
	f2_2eu2 $f set y $.
	p_2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $= f0_2eu2 f1_2eu2 a_wex f2_2eu2 p_eumo f0_2eu2 f2_2eu2 f1_2eu2 p_2moex f0_2eu2 f1_2eu2 f2_2eu2 p_2eu1 f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_weu p_simpl f0_2eu2 f2_2eu2 a_wmo f1_2eu2 a_wal f0_2eu2 f2_2eu2 a_weu f1_2eu2 a_weu f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_weu a_wa f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu p_syl6bi f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_weu f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_wmo f0_2eu2 f2_2eu2 a_wmo f1_2eu2 a_wal f0_2eu2 f2_2eu2 a_weu f1_2eu2 a_weu f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu a_wi p_3syl f0_2eu2 f1_2eu2 f2_2eu2 p_2exeu f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_weu f0_2eu2 f2_2eu2 a_weu f1_2eu2 a_weu p_expcom f0_2eu2 f1_2eu2 a_wex f2_2eu2 a_weu f0_2eu2 f2_2eu2 a_weu f1_2eu2 a_weu f0_2eu2 f2_2eu2 a_wex f1_2eu2 a_weu p_impbid $.
$}

$(Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)

${
	$v ph x y  $.
	f0_2eu3 $f wff ph $.
	f1_2eu3 $f set x $.
	f2_2eu3 $f set y $.
	p_2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) -> ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $= f0_2eu3 f2_2eu3 p_nfmo1 f0_2eu3 f1_2eu3 a_wmo f0_2eu3 f2_2eu3 a_wmo f2_2eu3 p_19.31 f0_2eu3 f1_2eu3 a_wmo f0_2eu3 f2_2eu3 a_wmo a_wo f2_2eu3 a_wal f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo a_wo f1_2eu3 p_albii f0_2eu3 f1_2eu3 p_nfmo1 f0_2eu3 f1_2eu3 a_wmo f1_2eu3 f2_2eu3 p_nfal f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo f1_2eu3 p_19.32 f0_2eu3 f1_2eu3 a_wmo f0_2eu3 f2_2eu3 a_wmo a_wo f2_2eu3 a_wal f1_2eu3 a_wal f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo a_wo f1_2eu3 a_wal f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal a_wo p_bitri f0_2eu3 f2_2eu3 f1_2eu3 p_2eu1 f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu a_wa p_biimpd f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu p_ancom f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa p_syl6ib f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu p_adantld f0_2eu3 f1_2eu3 f2_2eu3 p_2eu1 f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa p_biimpd f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu p_adantrd f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa a_wi f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal p_jaoi f0_2eu3 f1_2eu3 f2_2eu3 p_2exeu f0_2eu3 f2_2eu3 f1_2eu3 p_2exeu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu p_ancoms f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu p_jca f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal a_wo f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa p_impbid1 f0_2eu3 f1_2eu3 a_wmo f0_2eu3 f2_2eu3 a_wmo a_wo f2_2eu3 a_wal f1_2eu3 a_wal f0_2eu3 f1_2eu3 a_wmo f2_2eu3 a_wal f0_2eu3 f2_2eu3 a_wmo f1_2eu3 a_wal a_wo f0_2eu3 f2_2eu3 a_weu f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_weu f2_2eu3 a_weu a_wa f0_2eu3 f2_2eu3 a_wex f1_2eu3 a_weu f0_2eu3 f1_2eu3 a_wex f2_2eu3 a_weu a_wa a_wb p_sylbi $.
$}

$(This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions.  (Contributed by NM, 3-Dec-2001.) $)

${
	$v ph x y z w  $.
	$d x y z w  $.
	$d z w ph  $.
	f0_2eu4 $f wff ph $.
	f1_2eu4 $f set x $.
	f2_2eu4 $f set y $.
	f3_2eu4 $f set z $.
	f4_2eu4 $f set w $.
	p_2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $= f0_2eu4 f2_2eu4 a_wex f3_2eu4 p_nfv f0_2eu4 f2_2eu4 a_wex f1_2eu4 f3_2eu4 p_eu3 f0_2eu4 f1_2eu4 a_wex f4_2eu4 p_nfv f0_2eu4 f1_2eu4 a_wex f2_2eu4 f4_2eu4 p_eu3 f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_weu f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex a_wa f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_weu f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex a_wa p_anbi12i f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex p_an4 f0_2eu4 f2_2eu4 f1_2eu4 p_excom f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex p_anbi2i f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex p_anidm f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex p_bitri f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f1_2eu4 p_19.26 f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 p_nfa1 f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f1_2eu4 p_19.3 f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal p_anbi2i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq p_jcab f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi a_wa f2_2eu4 p_albii f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 p_19.26 f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi a_wa f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa p_bitri f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa f1_2eu4 p_albii f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 p_19.26 f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa p_bitri f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f1_2eu4 a_wal a_wa f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal p_bitr4i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal f1_2eu4 a_wal a_wa f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal p_bitr2i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f2_2eu4 p_19.26 f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 p_nfa1 f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f2_2eu4 p_19.3 f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 f1_2eu4 p_alcom f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal p_anbi12i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal a_wa f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f2_2eu4 a_wal a_wa f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa p_bitri f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal a_wa f2_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa f1_2eu4 p_albii f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f1_2eu4 a_wal a_wa f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal a_wa f2_2eu4 a_wal f1_2eu4 a_wal p_bitr4i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 p_19.23v f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq f1_2eu4 p_19.23v f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi p_anbi12i f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi a_wa f1_2eu4 f2_2eu4 p_2albii f0_2eu4 f2_2eu4 p_nfe1 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 p_nfv f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 p_nfim f0_2eu4 f1_2eu4 p_nfe1 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq f1_2eu4 p_nfv f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq f1_2eu4 p_nfim f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 f2_2eu4 p_aaan f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f0_2eu4 f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal a_wa f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi a_wa f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa p_3bitri f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa f3_2eu4 f4_2eu4 p_2exbii f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f3_2eu4 f4_2eu4 p_eeanv f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f4_2eu4 a_wex f3_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal a_wa f4_2eu4 a_wex f3_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex a_wa p_bitr2i f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex a_wa f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f4_2eu4 a_wex f3_2eu4 a_wex p_anbi12i f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_weu f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_weu a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex a_wa f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex a_wa a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_wex a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq a_wi f1_2eu4 a_wal f3_2eu4 a_wex f0_2eu4 f1_2eu4 a_wex f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wi f2_2eu4 a_wal f4_2eu4 a_wex a_wa a_wa f0_2eu4 f2_2eu4 a_wex f1_2eu4 a_wex f0_2eu4 f1_2eu4 a_sup_set_class f3_2eu4 a_sup_set_class a_wceq f2_2eu4 a_sup_set_class f4_2eu4 a_sup_set_class a_wceq a_wa a_wi f2_2eu4 a_wal f1_2eu4 a_wal f4_2eu4 a_wex f3_2eu4 a_wex a_wa p_3bitri $.
$}

$(An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") (Contributed by NM, 26-Oct-2003.) $)

${
	$v ph x y z w  $.
	$d x y z w  $.
	$d z w ph  $.
	f0_2eu5 $f wff ph $.
	f1_2eu5 $f set x $.
	f2_2eu5 $f set y $.
	f3_2eu5 $f set z $.
	f4_2eu5 $f set w $.
	p_2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $= f0_2eu5 f1_2eu5 f2_2eu5 p_2eu1 f0_2eu5 f2_2eu5 a_wmo f1_2eu5 a_wal f0_2eu5 f2_2eu5 a_weu f1_2eu5 a_weu f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu a_wa p_pm5.32ri f0_2eu5 f1_2eu5 a_wex f2_2eu5 p_eumo f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_wmo f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu p_adantl f0_2eu5 f2_2eu5 f1_2eu5 p_2moex f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu a_wa f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_wmo f0_2eu5 f2_2eu5 a_wmo f1_2eu5 a_wal p_syl f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu a_wa f0_2eu5 f2_2eu5 a_wmo f1_2eu5 a_wal p_pm4.71i f0_2eu5 f1_2eu5 f2_2eu5 f3_2eu5 f4_2eu5 p_2eu4 f0_2eu5 f2_2eu5 a_weu f1_2eu5 a_weu f0_2eu5 f2_2eu5 a_wmo f1_2eu5 a_wal a_wa f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu a_wa f0_2eu5 f2_2eu5 a_wmo f1_2eu5 a_wal a_wa f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_weu f0_2eu5 f1_2eu5 a_wex f2_2eu5 a_weu a_wa f0_2eu5 f2_2eu5 a_wex f1_2eu5 a_wex f0_2eu5 f1_2eu5 a_sup_set_class f3_2eu5 a_sup_set_class a_wceq f2_2eu5 a_sup_set_class f4_2eu5 a_sup_set_class a_wceq a_wa a_wi f2_2eu5 a_wal f1_2eu5 a_wal f4_2eu5 a_wex f3_2eu5 a_wex a_wa p_3bitr2i $.
$}

$(Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)

${
	$v ph x y z w  $.
	$d x y z w v u  $.
	$d z w v u ph  $.
	f0_2eu6 $f wff ph $.
	f1_2eu6 $f set x $.
	f2_2eu6 $f set y $.
	f3_2eu6 $f set z $.
	f4_2eu6 $f set w $.
	i0_2eu6 $f set v $.
	i1_2eu6 $f set u $.
	p_2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $= f0_2eu6 f1_2eu6 f2_2eu6 f3_2eu6 f4_2eu6 p_2eu4 f0_2eu6 f3_2eu6 p_nfv f0_2eu6 f4_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 p_sbequ12 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_sbequ12 f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq f0_2eu6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb p_sylan9bbr f0_2eu6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f1_2eu6 f2_2eu6 f3_2eu6 f4_2eu6 p_cbvex2 f3_2eu6 i0_2eu6 f1_2eu6 p_equequ2 f4_2eu6 i1_2eu6 f2_2eu6 p_equequ2 f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq p_bi2anan9 f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 p_imbi2d f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f1_2eu6 f2_2eu6 p_2albidv f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f3_2eu6 f4_2eu6 i0_2eu6 i1_2eu6 p_cbvex2v f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f3_2eu6 p_nfv f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f4_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_nfs1v f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 p_nfim f0_2eu6 f2_2eu6 f4_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 f2_2eu6 p_nfsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f2_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f2_2eu6 p_nfim f0_2eu6 f2_2eu6 f4_2eu6 p_sbequ12 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_sbequ12 f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq f0_2eu6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb p_sylan9bbr f1_2eu6 f3_2eu6 i0_2eu6 p_equequ1 f2_2eu6 f4_2eu6 i1_2eu6 p_equequ1 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq p_bi2anan9 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa p_imbi12d f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f1_2eu6 f2_2eu6 f3_2eu6 f4_2eu6 p_cbval2 f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f4_2eu6 a_wal f3_2eu6 a_wal i0_2eu6 i1_2eu6 p_2exbii f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 f4_2eu6 i0_2eu6 i1_2eu6 p_2mo f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal i1_2eu6 a_wex i0_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f4_2eu6 a_wal f3_2eu6 a_wal i1_2eu6 a_wex i0_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f4_2eu6 a_wal f3_2eu6 a_wal p_bitri f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal i1_2eu6 a_wex i0_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f4_2eu6 a_wal f3_2eu6 a_wal p_bitri f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f3_2eu6 f4_2eu6 p_19.29r2 f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f4_2eu6 a_wal f3_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex p_syl2anb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 f2_2eu6 p_2albiim f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal p_ancom f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa p_bitri f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa f3_2eu6 f4_2eu6 p_2exbii f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi i0_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 f1_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 f1_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb f1_2eu6 p_nfan f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 p_nfim f0_2eu6 f2_2eu6 f4_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb f2_2eu6 p_nfan f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f2_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f2_2eu6 p_nfim f0_2eu6 f2_2eu6 i1_2eu6 p_sbequ12 f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 p_sbequ12 f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq f0_2eu6 f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 a_wsb p_sylan9bbr f0_2eu6 f4_2eu6 p_nfv f0_2eu6 f2_2eu6 i1_2eu6 f4_2eu6 p_sbco2 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 p_sbbii f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 p_nfv f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 f3_2eu6 p_sbco2 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 f1_2eu6 f3_2eu6 p_sbcom2 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 p_sbbii f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb p_bitr3i f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb p_bitr3i f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f0_2eu6 f2_2eu6 i1_2eu6 a_wsb f1_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb p_syl6bb f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb p_anbi2d f1_2eu6 i0_2eu6 f3_2eu6 p_equequ2 f2_2eu6 i1_2eu6 f4_2eu6 p_equequ2 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq p_bi2anan9 f1_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa p_imbi12d f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi f1_2eu6 f2_2eu6 i0_2eu6 i1_2eu6 p_cbval2 f3_2eu6 f1_2eu6 p_equcom f4_2eu6 f2_2eu6 p_equcom f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq p_anbi12i f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa p_imbi2i f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa p_impexp f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi a_wi p_bitri f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi a_wi f1_2eu6 f2_2eu6 p_2albii f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 a_wa f3_2eu6 a_sup_set_class f1_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class f2_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2eu6 a_wal f1_2eu6 a_wal p_bitr3i f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 p_nfs1v f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 f2_2eu6 p_nfsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f1_2eu6 f2_2eu6 p_19.21-2 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wi p_bitri f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wi f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb p_anbi2i f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal p_abai f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wi a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa p_bitr4i f0_2eu6 f1_2eu6 f2_2eu6 f3_2eu6 f4_2eu6 p_2sb6 f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal p_anbi1i f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa p_bitri f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa f3_2eu6 f4_2eu6 p_2exbii f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal a_wa f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f4_2eu6 a_wex f3_2eu6 a_wex p_bitr4i f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex a_wa f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f0_2eu6 f2_2eu6 f4_2eu6 a_wsb f1_2eu6 f3_2eu6 a_wsb f4_2eu6 i1_2eu6 a_wsb f3_2eu6 i0_2eu6 a_wsb a_wa f3_2eu6 a_sup_set_class i0_2eu6 a_sup_set_class a_wceq f4_2eu6 a_sup_set_class i1_2eu6 a_sup_set_class a_wceq a_wa a_wi i1_2eu6 a_wal i0_2eu6 a_wal a_wa f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex p_sylibr f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa p_bi2 f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f1_2eu6 f2_2eu6 p_2alimi f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f3_2eu6 f4_2eu6 p_2eximi f0_2eu6 f1_2eu6 f2_2eu6 f3_2eu6 f4_2eu6 p_2exsb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa f0_2eu6 a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex p_sylibr f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa p_bi1 f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f1_2eu6 f2_2eu6 p_2alimi f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f3_2eu6 f4_2eu6 p_2eximi f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex p_jca f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex a_wa f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex p_impbii f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_weu f0_2eu6 f1_2eu6 a_wex f2_2eu6 a_weu a_wa f0_2eu6 f2_2eu6 a_wex f1_2eu6 a_wex f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wi f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex a_wa f0_2eu6 f1_2eu6 a_sup_set_class f3_2eu6 a_sup_set_class a_wceq f2_2eu6 a_sup_set_class f4_2eu6 a_sup_set_class a_wceq a_wa a_wb f2_2eu6 a_wal f1_2eu6 a_wal f4_2eu6 a_wex f3_2eu6 a_wex p_bitri $.
$}

$(Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)

${
	$v ph x y  $.
	f0_2eu7 $f wff ph $.
	f1_2eu7 $f set x $.
	f2_2eu7 $f set y $.
	p_2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E! x E! y ( E. x ph /\ E. y ph ) ) $= f0_2eu7 f1_2eu7 p_nfe1 f0_2eu7 f1_2eu7 a_wex f1_2eu7 f2_2eu7 p_nfeu f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex f1_2eu7 p_euan f0_2eu7 f1_2eu7 a_wex f0_2eu7 f2_2eu7 a_wex p_ancom f0_2eu7 f1_2eu7 a_wex f0_2eu7 f2_2eu7 a_wex a_wa f0_2eu7 f2_2eu7 a_wex f0_2eu7 f1_2eu7 a_wex a_wa f2_2eu7 p_eubii f0_2eu7 f2_2eu7 p_nfe1 f0_2eu7 f2_2eu7 a_wex f0_2eu7 f1_2eu7 a_wex f2_2eu7 p_euan f0_2eu7 f2_2eu7 a_wex f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu p_ancom f0_2eu7 f1_2eu7 a_wex f0_2eu7 f2_2eu7 a_wex a_wa f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex f0_2eu7 f1_2eu7 a_wex a_wa f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu a_wa f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex a_wa p_3bitri f0_2eu7 f1_2eu7 a_wex f0_2eu7 f2_2eu7 a_wex a_wa f2_2eu7 a_weu f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex a_wa f1_2eu7 p_eubii f0_2eu7 f2_2eu7 a_wex f1_2eu7 a_weu f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu p_ancom f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex a_wa f1_2eu7 a_weu f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex f1_2eu7 a_weu a_wa f0_2eu7 f1_2eu7 a_wex f0_2eu7 f2_2eu7 a_wex a_wa f2_2eu7 a_weu f1_2eu7 a_weu f0_2eu7 f2_2eu7 a_wex f1_2eu7 a_weu f0_2eu7 f1_2eu7 a_wex f2_2eu7 a_weu a_wa p_3bitr4ri $.
$}

$(Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  (Contributed by NM,
     20-Feb-2005.) $)

${
	$v ph x y  $.
	f0_2eu8 $f wff ph $.
	f1_2eu8 $f set x $.
	f2_2eu8 $f set y $.
	p_2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <-> E! x E! y ( E! x ph /\ E. y ph ) ) $= f0_2eu8 f2_2eu8 f1_2eu8 p_2eu2 f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f1_2eu8 a_wex f2_2eu8 a_weu p_pm5.32i f0_2eu8 f1_2eu8 p_nfeu1 f0_2eu8 f1_2eu8 a_weu f1_2eu8 f2_2eu8 p_nfeu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex f1_2eu8 p_euan f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex p_ancom f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f0_2eu8 f2_2eu8 a_wex f0_2eu8 f1_2eu8 a_weu a_wa f2_2eu8 p_eubii f0_2eu8 f2_2eu8 p_nfe1 f0_2eu8 f2_2eu8 a_wex f0_2eu8 f1_2eu8 a_weu f2_2eu8 p_euan f0_2eu8 f2_2eu8 a_wex f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu p_ancom f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex f0_2eu8 f1_2eu8 a_weu a_wa f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu a_wa f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa p_3bitri f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f2_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f1_2eu8 p_eubii f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu p_ancom f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu a_wa f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f2_2eu8 a_weu f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu a_wa p_3bitr4ri f0_2eu8 f1_2eu8 f2_2eu8 p_2eu7 f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_weu f2_2eu8 a_weu a_wa f0_2eu8 f2_2eu8 a_wex f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_wex f2_2eu8 a_weu a_wa f0_2eu8 f1_2eu8 a_weu f0_2eu8 f2_2eu8 a_wex a_wa f2_2eu8 a_weu f1_2eu8 a_weu f0_2eu8 f1_2eu8 a_wex f0_2eu8 f2_2eu8 a_wex a_wa f2_2eu8 a_weu f1_2eu8 a_weu p_3bitr3ri $.
$}

$(Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_euequ1 $f set x $.
	f1_euequ1 $f set y $.
	i0_euequ1 $f set z $.
	p_euequ1 $p |- E! x x = y $= f0_euequ1 f1_euequ1 p_a9ev f0_euequ1 i0_euequ1 f1_euequ1 p_equtr2 f0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq i0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq a_wa f0_euequ1 a_sup_set_class i0_euequ1 a_sup_set_class a_wceq a_wi f0_euequ1 i0_euequ1 p_gen2 f0_euequ1 i0_euequ1 f1_euequ1 p_equequ1 f0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq i0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq f0_euequ1 i0_euequ1 p_eu4 f0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq f0_euequ1 a_weu f0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq f0_euequ1 a_wex f0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq i0_euequ1 a_sup_set_class f1_euequ1 a_sup_set_class a_wceq a_wa f0_euequ1 a_sup_set_class i0_euequ1 a_sup_set_class a_wceq a_wi i0_euequ1 a_wal f0_euequ1 a_wal p_mpbir2an $.
$}

$(Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.) $)

${
	$v x y  $.
	$d x y  $.
	f0_exists1 $f set x $.
	f1_exists1 $f set y $.
	p_exists1 $p |- ( E! x x = x <-> A. x x = y ) $= f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 f1_exists1 a_df-eu f0_exists1 p_equid f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq p_tbt f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq p_bicom f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq a_wb f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq a_wb p_bitri f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq a_wb f0_exists1 p_albii f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_wal f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq a_wb f0_exists1 a_wal f1_exists1 p_exbii f0_exists1 f1_exists1 f1_exists1 p_nfae f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_wal f1_exists1 p_19.9 f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_weu f0_exists1 a_sup_set_class f0_exists1 a_sup_set_class a_wceq f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq a_wb f0_exists1 a_wal f1_exists1 a_wex f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_wal f1_exists1 a_wex f0_exists1 a_sup_set_class f1_exists1 a_sup_set_class a_wceq f0_exists1 a_wal p_3bitr2i $.
$}

$(A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph x  $.
	$d x y  $.
	f0_exists2 $f wff ph $.
	f1_exists2 $f set x $.
	i0_exists2 $f set y $.
	p_exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $= f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 p_nfeu1 f0_exists2 f1_exists2 p_nfa1 f1_exists2 i0_exists2 p_exists1 f0_exists2 f1_exists2 i0_exists2 p_ax16 f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu f1_exists2 a_sup_set_class i0_exists2 a_sup_set_class a_wceq f1_exists2 a_wal f0_exists2 f0_exists2 f1_exists2 a_wal a_wi p_sylbi f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu f0_exists2 f0_exists2 f1_exists2 a_wal f1_exists2 p_exlimd f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu f0_exists2 f1_exists2 a_wex f0_exists2 f1_exists2 a_wal p_com12 f0_exists2 f1_exists2 p_alex f0_exists2 f1_exists2 a_wex f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu f0_exists2 f1_exists2 a_wal f0_exists2 a_wn f1_exists2 a_wex a_wn p_syl6ib f0_exists2 f1_exists2 a_wex f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu f0_exists2 a_wn f1_exists2 a_wex p_con2d f0_exists2 f1_exists2 a_wex f0_exists2 a_wn f1_exists2 a_wex f1_exists2 a_sup_set_class f1_exists2 a_sup_set_class a_wceq f1_exists2 a_weu a_wn p_imp $.
$}


