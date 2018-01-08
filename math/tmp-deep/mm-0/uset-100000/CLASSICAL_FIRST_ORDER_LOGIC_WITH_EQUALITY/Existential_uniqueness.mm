$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes).mm $]
$( #*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
               Existential uniqueness

#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)
$( Declare new symbols needed for uniqueness notation. $)
$c E!  $.
$( Backwards E exclamation point. $)
$c E*  $.
$( Backwards E superscript *. $)
$( Extend wff definition to include existential uniqueness ("there exists a
     unique ` x ` such that ` ph ` "). $)
${
	fweu_0 $f wff ph $.
	fweu_1 $f set x $.
	weu $a wff E! x ph $.
$}
$( Extend wff definition to include uniqueness ("there exists at most one
     ` x ` such that ` ph ` "). $)
${
	fwmo_0 $f wff ph $.
	fwmo_1 $f set x $.
	wmo $a wff E* x ph $.
$}
$( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  See
       ~ eujustALT for a proof that provides an example of how it can be
       achieved through the use of ~ dvelim .  (Contributed by NM,
       11-Mar-2010.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$d w x y $.
	$d x z $.
	$d y ph $.
	$d w z ph $.
	ieujust_0 $f set w $.
	feujust_0 $f wff ph $.
	feujust_1 $f set x $.
	feujust_2 $f set y $.
	feujust_3 $f set z $.
	eujust $p |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) ) $= feujust_0 feujust_1 cv feujust_2 cv wceq wb feujust_1 wal feujust_2 wex feujust_0 feujust_1 cv ieujust_0 cv wceq wb feujust_1 wal ieujust_0 wex feujust_0 feujust_1 cv feujust_3 cv wceq wb feujust_1 wal feujust_3 wex feujust_0 feujust_1 cv feujust_2 cv wceq wb feujust_1 wal feujust_0 feujust_1 cv ieujust_0 cv wceq wb feujust_1 wal feujust_2 ieujust_0 feujust_2 cv ieujust_0 cv wceq feujust_0 feujust_1 cv feujust_2 cv wceq wb feujust_0 feujust_1 cv ieujust_0 cv wceq wb feujust_1 feujust_2 cv ieujust_0 cv wceq feujust_1 cv feujust_2 cv wceq feujust_1 cv ieujust_0 cv wceq feujust_0 feujust_2 ieujust_0 feujust_1 equequ2 bibi2d albidv cbvexv feujust_0 feujust_1 cv ieujust_0 cv wceq wb feujust_1 wal feujust_0 feujust_1 cv feujust_3 cv wceq wb feujust_1 wal ieujust_0 feujust_3 ieujust_0 cv feujust_3 cv wceq feujust_0 feujust_1 cv ieujust_0 cv wceq wb feujust_0 feujust_1 cv feujust_3 cv wceq wb feujust_1 ieujust_0 cv feujust_3 cv wceq feujust_1 cv ieujust_0 cv wceq feujust_1 cv feujust_3 cv wceq feujust_0 ieujust_0 feujust_3 feujust_1 equequ2 bibi2d albidv cbvexv bitri $.
$}
$( A soundness justification theorem for ~ df-eu , showing that the
       definition is equivalent to itself with its dummy variable renamed.
       Note that ` y ` and ` z ` needn't be distinct variables.  While this
       isn't strictly necessary for soundness, the proof provides an example of
       how it can be achieved through the use of ~ dvelim .  (Contributed by
       NM, 11-Mar-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d w x y $.
	$d x z $.
	$d y ph $.
	$d w z ph $.
	ieujustALT_0 $f set w $.
	feujustALT_0 $f wff ph $.
	feujustALT_1 $f set x $.
	feujustALT_2 $f set y $.
	feujustALT_3 $f set z $.
	eujustALT $p |- ( E. y A. x ( ph <-> x = y ) <-> E. z A. x ( ph <-> x = z ) ) $= feujustALT_2 feujustALT_3 weq feujustALT_2 wal feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_2 wex feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal feujustALT_3 wex wb feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal feujustALT_2 feujustALT_3 feujustALT_2 feujustALT_3 weq feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wb feujustALT_2 feujustALT_2 feujustALT_3 weq feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 feujustALT_2 feujustALT_3 weq feujustALT_1 feujustALT_2 weq feujustALT_1 feujustALT_3 weq feujustALT_0 feujustALT_2 feujustALT_3 feujustALT_1 equequ2 bibi2d albidv sps drex1 feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_2 wal wn feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn feujustALT_3 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_2 wex feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal feujustALT_3 wex feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_2 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn feujustALT_3 wal feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_3 wal feujustALT_2 wal feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_2 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn feujustALT_3 wal wb feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_3 wal feujustALT_2 feujustALT_2 feujustALT_3 feujustALT_2 hbnae feujustALT_2 feujustALT_3 feujustALT_3 hbnae alrimih feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn feujustALT_2 feujustALT_3 feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_3 wal wi feujustALT_3 feujustALT_2 feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal wn feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_3 feujustALT_2 ieujustALT_0 feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal wn feujustALT_3 ax-17 ieujustALT_0 feujustALT_2 weq feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal ieujustALT_0 feujustALT_2 weq feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 ieujustALT_0 feujustALT_2 weq feujustALT_1 ieujustALT_0 weq feujustALT_1 feujustALT_2 weq feujustALT_0 ieujustALT_0 feujustALT_2 feujustALT_1 equequ2 bibi2d albidv notbid dvelim naecoms feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal wn feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn feujustALT_2 feujustALT_3 ieujustALT_0 feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal wn feujustALT_2 ax-17 ieujustALT_0 feujustALT_3 weq feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_1 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal ieujustALT_0 feujustALT_3 weq feujustALT_0 feujustALT_1 ieujustALT_0 weq wb feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 ieujustALT_0 feujustALT_3 weq feujustALT_1 ieujustALT_0 weq feujustALT_1 feujustALT_3 weq feujustALT_0 ieujustALT_0 feujustALT_3 feujustALT_1 equequ2 bibi2d albidv notbid dvelim feujustALT_2 feujustALT_3 weq feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal wn feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal wn wb wi feujustALT_2 feujustALT_3 weq feujustALT_2 wal wn feujustALT_2 feujustALT_3 weq feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal feujustALT_2 feujustALT_3 weq feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 feujustALT_2 feujustALT_3 weq feujustALT_1 feujustALT_2 weq feujustALT_1 feujustALT_3 weq feujustALT_0 feujustALT_2 feujustALT_3 feujustALT_1 equequ2 bibi2d albidv notbid a1i cbv2h syl notbid feujustALT_0 feujustALT_1 feujustALT_2 weq wb feujustALT_1 wal feujustALT_2 df-ex feujustALT_0 feujustALT_1 feujustALT_3 weq wb feujustALT_1 wal feujustALT_3 df-ex 3bitr4g pm2.61i $.
$}
$( Define existential uniqueness, i.e.  "there exists exactly one ` x `
       such that ` ph ` ."  Definition 10.1 of [BellMachover] p. 97; also
       Definition *14.02 of [WhiteheadRussell] p. 175.  Other possible
       definitions are given by ~ eu1 , ~ eu2 , ~ eu3 , and ~ eu5 (which in
       some cases we show with a hypothesis ` ph -> A. y ph ` in place of a
       distinct variable condition on ` y ` and ` ph ` ).  Double uniqueness is
       tricky: ` E! x E! y ph ` does not mean "exactly one ` x ` and one
       ` y ` " (see ~ 2eu4 ).  (Contributed by NM, 12-Aug-1993.) $)
${
	$d x y $.
	$d y ph $.
	fdf-eu_0 $f wff ph $.
	fdf-eu_1 $f set x $.
	fdf-eu_2 $f set y $.
	df-eu $a |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $.
$}
$( Define "there exists at most one ` x ` such that ` ph ` ."  Here we define
     it in terms of existential uniqueness.  Notation of [BellMachover] p. 460,
     whose definition we show as ~ mo3 .  For other possible definitions see
     ~ mo2 and ~ mo4 .  (Contributed by NM, 8-Mar-1995.) $)
${
	fdf-mo_0 $f wff ph $.
	fdf-mo_1 $f set x $.
	df-mo $a |- ( E* x ph <-> ( E. x ph -> E! x ph ) ) $.
$}
$( A version of the existential uniqueness definition with a hypothesis
       instead of a distinct variable condition.  (Contributed by NM,
       12-Aug-1993.) $)
${
	$d x y z $.
	$d ph z $.
	ieuf_0 $f set z $.
	feuf_0 $f wff ph $.
	feuf_1 $f set x $.
	feuf_2 $f set y $.
	eeuf_0 $e |- F/ y ph $.
	euf $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $= feuf_0 feuf_1 weu feuf_0 feuf_1 cv ieuf_0 cv wceq wb feuf_1 wal ieuf_0 wex feuf_0 feuf_1 cv feuf_2 cv wceq wb feuf_1 wal feuf_2 wex feuf_0 feuf_1 ieuf_0 df-eu feuf_0 feuf_1 cv ieuf_0 cv wceq wb feuf_1 wal feuf_0 feuf_1 cv feuf_2 cv wceq wb feuf_1 wal ieuf_0 feuf_2 feuf_0 feuf_1 cv ieuf_0 cv wceq wb feuf_2 feuf_1 feuf_0 feuf_1 cv ieuf_0 cv wceq feuf_2 eeuf_0 feuf_1 cv ieuf_0 cv wceq feuf_2 nfv nfbi nfal feuf_0 feuf_1 cv feuf_2 cv wceq wb ieuf_0 feuf_1 feuf_0 feuf_1 cv feuf_2 cv wceq ieuf_0 feuf_0 ieuf_0 nfv feuf_1 cv feuf_2 cv wceq ieuf_0 nfv nfbi nfal ieuf_0 cv feuf_2 cv wceq feuf_0 feuf_1 cv ieuf_0 cv wceq wb feuf_0 feuf_1 cv feuf_2 cv wceq wb feuf_1 ieuf_0 cv feuf_2 cv wceq feuf_1 cv ieuf_0 cv wceq feuf_1 cv feuf_2 cv wceq feuf_0 ieuf_0 feuf_2 feuf_1 equequ2 bibi2d albidv cbvex bitri $.
$}
$( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
${
	$d x y $.
	$d y ph $.
	$d y ps $.
	$d y ch $.
	ieubid_0 $f set y $.
	feubid_0 $f wff ph $.
	feubid_1 $f wff ps $.
	feubid_2 $f wff ch $.
	feubid_3 $f set x $.
	eeubid_0 $e |- F/ x ph $.
	eeubid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	eubid $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $= feubid_0 feubid_1 feubid_3 cv ieubid_0 cv wceq wb feubid_3 wal ieubid_0 wex feubid_2 feubid_3 cv ieubid_0 cv wceq wb feubid_3 wal ieubid_0 wex feubid_1 feubid_3 weu feubid_2 feubid_3 weu feubid_0 feubid_1 feubid_3 cv ieubid_0 cv wceq wb feubid_3 wal feubid_2 feubid_3 cv ieubid_0 cv wceq wb feubid_3 wal ieubid_0 feubid_0 feubid_1 feubid_3 cv ieubid_0 cv wceq wb feubid_2 feubid_3 cv ieubid_0 cv wceq wb feubid_3 eeubid_0 feubid_0 feubid_1 feubid_2 feubid_3 cv ieubid_0 cv wceq eeubid_1 bibi1d albid exbidv feubid_1 feubid_3 ieubid_0 df-eu feubid_2 feubid_3 ieubid_0 df-eu 3bitr4g $.
$}
$( Formula-building rule for uniqueness quantifier (deduction rule).
       (Contributed by NM, 9-Jul-1994.) $)
${
	$d x ph $.
	feubidv_0 $f wff ph $.
	feubidv_1 $f wff ps $.
	feubidv_2 $f wff ch $.
	feubidv_3 $f set x $.
	eeubidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	eubidv $p |- ( ph -> ( E! x ps <-> E! x ch ) ) $= feubidv_0 feubidv_1 feubidv_2 feubidv_3 feubidv_0 feubidv_3 nfv eeubidv_0 eubid $.
$}
$( Introduce uniqueness quantifier to both sides of an equivalence.
       (Contributed by NM, 9-Jul-1994.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
${
	feubii_0 $f wff ph $.
	feubii_1 $f wff ps $.
	feubii_2 $f set x $.
	eeubii_0 $e |- ( ph <-> ps ) $.
	eubii $p |- ( E! x ph <-> E! x ps ) $= feubii_0 feubii_2 weu feubii_1 feubii_2 weu wb wtru feubii_0 feubii_1 feubii_2 feubii_0 feubii_1 wb wtru eeubii_0 a1i eubidv trud $.
$}
$( Bound-variable hypothesis builder for uniqueness.  (Contributed by NM,
       9-Jul-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$d x y $.
	$d y ph $.
	infeu1_0 $f set y $.
	fnfeu1_0 $f wff ph $.
	fnfeu1_1 $f set x $.
	nfeu1 $p |- F/ x E! x ph $= fnfeu1_0 fnfeu1_1 weu fnfeu1_0 fnfeu1_1 cv infeu1_0 cv wceq wb fnfeu1_1 wal infeu1_0 wex fnfeu1_1 fnfeu1_0 fnfeu1_1 infeu1_0 df-eu fnfeu1_0 fnfeu1_1 cv infeu1_0 cv wceq wb fnfeu1_1 wal fnfeu1_1 infeu1_0 fnfeu1_0 fnfeu1_1 cv infeu1_0 cv wceq wb fnfeu1_1 nfa1 nfex nfxfr $.
$}
$( Bound-variable hypothesis builder for "at most one."  (Contributed by NM,
     8-Mar-1995.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfmo1_0 $f wff ph $.
	fnfmo1_1 $f set x $.
	nfmo1 $p |- F/ x E* x ph $= fnfmo1_0 fnfmo1_1 wmo fnfmo1_0 fnfmo1_1 wex fnfmo1_0 fnfmo1_1 weu wi fnfmo1_1 fnfmo1_0 fnfmo1_1 df-mo fnfmo1_0 fnfmo1_1 wex fnfmo1_0 fnfmo1_1 weu fnfmo1_1 fnfmo1_0 fnfmo1_1 nfe1 fnfmo1_0 fnfmo1_1 nfeu1 nfim nfxfr $.
$}
$( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
${
	$d y z $.
	$d z ph $.
	$d z ps $.
	infeud2_0 $f set z $.
	fnfeud2_0 $f wff ph $.
	fnfeud2_1 $f wff ps $.
	fnfeud2_2 $f set x $.
	fnfeud2_3 $f set y $.
	enfeud2_0 $e |- F/ y ph $.
	enfeud2_1 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	nfeud2 $p |- ( ph -> F/ x E! y ps ) $= fnfeud2_1 fnfeud2_3 weu fnfeud2_1 fnfeud2_3 cv infeud2_0 cv wceq wb fnfeud2_3 wal infeud2_0 wex fnfeud2_0 fnfeud2_2 fnfeud2_1 fnfeud2_3 infeud2_0 df-eu fnfeud2_0 fnfeud2_1 fnfeud2_3 cv infeud2_0 cv wceq wb fnfeud2_3 wal fnfeud2_2 infeud2_0 fnfeud2_0 infeud2_0 nfv fnfeud2_0 fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn wa fnfeud2_1 fnfeud2_3 cv infeud2_0 cv wceq wb fnfeud2_2 fnfeud2_3 fnfeud2_0 fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn fnfeud2_3 enfeud2_0 fnfeud2_2 infeud2_0 fnfeud2_3 nfnae nfan fnfeud2_0 fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn wa fnfeud2_2 cv fnfeud2_3 cv wceq fnfeud2_2 wal wn wa fnfeud2_1 fnfeud2_3 cv infeud2_0 cv wceq fnfeud2_2 fnfeud2_0 fnfeud2_2 cv fnfeud2_3 cv wceq fnfeud2_2 wal wn fnfeud2_1 fnfeud2_2 wnf fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn enfeud2_1 adantlr fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn fnfeud2_2 cv fnfeud2_3 cv wceq fnfeud2_2 wal wn fnfeud2_3 cv infeud2_0 cv wceq fnfeud2_2 wnf fnfeud2_0 fnfeud2_2 cv fnfeud2_3 cv wceq fnfeud2_2 wal wn fnfeud2_2 cv infeud2_0 cv wceq fnfeud2_2 wal wn fnfeud2_3 cv infeud2_0 cv wceq fnfeud2_2 wnf fnfeud2_3 infeud2_0 fnfeud2_2 nfeqf ancoms adantll nfbid nfald2 nfexd2 nfxfrd $.
$}
$( Bound-variable hypothesis builder for uniqueness.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
${
	fnfmod2_0 $f wff ph $.
	fnfmod2_1 $f wff ps $.
	fnfmod2_2 $f set x $.
	fnfmod2_3 $f set y $.
	enfmod2_0 $e |- F/ y ph $.
	enfmod2_1 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	nfmod2 $p |- ( ph -> F/ x E* y ps ) $= fnfmod2_1 fnfmod2_3 wmo fnfmod2_1 fnfmod2_3 wex fnfmod2_1 fnfmod2_3 weu wi fnfmod2_0 fnfmod2_2 fnfmod2_1 fnfmod2_3 df-mo fnfmod2_0 fnfmod2_1 fnfmod2_3 wex fnfmod2_1 fnfmod2_3 weu fnfmod2_2 fnfmod2_0 fnfmod2_1 fnfmod2_2 fnfmod2_3 enfmod2_0 enfmod2_1 nfexd2 fnfmod2_0 fnfmod2_1 fnfmod2_2 fnfmod2_3 enfmod2_0 enfmod2_1 nfeud2 nfimd nfxfrd $.
$}
$( Deduction version of ~ nfeu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	fnfeud_0 $f wff ph $.
	fnfeud_1 $f wff ps $.
	fnfeud_2 $f set x $.
	fnfeud_3 $f set y $.
	enfeud_0 $e |- F/ y ph $.
	enfeud_1 $e |- ( ph -> F/ x ps ) $.
	nfeud $p |- ( ph -> F/ x E! y ps ) $= fnfeud_0 fnfeud_1 fnfeud_2 fnfeud_3 enfeud_0 fnfeud_0 fnfeud_1 fnfeud_2 wnf fnfeud_2 cv fnfeud_3 cv wceq fnfeud_2 wal wn enfeud_1 adantr nfeud2 $.
$}
$( Bound-variable hypothesis builder for "at most one."  (Contributed by
       Mario Carneiro, 14-Nov-2016.) $)
${
	fnfmod_0 $f wff ph $.
	fnfmod_1 $f wff ps $.
	fnfmod_2 $f set x $.
	fnfmod_3 $f set y $.
	enfmod_0 $e |- F/ y ph $.
	enfmod_1 $e |- ( ph -> F/ x ps ) $.
	nfmod $p |- ( ph -> F/ x E* y ps ) $= fnfmod_0 fnfmod_1 fnfmod_2 fnfmod_3 enfmod_0 fnfmod_0 fnfmod_1 fnfmod_2 wnf fnfmod_2 cv fnfmod_3 cv wceq fnfmod_2 wal wn enfmod_1 adantr nfmod2 $.
$}
$( Bound-variable hypothesis builder for "at most one."  Note that ` x `
       and ` y ` needn't be distinct (this makes the proof more difficult).
       (Contributed by NM, 8-Mar-1995.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	fnfeu_0 $f wff ph $.
	fnfeu_1 $f set x $.
	fnfeu_2 $f set y $.
	enfeu_0 $e |- F/ x ph $.
	nfeu $p |- F/ x E! y ph $= fnfeu_0 fnfeu_2 weu fnfeu_1 wnf wtru fnfeu_0 fnfeu_1 fnfeu_2 fnfeu_2 nftru fnfeu_0 fnfeu_1 wnf wtru enfeu_0 a1i nfeud trud $.
$}
$( Bound-variable hypothesis builder for "at most one."  (Contributed by
       NM, 9-Mar-1995.) $)
${
	fnfmo_0 $f wff ph $.
	fnfmo_1 $f set x $.
	fnfmo_2 $f set y $.
	enfmo_0 $e |- F/ x ph $.
	nfmo $p |- F/ x E* y ph $= fnfmo_0 fnfmo_2 wmo fnfmo_1 wnf wtru fnfmo_0 fnfmo_1 fnfmo_2 fnfmo_2 nftru fnfmo_0 fnfmo_1 wnf wtru enfmo_0 a1i nfmod trud $.
$}
$( Variable substitution in uniqueness quantifier.  (Contributed by NM,
       7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$d w y z $.
	$d ph z w $.
	$d w x z $.
	isb8eu_0 $f set z $.
	isb8eu_1 $f set w $.
	fsb8eu_0 $f wff ph $.
	fsb8eu_1 $f set x $.
	fsb8eu_2 $f set y $.
	esb8eu_0 $e |- F/ y ph $.
	sb8eu $p |- ( E! x ph <-> E! y [ y / x ] ph ) $= fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 wal isb8eu_0 wex fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 cv isb8eu_0 cv wceq wb fsb8eu_2 wal isb8eu_0 wex fsb8eu_0 fsb8eu_1 weu fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 weu fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 wal fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 cv isb8eu_0 cv wceq wb fsb8eu_2 wal isb8eu_0 fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 wal fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 isb8eu_1 wsb isb8eu_1 wal fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 wal fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 cv isb8eu_0 cv wceq wb fsb8eu_2 wal fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 isb8eu_1 fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb isb8eu_1 nfv sb8 fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 isb8eu_1 wsb fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 fsb8eu_2 wsb isb8eu_1 fsb8eu_2 fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 isb8eu_1 wsb fsb8eu_0 fsb8eu_1 isb8eu_1 wsb fsb8eu_1 cv isb8eu_0 cv wceq fsb8eu_1 isb8eu_1 wsb wb fsb8eu_2 fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq fsb8eu_1 isb8eu_1 sbbi fsb8eu_0 fsb8eu_1 isb8eu_1 wsb fsb8eu_1 cv isb8eu_0 cv wceq fsb8eu_1 isb8eu_1 wsb fsb8eu_2 fsb8eu_0 fsb8eu_1 isb8eu_1 fsb8eu_2 esb8eu_0 nfsb fsb8eu_1 cv isb8eu_0 cv wceq fsb8eu_1 isb8eu_1 wsb isb8eu_1 cv isb8eu_0 cv wceq fsb8eu_2 isb8eu_1 fsb8eu_1 isb8eu_0 equsb3 isb8eu_1 cv isb8eu_0 cv wceq fsb8eu_2 nfv nfxfr nfbi nfxfr fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 fsb8eu_2 wsb isb8eu_1 nfv fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb isb8eu_1 fsb8eu_2 fsb8eu_1 sbequ cbval fsb8eu_0 fsb8eu_1 cv isb8eu_0 cv wceq wb fsb8eu_1 fsb8eu_2 wsb fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 cv isb8eu_0 cv wceq wb fsb8eu_2 fsb8eu_1 cv isb8eu_0 cv wceq fsb8eu_2 cv isb8eu_0 cv wceq fsb8eu_0 fsb8eu_1 fsb8eu_2 fsb8eu_2 fsb8eu_1 isb8eu_0 equsb3 sblbis albii 3bitri exbii fsb8eu_0 fsb8eu_1 isb8eu_0 df-eu fsb8eu_0 fsb8eu_1 fsb8eu_2 wsb fsb8eu_2 isb8eu_0 df-eu 3bitr4i $.
$}
$( Variable substitution in uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)
${
	fsb8mo_0 $f wff ph $.
	fsb8mo_1 $f set x $.
	fsb8mo_2 $f set y $.
	esb8mo_0 $e |- F/ y ph $.
	sb8mo $p |- ( E* x ph <-> E* y [ y / x ] ph ) $= fsb8mo_0 fsb8mo_1 wex fsb8mo_0 fsb8mo_1 weu wi fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 wex fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 weu wi fsb8mo_0 fsb8mo_1 wmo fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 wmo fsb8mo_0 fsb8mo_1 wex fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 wex fsb8mo_0 fsb8mo_1 weu fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 weu fsb8mo_0 fsb8mo_1 fsb8mo_2 esb8mo_0 sb8e fsb8mo_0 fsb8mo_1 fsb8mo_2 esb8mo_0 sb8eu imbi12i fsb8mo_0 fsb8mo_1 df-mo fsb8mo_0 fsb8mo_1 fsb8mo_2 wsb fsb8mo_2 df-mo 3bitr4i $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 25-Nov-1994.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	fcbveu_0 $f wff ph $.
	fcbveu_1 $f wff ps $.
	fcbveu_2 $f set x $.
	fcbveu_3 $f set y $.
	ecbveu_0 $e |- F/ y ph $.
	ecbveu_1 $e |- F/ x ps $.
	ecbveu_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbveu $p |- ( E! x ph <-> E! y ps ) $= fcbveu_0 fcbveu_2 weu fcbveu_0 fcbveu_2 fcbveu_3 wsb fcbveu_3 weu fcbveu_1 fcbveu_3 weu fcbveu_0 fcbveu_2 fcbveu_3 ecbveu_0 sb8eu fcbveu_0 fcbveu_2 fcbveu_3 wsb fcbveu_1 fcbveu_3 fcbveu_0 fcbveu_1 fcbveu_2 fcbveu_3 ecbveu_1 ecbveu_2 sbie eubii bitri $.
$}
$( An alternate way to express uniqueness used by some authors.  Exercise
       2(b) of [Margaris] p. 110.  (Contributed by NM, 20-Aug-1993.)  (Revised
       by Mario Carneiro, 7-Oct-2016.) $)
${
	$d x y $.
	feu1_0 $f wff ph $.
	feu1_1 $f set x $.
	feu1_2 $f set y $.
	eeu1_0 $e |- F/ y ph $.
	eu1 $p |- ( E! x ph <-> E. x ( ph /\ A. y ( [ y / x ] ph -> x = y ) ) ) $= feu1_0 feu1_1 feu1_2 wsb feu1_2 weu feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wb feu1_2 wal feu1_1 wex feu1_0 feu1_1 weu feu1_0 feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal wa feu1_1 wex feu1_0 feu1_1 feu1_2 wsb feu1_2 feu1_1 feu1_0 feu1_1 feu1_2 nfs1v euf feu1_0 feu1_1 feu1_2 eeu1_0 sb8eu feu1_0 feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal wa feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wb feu1_2 wal feu1_1 feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal feu1_0 wa feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wi feu1_2 wal feu1_2 cv feu1_1 cv wceq feu1_0 feu1_1 feu1_2 wsb wi feu1_2 wal wa feu1_0 feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal wa feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wb feu1_2 wal feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wi feu1_2 wal feu1_0 feu1_2 cv feu1_1 cv wceq feu1_0 feu1_1 feu1_2 wsb wi feu1_2 wal feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq wi feu1_2 feu1_1 cv feu1_2 cv wceq feu1_2 cv feu1_1 cv wceq feu1_0 feu1_1 feu1_2 wsb feu1_1 feu1_2 equcom imbi2i albii feu1_0 feu1_1 feu1_2 eeu1_0 sb6rf anbi12i feu1_0 feu1_0 feu1_1 feu1_2 wsb feu1_1 cv feu1_2 cv wceq wi feu1_2 wal ancom feu1_0 feu1_1 feu1_2 wsb feu1_2 cv feu1_1 cv wceq feu1_2 albiim 3bitr4i exbii 3bitr4i $.
$}
$( Equivalent definitions of "there exists at most one."  (Contributed by
       NM, 7-Aug-1994.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$d x y z $.
	$d ph z $.
	imo_0 $f set z $.
	fmo_0 $f wff ph $.
	fmo_1 $f set x $.
	fmo_2 $f set y $.
	emo_0 $e |- F/ y ph $.
	mo $p |- ( E. y A. x ( ph -> x = y ) <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 wex fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 wex fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal imo_0 wex fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal imo_0 fmo_2 fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_2 fmo_1 fmo_0 fmo_1 cv imo_0 cv wceq fmo_2 emo_0 fmo_1 cv imo_0 cv wceq fmo_2 nfv nfim nfal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal imo_0 nfv imo_0 cv fmo_2 cv wceq fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 imo_0 cv fmo_2 cv wceq fmo_1 cv imo_0 cv wceq fmo_1 cv fmo_2 cv wceq fmo_0 imo_0 fmo_2 fmo_1 equequ2 imbi2d albidv cbvex fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal imo_0 fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi wa fmo_2 wal fmo_1 wal fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi fmo_2 wal wa fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi wa fmo_2 wal fmo_1 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_1 wal fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi fmo_2 wal fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi fmo_1 fmo_2 fmo_0 fmo_1 cv imo_0 cv wceq fmo_2 emo_0 fmo_1 cv imo_0 cv wceq fmo_2 nfv nfim fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq fmo_1 fmo_0 fmo_1 fmo_2 emo_0 nfs1 fmo_2 cv imo_0 cv wceq fmo_1 nfv nfim fmo_1 cv fmo_2 cv wceq fmo_0 fmo_1 fmo_2 wsb fmo_0 fmo_1 cv imo_0 cv wceq fmo_2 cv imo_0 cv wceq fmo_0 fmo_1 fmo_2 sbequ2 fmo_1 fmo_2 imo_0 ax-8 imim12d cbv3 ancli fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi fmo_1 fmo_2 fmo_0 fmo_1 cv imo_0 cv wceq fmo_2 emo_0 fmo_1 cv imo_0 cv wceq fmo_2 nfv nfim fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq fmo_1 fmo_0 fmo_1 fmo_2 emo_0 nfs1 fmo_2 cv imo_0 cv wceq fmo_1 nfv nfim aaan sylibr fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi wa fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_1 fmo_2 fmo_0 fmo_1 cv imo_0 cv wceq wi fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq wi wa fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv imo_0 cv wceq fmo_2 cv imo_0 cv wceq wa fmo_1 cv fmo_2 cv wceq fmo_0 fmo_1 cv imo_0 cv wceq fmo_0 fmo_1 fmo_2 wsb fmo_2 cv imo_0 cv wceq prth fmo_1 fmo_2 imo_0 equtr2 syl6 2alimi syl exlimiv sylbir fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 fmo_2 wsb fmo_2 wex fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 wex fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 fmo_2 wsb fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 fmo_1 nfa2 fmo_0 fmo_1 fmo_2 wsb fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_1 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_0 fmo_1 fmo_2 wsb fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 fmo_0 fmo_1 fmo_2 emo_0 nfs1 fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_0 fmo_0 fmo_1 fmo_2 wsb fmo_1 cv fmo_2 cv wceq fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 wal fmo_0 fmo_0 fmo_1 fmo_2 wsb fmo_1 cv fmo_2 cv wceq fmo_0 fmo_0 fmo_1 fmo_2 wsb wa fmo_1 cv fmo_2 cv wceq wi fmo_2 sp exp3a com3r alimd com12 eximd fmo_0 fmo_1 fmo_2 wsb fmo_2 wex wn fmo_0 fmo_1 fmo_2 wsb wn fmo_2 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 wex fmo_0 fmo_1 fmo_2 wsb fmo_2 alnex fmo_0 fmo_1 fmo_2 wsb wn fmo_2 wal fmo_0 wn fmo_1 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 wex fmo_0 fmo_1 fmo_2 wsb wn fmo_0 wn fmo_2 fmo_1 fmo_0 fmo_1 fmo_2 wsb fmo_1 fmo_0 fmo_1 fmo_2 emo_0 nfs1 nfn fmo_0 fmo_2 emo_0 nfn fmo_2 cv fmo_1 cv wceq fmo_0 fmo_0 fmo_1 fmo_2 wsb fmo_0 fmo_0 fmo_1 fmo_2 wsb wi fmo_1 fmo_2 fmo_0 fmo_1 fmo_2 sbequ1 equcoms con3d cbv3 fmo_0 wn fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 fmo_0 fmo_1 cv fmo_2 cv wceq pm2.21 alimi fmo_0 fmo_1 cv fmo_2 cv wceq wi fmo_1 wal fmo_2 19.8a 3syl sylbir pm2.61d1 impbii $.
$}
$( Existential uniqueness implies existence.  (Contributed by NM,
       15-Sep-1993.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$d x y $.
	$d ph y $.
	ieuex_0 $f set y $.
	feuex_0 $f wff ph $.
	feuex_1 $f set x $.
	euex $p |- ( E! x ph -> E. x ph ) $= feuex_0 feuex_1 weu feuex_0 feuex_0 feuex_1 ieuex_0 wsb feuex_1 cv ieuex_0 cv wceq wi ieuex_0 wal wa feuex_1 wex feuex_0 feuex_1 wex feuex_0 feuex_1 ieuex_0 feuex_0 ieuex_0 nfv eu1 feuex_0 feuex_0 feuex_1 ieuex_0 wsb feuex_1 cv ieuex_0 cv wceq wi ieuex_0 wal feuex_1 exsimpl sylbi $.
$}
$( Existential uniqueness implies "at most one."  (Contributed by NM,
       8-Jul-1994.) $)
${
	$d x y $.
	feumo0_0 $f wff ph $.
	feumo0_1 $f set x $.
	feumo0_2 $f set y $.
	eeumo0_0 $e |- F/ y ph $.
	eumo0 $p |- ( E! x ph -> E. y A. x ( ph -> x = y ) ) $= feumo0_0 feumo0_1 weu feumo0_0 feumo0_1 feumo0_2 weq wb feumo0_1 wal feumo0_2 wex feumo0_0 feumo0_1 feumo0_2 weq wi feumo0_1 wal feumo0_2 wex feumo0_0 feumo0_1 feumo0_2 eeumo0_0 euf feumo0_0 feumo0_1 feumo0_2 weq wb feumo0_1 wal feumo0_0 feumo0_1 feumo0_2 weq wi feumo0_1 wal feumo0_2 feumo0_0 feumo0_1 feumo0_2 weq wb feumo0_0 feumo0_1 feumo0_2 weq wi feumo0_1 feumo0_0 feumo0_1 feumo0_2 weq bi1 alimi eximi sylbi $.
$}
$( An alternate way of defining existential uniqueness.  Definition 6.10 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 8-Jul-1994.) $)
${
	$d x y $.
	feu2_0 $f wff ph $.
	feu2_1 $f set x $.
	feu2_2 $f set y $.
	eeu2_0 $e |- F/ y ph $.
	eu2 $p |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $= feu2_0 feu2_1 weu feu2_0 feu2_1 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 wal wa feu2_0 feu2_1 weu feu2_0 feu2_1 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 wal feu2_0 feu2_1 euex feu2_0 feu2_1 weu feu2_0 feu2_1 feu2_2 weq wi feu2_1 wal feu2_2 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 wal feu2_0 feu2_1 feu2_2 eeu2_0 eumo0 feu2_0 feu2_1 feu2_2 eeu2_0 mo sylib jca feu2_0 feu2_1 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 wal wa feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_1 wex feu2_0 feu2_1 weu feu2_0 feu2_1 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 wal wa feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_1 wex feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_1 wex feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_1 19.29r feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_1 feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wi wa feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wa feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wi feu2_0 feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_2 wal feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi wi feu2_2 wal feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal wi feu2_0 feu2_0 feu2_1 feu2_2 wsb wa feu2_1 feu2_2 weq wi feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi wi feu2_2 feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq impexp albii feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 eeu2_0 19.21 bitri anbi2i feu2_0 feu2_0 feu2_1 feu2_2 wsb feu2_1 feu2_2 weq wi feu2_2 wal abai bitr4i exbii sylib feu2_0 feu2_1 feu2_2 eeu2_0 eu1 sylibr impbii $.
$}
$( An alternate way to express existential uniqueness.  (Contributed by NM,
       8-Jul-1994.) $)
${
	$d x y $.
	feu3_0 $f wff ph $.
	feu3_1 $f set x $.
	feu3_2 $f set y $.
	eeu3_0 $e |- F/ y ph $.
	eu3 $p |- ( E! x ph <-> ( E. x ph /\ E. y A. x ( ph -> x = y ) ) ) $= feu3_0 feu3_1 weu feu3_0 feu3_1 wex feu3_0 feu3_0 feu3_1 feu3_2 wsb wa feu3_1 feu3_2 weq wi feu3_2 wal feu3_1 wal wa feu3_0 feu3_1 wex feu3_0 feu3_1 feu3_2 weq wi feu3_1 wal feu3_2 wex wa feu3_0 feu3_1 feu3_2 eeu3_0 eu2 feu3_0 feu3_1 feu3_2 weq wi feu3_1 wal feu3_2 wex feu3_0 feu3_0 feu3_1 feu3_2 wsb wa feu3_1 feu3_2 weq wi feu3_2 wal feu3_1 wal feu3_0 feu3_1 wex feu3_0 feu3_1 feu3_2 eeu3_0 mo anbi2i bitr4i $.
$}
$( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       21-Oct-2005.) $)
${
	feuor_0 $f wff ph $.
	feuor_1 $f wff ps $.
	feuor_2 $f set x $.
	eeuor_0 $e |- F/ x ph $.
	euor $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $= feuor_0 wn feuor_1 feuor_2 weu feuor_0 feuor_1 wo feuor_2 weu feuor_0 wn feuor_1 feuor_0 feuor_1 wo feuor_2 feuor_0 feuor_2 eeuor_0 nfn feuor_0 feuor_1 biorf eubid biimpa $.
$}
$( Introduce a disjunct into a uniqueness quantifier.  (Contributed by NM,
       23-Mar-1995.) $)
${
	$d x ph $.
	feuorv_0 $f wff ph $.
	feuorv_1 $f wff ps $.
	feuorv_2 $f set x $.
	euorv $p |- ( ( -. ph /\ E! x ps ) -> E! x ( ph \/ ps ) ) $= feuorv_0 feuorv_1 feuorv_2 feuorv_0 feuorv_2 nfv euor $.
$}
$( Alternate definition of "at most one."  (Contributed by NM,
       8-Mar-1995.) $)
${
	$d x y $.
	fmo2_0 $f wff ph $.
	fmo2_1 $f set x $.
	fmo2_2 $f set y $.
	emo2_0 $e |- F/ y ph $.
	mo2 $p |- ( E* x ph <-> E. y A. x ( ph -> x = y ) ) $= fmo2_0 fmo2_1 wmo fmo2_0 fmo2_1 wex fmo2_0 fmo2_1 weu wi fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 fmo2_1 df-mo fmo2_0 fmo2_1 wex fmo2_0 fmo2_1 weu wi fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 fmo2_1 wex fmo2_0 fmo2_1 weu fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 fmo2_1 wex wn fmo2_0 wn fmo2_1 wal fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 fmo2_1 alnex fmo2_0 wn fmo2_1 wal fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 wn fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 fmo2_0 fmo2_1 fmo2_2 weq pm2.21 alimi fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 19.8a syl sylbir fmo2_0 fmo2_1 fmo2_2 emo2_0 eumo0 ja fmo2_0 fmo2_1 weu fmo2_0 fmo2_1 wex fmo2_0 fmo2_1 fmo2_2 weq wi fmo2_1 wal fmo2_2 wex fmo2_0 fmo2_1 fmo2_2 emo2_0 eu3 simplbi2com impbii bitri $.
$}
$( Substitution into "at most one".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
${
	$d w x z $.
	$d w y z $.
	$d w ph $.
	isbmo_0 $f set w $.
	fsbmo_0 $f wff ph $.
	fsbmo_1 $f set x $.
	fsbmo_2 $f set y $.
	fsbmo_3 $f set z $.
	sbmo $p |- ( [ y / x ] E* z ph <-> E* z [ y / x ] ph ) $= fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 wex fsbmo_1 fsbmo_2 wsb fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 wex fsbmo_0 fsbmo_3 wmo fsbmo_1 fsbmo_2 wsb fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 wmo fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 wex fsbmo_1 fsbmo_2 wsb fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal fsbmo_1 fsbmo_2 wsb isbmo_0 wex fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 wex fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 fsbmo_1 fsbmo_2 sbex fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal fsbmo_1 fsbmo_2 wsb fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_1 fsbmo_2 fsbmo_3 fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq fsbmo_1 fsbmo_2 fsbmo_3 cv isbmo_0 cv wceq fsbmo_1 nfv sblim sbalv exbii bitri fsbmo_0 fsbmo_3 wmo fsbmo_0 fsbmo_3 cv isbmo_0 cv wceq wi fsbmo_3 wal isbmo_0 wex fsbmo_1 fsbmo_2 fsbmo_0 fsbmo_3 isbmo_0 fsbmo_0 isbmo_0 nfv mo2 sbbii fsbmo_0 fsbmo_1 fsbmo_2 wsb fsbmo_3 isbmo_0 fsbmo_0 fsbmo_1 fsbmo_2 wsb isbmo_0 nfv mo2 3bitr4i $.
$}
$( Alternate definition of "at most one."  Definition of [BellMachover]
       p. 460, except that definition has the side condition that ` y ` not
       occur in ` ph ` in place of our hypothesis.  (Contributed by NM,
       8-Mar-1995.) $)
${
	$d x y $.
	fmo3_0 $f wff ph $.
	fmo3_1 $f set x $.
	fmo3_2 $f set y $.
	emo3_0 $e |- F/ y ph $.
	mo3 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $= fmo3_0 fmo3_1 wmo fmo3_0 fmo3_1 fmo3_2 weq wi fmo3_1 wal fmo3_2 wex fmo3_0 fmo3_0 fmo3_1 fmo3_2 wsb wa fmo3_1 fmo3_2 weq wi fmo3_2 wal fmo3_1 wal fmo3_0 fmo3_1 fmo3_2 emo3_0 mo2 fmo3_0 fmo3_1 fmo3_2 emo3_0 mo bitri $.
$}
$( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 10-Apr-2004.) $)
${
	$d x y $.
	$d y ph $.
	fmo4f_0 $f wff ph $.
	fmo4f_1 $f wff ps $.
	fmo4f_2 $f set x $.
	fmo4f_3 $f set y $.
	emo4f_0 $e |- F/ x ps $.
	emo4f_1 $e |- ( x = y -> ( ph <-> ps ) ) $.
	mo4f $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $= fmo4f_0 fmo4f_2 wmo fmo4f_0 fmo4f_0 fmo4f_2 fmo4f_3 wsb wa fmo4f_2 fmo4f_3 weq wi fmo4f_3 wal fmo4f_2 wal fmo4f_0 fmo4f_1 wa fmo4f_2 fmo4f_3 weq wi fmo4f_3 wal fmo4f_2 wal fmo4f_0 fmo4f_2 fmo4f_3 fmo4f_0 fmo4f_3 nfv mo3 fmo4f_0 fmo4f_0 fmo4f_2 fmo4f_3 wsb wa fmo4f_2 fmo4f_3 weq wi fmo4f_0 fmo4f_1 wa fmo4f_2 fmo4f_3 weq wi fmo4f_2 fmo4f_3 fmo4f_0 fmo4f_0 fmo4f_2 fmo4f_3 wsb wa fmo4f_0 fmo4f_1 wa fmo4f_2 fmo4f_3 weq fmo4f_0 fmo4f_2 fmo4f_3 wsb fmo4f_1 fmo4f_0 fmo4f_0 fmo4f_1 fmo4f_2 fmo4f_3 emo4f_0 emo4f_1 sbie anbi2i imbi1i 2albii bitri $.
$}
$( "At most one" expressed using implicit substitution.  (Contributed by
       NM, 26-Jul-1995.) $)
${
	$d x y $.
	$d y ph $.
	$d x ps $.
	fmo4_0 $f wff ph $.
	fmo4_1 $f wff ps $.
	fmo4_2 $f set x $.
	fmo4_3 $f set y $.
	emo4_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	mo4 $p |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) ) $= fmo4_0 fmo4_1 fmo4_2 fmo4_3 fmo4_1 fmo4_2 nfv emo4_0 mo4f $.
$}
$( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by NM, 8-Mar-1995.) $)
${
	fmobid_0 $f wff ph $.
	fmobid_1 $f wff ps $.
	fmobid_2 $f wff ch $.
	fmobid_3 $f set x $.
	emobid_0 $e |- F/ x ph $.
	emobid_1 $e |- ( ph -> ( ps <-> ch ) ) $.
	mobid $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $= fmobid_0 fmobid_1 fmobid_3 wex fmobid_1 fmobid_3 weu wi fmobid_2 fmobid_3 wex fmobid_2 fmobid_3 weu wi fmobid_1 fmobid_3 wmo fmobid_2 fmobid_3 wmo fmobid_0 fmobid_1 fmobid_3 wex fmobid_2 fmobid_3 wex fmobid_1 fmobid_3 weu fmobid_2 fmobid_3 weu fmobid_0 fmobid_1 fmobid_2 fmobid_3 emobid_0 emobid_1 exbid fmobid_0 fmobid_1 fmobid_2 fmobid_3 emobid_0 emobid_1 eubid imbi12d fmobid_1 fmobid_3 df-mo fmobid_2 fmobid_3 df-mo 3bitr4g $.
$}
$( Formula-building rule for "at most one" quantifier (deduction rule).
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
${
	$d x ph $.
	fmobidv_0 $f wff ph $.
	fmobidv_1 $f wff ps $.
	fmobidv_2 $f wff ch $.
	fmobidv_3 $f set x $.
	emobidv_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	mobidv $p |- ( ph -> ( E* x ps <-> E* x ch ) ) $= fmobidv_0 fmobidv_1 fmobidv_2 fmobidv_3 fmobidv_0 fmobidv_3 nfv emobidv_0 mobid $.
$}
$( Formula-building rule for "at most one" quantifier (inference rule).
       (Contributed by NM, 9-Mar-1995.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
${
	fmobii_0 $f wff ps $.
	fmobii_1 $f wff ch $.
	fmobii_2 $f set x $.
	emobii_0 $e |- ( ps <-> ch ) $.
	mobii $p |- ( E* x ps <-> E* x ch ) $= fmobii_0 fmobii_2 wmo fmobii_1 fmobii_2 wmo wb wtru fmobii_0 fmobii_1 fmobii_2 fmobii_0 fmobii_1 wb wtru emobii_0 a1i mobidv trud $.
$}
$( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 9-Mar-1995.)  (Revised by Andrew Salmon,
       8-Jun-2011.) $)
${
	fcbvmo_0 $f wff ph $.
	fcbvmo_1 $f wff ps $.
	fcbvmo_2 $f set x $.
	fcbvmo_3 $f set y $.
	ecbvmo_0 $e |- F/ y ph $.
	ecbvmo_1 $e |- F/ x ps $.
	ecbvmo_2 $e |- ( x = y -> ( ph <-> ps ) ) $.
	cbvmo $p |- ( E* x ph <-> E* y ps ) $= fcbvmo_0 fcbvmo_2 wex fcbvmo_0 fcbvmo_2 weu wi fcbvmo_1 fcbvmo_3 wex fcbvmo_1 fcbvmo_3 weu wi fcbvmo_0 fcbvmo_2 wmo fcbvmo_1 fcbvmo_3 wmo fcbvmo_0 fcbvmo_2 wex fcbvmo_1 fcbvmo_3 wex fcbvmo_0 fcbvmo_2 weu fcbvmo_1 fcbvmo_3 weu fcbvmo_0 fcbvmo_1 fcbvmo_2 fcbvmo_3 ecbvmo_0 ecbvmo_1 ecbvmo_2 cbvex fcbvmo_0 fcbvmo_1 fcbvmo_2 fcbvmo_3 ecbvmo_0 ecbvmo_1 ecbvmo_2 cbveu imbi12i fcbvmo_0 fcbvmo_2 df-mo fcbvmo_1 fcbvmo_3 df-mo 3bitr4i $.
$}
$( Uniqueness in terms of "at most one."  (Contributed by NM,
       23-Mar-1995.) $)
${
	$d x y $.
	$d y ph $.
	ieu5_0 $f set y $.
	feu5_0 $f wff ph $.
	feu5_1 $f set x $.
	eu5 $p |- ( E! x ph <-> ( E. x ph /\ E* x ph ) ) $= feu5_0 feu5_1 weu feu5_0 feu5_1 wex feu5_0 feu5_1 cv ieu5_0 cv wceq wi feu5_1 wal ieu5_0 wex wa feu5_0 feu5_1 wex feu5_0 feu5_1 wmo wa feu5_0 feu5_1 ieu5_0 feu5_0 ieu5_0 nfv eu3 feu5_0 feu5_1 wmo feu5_0 feu5_1 cv ieu5_0 cv wceq wi feu5_1 wal ieu5_0 wex feu5_0 feu5_1 wex feu5_0 feu5_1 ieu5_0 feu5_0 ieu5_0 nfv mo2 anbi2i bitr4i $.
$}
$( Uniqueness using implicit substitution.  (Contributed by NM,
       26-Jul-1995.) $)
${
	$d x y $.
	$d y ph $.
	$d x ps $.
	feu4_0 $f wff ph $.
	feu4_1 $f wff ps $.
	feu4_2 $f set x $.
	feu4_3 $f set y $.
	eeu4_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	eu4 $p |- ( E! x ph <-> ( E. x ph /\ A. x A. y ( ( ph /\ ps ) -> x = y ) ) ) $= feu4_0 feu4_2 weu feu4_0 feu4_2 wex feu4_0 feu4_2 wmo wa feu4_0 feu4_2 wex feu4_0 feu4_1 wa feu4_2 feu4_3 weq wi feu4_3 wal feu4_2 wal wa feu4_0 feu4_2 eu5 feu4_0 feu4_2 wmo feu4_0 feu4_1 wa feu4_2 feu4_3 weq wi feu4_3 wal feu4_2 wal feu4_0 feu4_2 wex feu4_0 feu4_1 feu4_2 feu4_3 eeu4_0 mo4 anbi2i bitri $.
$}
$( Existential uniqueness implies "at most one."  (Contributed by NM,
     23-Mar-1995.) $)
${
	feumo_0 $f wff ph $.
	feumo_1 $f set x $.
	eumo $p |- ( E! x ph -> E* x ph ) $= feumo_0 feumo_1 weu feumo_0 feumo_1 wex feumo_0 feumo_1 wmo feumo_0 feumo_1 eu5 simprbi $.
$}
$( "At most one" inferred from existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
${
	feumoi_0 $f wff ph $.
	feumoi_1 $f set x $.
	eeumoi_0 $e |- E! x ph $.
	eumoi $p |- E* x ph $= feumoi_0 feumoi_1 weu feumoi_0 feumoi_1 wmo eeumoi_0 feumoi_0 feumoi_1 eumo ax-mp $.
$}
$( Existence in terms of "at most one" and uniqueness.  (Contributed by NM,
     5-Apr-2004.) $)
${
	fexmoeu_0 $f wff ph $.
	fexmoeu_1 $f set x $.
	exmoeu $p |- ( E. x ph <-> ( E* x ph -> E! x ph ) ) $= fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 df-mo biimpi com12 fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 wex wi fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 weu fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 wmo fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu wi fexmoeu_0 fexmoeu_1 df-mo biimpri fexmoeu_0 fexmoeu_1 euex imim12i fexmoeu_0 fexmoeu_1 wex fexmoeu_0 fexmoeu_1 weu peirce syl impbii $.
$}
$( Existence implies "at most one" is equivalent to uniqueness.  (Contributed
     by NM, 5-Apr-2004.) $)
${
	fexmoeu2_0 $f wff ph $.
	fexmoeu2_1 $f set x $.
	exmoeu2 $p |- ( E. x ph -> ( E* x ph <-> E! x ph ) ) $= fexmoeu2_0 fexmoeu2_1 weu fexmoeu2_0 fexmoeu2_1 wex fexmoeu2_0 fexmoeu2_1 wmo fexmoeu2_0 fexmoeu2_1 eu5 baibr $.
$}
$( Absorption of existence condition by "at most one."  (Contributed by NM,
     4-Nov-2002.) $)
${
	fmoabs_0 $f wff ph $.
	fmoabs_1 $f set x $.
	moabs $p |- ( E* x ph <-> ( E. x ph -> E* x ph ) ) $= fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 weu wi wi fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 weu wi fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 wmo wi fmoabs_0 fmoabs_1 wmo fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 weu pm5.4 fmoabs_0 fmoabs_1 wmo fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 weu wi fmoabs_0 fmoabs_1 wex fmoabs_0 fmoabs_1 df-mo imbi2i fmoabs_0 fmoabs_1 df-mo 3bitr4ri $.
$}
$( Something exists or at most one exists.  (Contributed by NM,
     8-Mar-1995.) $)
${
	fexmo_0 $f wff ph $.
	fexmo_1 $f set x $.
	exmo $p |- ( E. x ph \/ E* x ph ) $= fexmo_0 fexmo_1 wex fexmo_0 fexmo_1 wmo fexmo_0 fexmo_1 wex wn fexmo_0 fexmo_1 wex fexmo_0 fexmo_1 weu wi fexmo_0 fexmo_1 wmo fexmo_0 fexmo_1 wex fexmo_0 fexmo_1 weu pm2.21 fexmo_0 fexmo_1 df-mo sylibr orri $.
$}
$( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 22-Apr-1995.) $)
${
	$d x y $.
	$d y ph $.
	$d y ps $.
	imoim_0 $f set y $.
	fmoim_0 $f wff ph $.
	fmoim_1 $f wff ps $.
	fmoim_2 $f set x $.
	moim $p |- ( A. x ( ph -> ps ) -> ( E* x ps -> E* x ph ) ) $= fmoim_0 fmoim_1 wi fmoim_2 wal fmoim_1 fmoim_2 cv imoim_0 cv wceq wi fmoim_2 wal imoim_0 wex fmoim_0 fmoim_2 cv imoim_0 cv wceq wi fmoim_2 wal imoim_0 wex fmoim_1 fmoim_2 wmo fmoim_0 fmoim_2 wmo fmoim_0 fmoim_1 wi fmoim_2 wal fmoim_1 fmoim_2 cv imoim_0 cv wceq wi fmoim_2 wal fmoim_0 fmoim_2 cv imoim_0 cv wceq wi fmoim_2 wal imoim_0 fmoim_0 fmoim_1 wi fmoim_1 fmoim_2 cv imoim_0 cv wceq wi fmoim_0 fmoim_2 cv imoim_0 cv wceq wi fmoim_2 fmoim_0 fmoim_1 fmoim_2 cv imoim_0 cv wceq imim1 al2imi eximdv fmoim_1 fmoim_2 imoim_0 fmoim_1 imoim_0 nfv mo2 fmoim_0 fmoim_2 imoim_0 fmoim_0 imoim_0 nfv mo2 3imtr4g $.
$}
$( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by NM, 15-Feb-2006.) $)
${
	fmoimi_0 $f wff ph $.
	fmoimi_1 $f wff ps $.
	fmoimi_2 $f set x $.
	emoimi_0 $e |- ( ph -> ps ) $.
	moimi $p |- ( E* x ps -> E* x ph ) $= fmoimi_0 fmoimi_1 wi fmoimi_1 fmoimi_2 wmo fmoimi_0 fmoimi_2 wmo wi fmoimi_2 fmoimi_0 fmoimi_1 fmoimi_2 moim emoimi_0 mpg $.
$}
$( Move antecedent outside of "at most one."  (Contributed by NM,
       28-Jul-1995.) $)
${
	$d x y $.
	$d x y ph $.
	$d y ps $.
	imorimv_0 $f set y $.
	fmorimv_0 $f wff ph $.
	fmorimv_1 $f wff ps $.
	fmorimv_2 $f set x $.
	morimv $p |- ( E* x ( ph -> ps ) -> ( ph -> E* x ps ) ) $= fmorimv_0 fmorimv_0 fmorimv_1 wi fmorimv_2 wmo fmorimv_1 fmorimv_2 wmo fmorimv_0 fmorimv_0 fmorimv_1 wi fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_2 wal imorimv_0 wex fmorimv_1 fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_2 wal imorimv_0 wex fmorimv_0 fmorimv_1 wi fmorimv_2 wmo fmorimv_1 fmorimv_2 wmo fmorimv_0 fmorimv_0 fmorimv_1 wi fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_2 wal fmorimv_1 fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_2 wal imorimv_0 fmorimv_0 fmorimv_0 fmorimv_1 wi fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_1 fmorimv_2 cv imorimv_0 cv wceq wi fmorimv_2 fmorimv_0 fmorimv_1 fmorimv_0 fmorimv_1 wi fmorimv_2 cv imorimv_0 cv wceq fmorimv_1 fmorimv_0 fmorimv_1 wi wi fmorimv_0 fmorimv_1 fmorimv_0 ax-1 a1i imim1d alimdv eximdv fmorimv_0 fmorimv_1 wi fmorimv_2 imorimv_0 fmorimv_0 fmorimv_1 wi imorimv_0 nfv mo2 fmorimv_1 fmorimv_2 imorimv_0 fmorimv_1 imorimv_0 nfv mo2 3imtr4g com12 $.
$}
$( Uniqueness implies "at most one" through implication.  (Contributed by NM,
     22-Apr-1995.) $)
${
	feuimmo_0 $f wff ph $.
	feuimmo_1 $f wff ps $.
	feuimmo_2 $f set x $.
	euimmo $p |- ( A. x ( ph -> ps ) -> ( E! x ps -> E* x ph ) ) $= feuimmo_1 feuimmo_2 weu feuimmo_1 feuimmo_2 wmo feuimmo_0 feuimmo_1 wi feuimmo_2 wal feuimmo_0 feuimmo_2 wmo feuimmo_1 feuimmo_2 eumo feuimmo_0 feuimmo_1 feuimmo_2 moim syl5 $.
$}
$( Add existential uniqueness quantifiers to an implication.  Note the
     reversed implication in the antecedent.  (Contributed by NM,
     19-Oct-2005.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
${
	feuim_0 $f wff ph $.
	feuim_1 $f wff ps $.
	feuim_2 $f set x $.
	euim $p |- ( ( E. x ph /\ A. x ( ph -> ps ) ) -> ( E! x ps -> E! x ph ) ) $= feuim_0 feuim_2 wex feuim_0 feuim_1 wi feuim_2 wal wa feuim_1 feuim_2 weu feuim_0 feuim_2 wex feuim_0 feuim_2 wmo wa feuim_0 feuim_2 weu feuim_0 feuim_2 wex feuim_1 feuim_2 weu feuim_0 feuim_2 wex feuim_0 feuim_1 wi feuim_2 wal feuim_0 feuim_2 wmo feuim_0 feuim_2 wex feuim_1 feuim_2 weu ax-1 feuim_0 feuim_1 feuim_2 euimmo anim12ii feuim_0 feuim_2 eu5 syl6ibr $.
$}
$( "At most one" is still the case when a conjunct is added.  (Contributed by
     NM, 22-Apr-1995.) $)
${
	fmoan_0 $f wff ph $.
	fmoan_1 $f wff ps $.
	fmoan_2 $f set x $.
	moan $p |- ( E* x ph -> E* x ( ps /\ ph ) ) $= fmoan_1 fmoan_0 wa fmoan_0 fmoan_2 fmoan_1 fmoan_0 simpr moimi $.
$}
$( "At most one" is still true when a conjunct is added.  (Contributed by
       NM, 9-Mar-1995.) $)
${
	fmoani_0 $f wff ph $.
	fmoani_1 $f wff ps $.
	fmoani_2 $f set x $.
	emoani_0 $e |- E* x ph $.
	moani $p |- E* x ( ps /\ ph ) $= fmoani_0 fmoani_2 wmo fmoani_1 fmoani_0 wa fmoani_2 wmo emoani_0 fmoani_0 fmoani_1 fmoani_2 moan ax-mp $.
$}
$( "At most one" is still the case when a disjunct is removed.  (Contributed
     by NM, 5-Apr-2004.) $)
${
	fmoor_0 $f wff ph $.
	fmoor_1 $f wff ps $.
	fmoor_2 $f set x $.
	moor $p |- ( E* x ( ph \/ ps ) -> E* x ph ) $= fmoor_0 fmoor_0 fmoor_1 wo fmoor_2 fmoor_0 fmoor_1 orc moimi $.
$}
$( "At most one" imports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	fmooran1_0 $f wff ph $.
	fmooran1_1 $f wff ps $.
	fmooran1_2 $f set x $.
	mooran1 $p |- ( ( E* x ph \/ E* x ps ) -> E* x ( ph /\ ps ) ) $= fmooran1_0 fmooran1_2 wmo fmooran1_0 fmooran1_1 wa fmooran1_2 wmo fmooran1_1 fmooran1_2 wmo fmooran1_0 fmooran1_1 wa fmooran1_0 fmooran1_2 fmooran1_0 fmooran1_1 simpl moimi fmooran1_1 fmooran1_0 fmooran1_2 moan jaoi $.
$}
$( "At most one" exports disjunction to conjunction.  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	fmooran2_0 $f wff ph $.
	fmooran2_1 $f wff ps $.
	fmooran2_2 $f set x $.
	mooran2 $p |- ( E* x ( ph \/ ps ) -> ( E* x ph /\ E* x ps ) ) $= fmooran2_0 fmooran2_1 wo fmooran2_2 wmo fmooran2_0 fmooran2_2 wmo fmooran2_1 fmooran2_2 wmo fmooran2_0 fmooran2_1 fmooran2_2 moor fmooran2_1 fmooran2_0 fmooran2_1 wo fmooran2_2 fmooran2_1 fmooran2_0 olc moimi jca $.
$}
$( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 3-Dec-2001.) $)
${
	$d x y $.
	$d y ph $.
	$d y ps $.
	imoanim_0 $f set y $.
	fmoanim_0 $f wff ph $.
	fmoanim_1 $f wff ps $.
	fmoanim_2 $f set x $.
	emoanim_0 $e |- F/ x ph $.
	moanim $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $= fmoanim_0 fmoanim_1 wa fmoanim_2 imoanim_0 weq wi fmoanim_2 wal imoanim_0 wex fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal wi imoanim_0 wex fmoanim_0 fmoanim_1 wa fmoanim_2 wmo fmoanim_0 fmoanim_1 fmoanim_2 wmo wi fmoanim_0 fmoanim_1 wa fmoanim_2 imoanim_0 weq wi fmoanim_2 wal fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal wi imoanim_0 fmoanim_0 fmoanim_1 wa fmoanim_2 imoanim_0 weq wi fmoanim_2 wal fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi wi fmoanim_2 wal fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal wi fmoanim_0 fmoanim_1 wa fmoanim_2 imoanim_0 weq wi fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi wi fmoanim_2 fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq impexp albii fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 emoanim_0 19.21 bitri exbii fmoanim_0 fmoanim_1 wa fmoanim_2 imoanim_0 fmoanim_0 fmoanim_1 wa imoanim_0 nfv mo2 fmoanim_0 fmoanim_1 fmoanim_2 wmo wi fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal imoanim_0 wex wi fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal wi imoanim_0 wex fmoanim_1 fmoanim_2 wmo fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal imoanim_0 wex fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 fmoanim_1 imoanim_0 nfv mo2 imbi2i fmoanim_0 fmoanim_1 fmoanim_2 imoanim_0 weq wi fmoanim_2 wal imoanim_0 19.37v bitr4i 3bitr4i $.
$}
$( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 19-Feb-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	feuan_0 $f wff ph $.
	feuan_1 $f wff ps $.
	feuan_2 $f set x $.
	eeuan_0 $e |- F/ x ph $.
	euan $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $= feuan_0 feuan_1 wa feuan_2 weu feuan_0 feuan_1 feuan_2 weu wa feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 wa feuan_2 wmo wa feuan_0 feuan_1 feuan_2 wex feuan_1 feuan_2 wmo wa wa feuan_0 feuan_1 wa feuan_2 weu feuan_0 feuan_1 feuan_2 weu wa feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 wa feuan_2 wmo wa feuan_0 feuan_1 feuan_2 wex feuan_1 feuan_2 wmo feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_0 feuan_1 wa feuan_2 wmo feuan_0 feuan_1 wa feuan_0 feuan_2 eeuan_0 feuan_0 feuan_1 simpl exlimi adantr feuan_0 feuan_1 wa feuan_2 wex feuan_1 feuan_2 wex feuan_0 feuan_1 wa feuan_2 wmo feuan_0 feuan_1 wa feuan_1 feuan_2 feuan_0 feuan_1 simpr eximi adantr feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 wa feuan_2 wmo feuan_1 feuan_2 wmo feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 wa feuan_1 feuan_2 feuan_0 feuan_1 wa feuan_2 nfe1 feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 wa feuan_1 feuan_0 feuan_1 simpr feuan_0 feuan_1 wa feuan_2 wex feuan_1 feuan_0 feuan_0 feuan_1 wa feuan_2 wex feuan_0 feuan_1 feuan_0 feuan_1 wa feuan_0 feuan_2 eeuan_0 feuan_0 feuan_1 simpl exlimi a1d ancrd impbid2 mobid biimpa jca32 feuan_0 feuan_1 wa feuan_2 eu5 feuan_1 feuan_2 weu feuan_1 feuan_2 wex feuan_1 feuan_2 wmo wa feuan_0 feuan_1 feuan_2 eu5 anbi2i 3imtr4i feuan_0 feuan_1 feuan_2 weu feuan_0 feuan_1 wa feuan_2 weu feuan_0 feuan_1 feuan_0 feuan_1 wa feuan_2 eeuan_0 feuan_0 feuan_1 ibar eubid biimpa impbii $.
$}
$( Introduction of a conjunct into "at most one" quantifier.  (Contributed
       by NM, 23-Mar-1995.) $)
${
	$d x ph $.
	fmoanimv_0 $f wff ph $.
	fmoanimv_1 $f wff ps $.
	fmoanimv_2 $f set x $.
	moanimv $p |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) ) $= fmoanimv_0 fmoanimv_1 fmoanimv_2 fmoanimv_0 fmoanimv_2 nfv moanim $.
$}
$( Nested "at most one" and uniqueness quantifiers.  (Contributed by NM,
     25-Jan-2006.) $)
${
	fmoaneu_0 $f wff ph $.
	fmoaneu_1 $f set x $.
	moaneu $p |- E* x ( ph /\ E! x ph ) $= fmoaneu_0 fmoaneu_0 fmoaneu_1 weu wa fmoaneu_1 wmo fmoaneu_0 fmoaneu_1 weu fmoaneu_0 wa fmoaneu_1 wmo fmoaneu_0 fmoaneu_1 weu fmoaneu_0 wa fmoaneu_1 wmo fmoaneu_0 fmoaneu_1 weu fmoaneu_0 fmoaneu_1 wmo wi fmoaneu_0 fmoaneu_1 eumo fmoaneu_0 fmoaneu_1 weu fmoaneu_0 fmoaneu_1 fmoaneu_0 fmoaneu_1 nfeu1 moanim mpbir fmoaneu_0 fmoaneu_0 fmoaneu_1 weu wa fmoaneu_0 fmoaneu_1 weu fmoaneu_0 wa fmoaneu_1 fmoaneu_0 fmoaneu_0 fmoaneu_1 weu ancom mobii mpbir $.
$}
$( Nested "at most one" quantifiers.  (Contributed by NM, 25-Jan-2006.) $)
${
	fmoanmo_0 $f wff ph $.
	fmoanmo_1 $f set x $.
	moanmo $p |- E* x ( ph /\ E* x ph ) $= fmoanmo_0 fmoanmo_0 fmoanmo_1 wmo wa fmoanmo_1 wmo fmoanmo_0 fmoanmo_1 wmo fmoanmo_0 wa fmoanmo_1 wmo fmoanmo_0 fmoanmo_1 wmo fmoanmo_0 wa fmoanmo_1 wmo fmoanmo_0 fmoanmo_1 wmo fmoanmo_0 fmoanmo_1 wmo wi fmoanmo_0 fmoanmo_1 wmo id fmoanmo_0 fmoanmo_1 wmo fmoanmo_0 fmoanmo_1 fmoanmo_0 fmoanmo_1 nfmo1 moanim mpbir fmoanmo_0 fmoanmo_0 fmoanmo_1 wmo wa fmoanmo_0 fmoanmo_1 wmo fmoanmo_0 wa fmoanmo_1 fmoanmo_0 fmoanmo_0 fmoanmo_1 wmo ancom mobii mpbir $.
$}
$( Introduction of a conjunct into uniqueness quantifier.  (Contributed by
       NM, 23-Mar-1995.) $)
${
	$d x ph $.
	feuanv_0 $f wff ph $.
	feuanv_1 $f wff ps $.
	feuanv_2 $f set x $.
	euanv $p |- ( E! x ( ph /\ ps ) <-> ( ph /\ E! x ps ) ) $= feuanv_0 feuanv_1 feuanv_2 feuanv_0 feuanv_2 nfv euan $.
$}
$( "At most one" picks a variable value, eliminating an existential
       quantifier.  (Contributed by NM, 27-Jan-1997.) $)
${
	$d x y $.
	$d y ph $.
	$d y ps $.
	imopick_0 $f set y $.
	fmopick_0 $f wff ph $.
	fmopick_1 $f wff ps $.
	fmopick_2 $f set x $.
	mopick $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $= fmopick_0 fmopick_1 wa fmopick_2 wex fmopick_0 fmopick_2 wmo fmopick_0 fmopick_1 wi fmopick_0 fmopick_1 wa fmopick_2 wex fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb wa imopick_0 wex fmopick_0 fmopick_2 wmo fmopick_0 fmopick_1 wi wi fmopick_0 fmopick_1 wa fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb wa fmopick_2 imopick_0 fmopick_0 fmopick_1 wa imopick_0 nfv fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb fmopick_2 fmopick_0 fmopick_2 imopick_0 nfs1v fmopick_1 fmopick_2 imopick_0 nfs1v nfan fmopick_2 cv imopick_0 cv wceq fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_1 fmopick_2 imopick_0 wsb fmopick_0 fmopick_2 imopick_0 sbequ12 fmopick_1 fmopick_2 imopick_0 sbequ12 anbi12d cbvex fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb wa fmopick_0 fmopick_2 wmo fmopick_0 fmopick_1 wi wi imopick_0 fmopick_0 fmopick_2 wmo fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb wa fmopick_0 fmopick_1 wi fmopick_0 fmopick_2 wmo fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi imopick_0 wal fmopick_2 wal fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_0 fmopick_2 imopick_0 fmopick_0 imopick_0 nfv mo3 fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi imopick_0 wal fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_2 fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi imopick_0 sp sps sylbi fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_0 fmopick_1 wi wi fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb fmopick_1 fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_2 cv imopick_0 cv wceq wi fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb fmopick_1 fmopick_2 imopick_0 wsb fmopick_1 wi fmopick_2 cv imopick_0 cv wceq fmopick_1 fmopick_2 imopick_0 wsb fmopick_1 wi fmopick_0 fmopick_0 fmopick_2 imopick_0 wsb wa fmopick_1 fmopick_2 imopick_0 sbequ2 imim2i exp3a com4t imp syl5 exlimiv sylbi impcom $.
$}
$( Existential uniqueness "picks" a variable value for which another wff is
     true.  If there is only one thing ` x ` such that ` ph ` is true, and
     there is also an ` x ` (actually the same one) such that ` ph ` and ` ps `
     are both true, then ` ph ` implies ` ps ` regardless of ` x ` .  This
     theorem can be useful for eliminating existential quantifiers in a
     hypothesis.  Compare Theorem *14.26 in [WhiteheadRussell] p. 192.
     (Contributed by NM, 10-Jul-1994.) $)
${
	feupick_0 $f wff ph $.
	feupick_1 $f wff ps $.
	feupick_2 $f set x $.
	eupick $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) ) $= feupick_0 feupick_2 weu feupick_0 feupick_2 wmo feupick_0 feupick_1 wa feupick_2 wex feupick_0 feupick_1 wi feupick_0 feupick_2 eumo feupick_0 feupick_1 feupick_2 mopick sylan $.
$}
$( Version of ~ eupick with closed formulas.  (Contributed by NM,
     6-Sep-2008.) $)
${
	feupicka_0 $f wff ph $.
	feupicka_1 $f wff ps $.
	feupicka_2 $f set x $.
	eupicka $p |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> A. x ( ph -> ps ) ) $= feupicka_0 feupicka_2 weu feupicka_0 feupicka_1 wa feupicka_2 wex wa feupicka_0 feupicka_1 wi feupicka_2 feupicka_0 feupicka_2 weu feupicka_0 feupicka_1 wa feupicka_2 wex feupicka_2 feupicka_0 feupicka_2 nfeu1 feupicka_0 feupicka_1 wa feupicka_2 nfe1 nfan feupicka_0 feupicka_1 feupicka_2 eupick alrimi $.
$}
$( Existential uniqueness "pick" showing wff equivalence.  (Contributed by
     NM, 25-Nov-1994.) $)
${
	feupickb_0 $f wff ph $.
	feupickb_1 $f wff ps $.
	feupickb_2 $f set x $.
	eupickb $p |- ( ( E! x ph /\ E! x ps /\ E. x ( ph /\ ps ) ) -> ( ph <-> ps ) ) $= feupickb_0 feupickb_2 weu feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_2 wex w3a feupickb_0 feupickb_1 feupickb_0 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_2 wex feupickb_0 feupickb_1 wi feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 feupickb_2 eupick 3adant2 feupickb_0 feupickb_2 weu feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_2 wex w3a feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_2 wex wa feupickb_1 feupickb_2 weu feupickb_1 feupickb_0 wa feupickb_2 wex wa feupickb_1 feupickb_0 wi feupickb_0 feupickb_2 weu feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_2 wex 3simpc feupickb_0 feupickb_1 wa feupickb_2 wex feupickb_1 feupickb_0 wa feupickb_2 wex feupickb_1 feupickb_2 weu feupickb_0 feupickb_1 wa feupickb_1 feupickb_0 wa feupickb_2 feupickb_0 feupickb_1 pm3.22 eximi anim2i feupickb_1 feupickb_0 feupickb_2 eupick 3syl impbid $.
$}
$( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
${
	feupickbi_0 $f wff ph $.
	feupickbi_1 $f wff ps $.
	feupickbi_2 $f set x $.
	eupickbi $p |- ( E! x ph -> ( E. x ( ph /\ ps ) <-> A. x ( ph -> ps ) ) ) $= feupickbi_0 feupickbi_2 weu feupickbi_0 feupickbi_1 wa feupickbi_2 wex feupickbi_0 feupickbi_1 wi feupickbi_2 wal feupickbi_0 feupickbi_2 weu feupickbi_0 feupickbi_1 wa feupickbi_2 wex feupickbi_0 feupickbi_1 wi feupickbi_2 wal feupickbi_0 feupickbi_1 feupickbi_2 eupicka ex feupickbi_0 feupickbi_1 wi feupickbi_2 wal feupickbi_0 feupickbi_2 weu feupickbi_0 feupickbi_1 wa feupickbi_2 wex feupickbi_0 feupickbi_1 wi feupickbi_2 wal feupickbi_0 feupickbi_2 weu feupickbi_0 feupickbi_1 wa feupickbi_2 weu feupickbi_0 feupickbi_1 wa feupickbi_2 wex feupickbi_0 feupickbi_1 wi feupickbi_2 wal feupickbi_0 feupickbi_0 feupickbi_1 wa feupickbi_2 feupickbi_0 feupickbi_1 wi feupickbi_2 nfa1 feupickbi_0 feupickbi_1 wi feupickbi_0 feupickbi_0 feupickbi_1 wa wb feupickbi_2 feupickbi_0 feupickbi_1 wi feupickbi_0 feupickbi_0 feupickbi_1 wa feupickbi_0 feupickbi_1 ancl feupickbi_0 feupickbi_1 simpl impbid1 sps eubid feupickbi_0 feupickbi_1 wa feupickbi_2 euex syl6bi com12 impbid $.
$}
$( "At most one" can show the existence of a common value.  In this case we
     can infer existence of conjunction from a conjunction of existence, and it
     is one way to achieve the converse of ~ 19.40 .  (Contributed by NM,
     5-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	fmopick2_0 $f wff ph $.
	fmopick2_1 $f wff ps $.
	fmopick2_2 $f wff ch $.
	fmopick2_3 $f set x $.
	mopick2 $p |- ( ( E* x ph /\ E. x ( ph /\ ps ) /\ E. x ( ph /\ ch ) ) -> E. x ( ph /\ ps /\ ch ) ) $= fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex fmopick2_0 fmopick2_2 wa fmopick2_3 wex fmopick2_0 fmopick2_1 fmopick2_2 w3a fmopick2_3 wex fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex wa fmopick2_0 fmopick2_2 wa fmopick2_0 fmopick2_1 fmopick2_2 w3a fmopick2_3 fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex fmopick2_3 fmopick2_0 fmopick2_3 nfmo1 fmopick2_0 fmopick2_1 wa fmopick2_3 nfe1 nfan fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex wa fmopick2_0 fmopick2_2 wa fmopick2_0 fmopick2_1 wa fmopick2_2 wa fmopick2_0 fmopick2_1 fmopick2_2 w3a fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex wa fmopick2_0 fmopick2_0 fmopick2_1 wa fmopick2_2 fmopick2_0 fmopick2_3 wmo fmopick2_0 fmopick2_1 wa fmopick2_3 wex wa fmopick2_0 fmopick2_1 fmopick2_0 fmopick2_1 fmopick2_3 mopick ancld anim1d fmopick2_0 fmopick2_1 fmopick2_2 df-3an syl6ibr eximd 3impia $.
$}
$( Introduce or eliminate a disjunct in a uniqueness quantifier.
     (Contributed by NM, 21-Oct-2005.)  (Proof shortened by Andrew Salmon,
     9-Jul-2011.) $)
${
	feuor2_0 $f wff ph $.
	feuor2_1 $f wff ps $.
	feuor2_2 $f set x $.
	euor2 $p |- ( -. E. x ph -> ( E! x ( ph \/ ps ) <-> E! x ps ) ) $= feuor2_0 feuor2_2 wex wn feuor2_0 feuor2_1 wo feuor2_1 feuor2_2 feuor2_0 feuor2_2 wex feuor2_2 feuor2_0 feuor2_2 nfe1 nfn feuor2_0 feuor2_2 wex wn feuor2_0 wn feuor2_0 feuor2_1 wo feuor2_1 wb feuor2_0 feuor2_0 feuor2_2 wex feuor2_0 feuor2_2 19.8a con3i feuor2_0 wn feuor2_0 feuor2_1 wo feuor2_1 feuor2_0 feuor2_1 orel1 feuor2_1 feuor2_0 olc impbid1 syl eubid $.
$}
$( "At most one" double quantification.  (Contributed by NM,
       3-Dec-2001.) $)
${
	fmoexex_0 $f wff ph $.
	fmoexex_1 $f wff ps $.
	fmoexex_2 $f set x $.
	fmoexex_3 $f set y $.
	emoexex_0 $e |- F/ y ph $.
	moexex $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $= fmoexex_0 fmoexex_2 wmo fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_0 fmoexex_2 wex fmoexex_0 fmoexex_2 wmo fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo wi wi fmoexex_0 fmoexex_0 fmoexex_2 wmo fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo wi wi fmoexex_2 fmoexex_0 fmoexex_2 wmo fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo wi fmoexex_2 fmoexex_0 fmoexex_2 nfmo1 fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_2 fmoexex_1 fmoexex_3 wmo fmoexex_2 nfa1 fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_2 fmoexex_3 fmoexex_0 fmoexex_1 wa fmoexex_2 nfe1 nfmo nfim nfim fmoexex_0 fmoexex_0 fmoexex_2 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_1 wi fmoexex_3 wal fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo wi fmoexex_0 fmoexex_0 fmoexex_2 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_1 wi fmoexex_3 emoexex_0 fmoexex_0 fmoexex_3 fmoexex_2 emoexex_0 nfmo fmoexex_0 fmoexex_2 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_0 fmoexex_1 fmoexex_0 fmoexex_2 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_0 fmoexex_1 wi fmoexex_0 fmoexex_1 fmoexex_2 mopick ex com3r alrimd fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_1 wi fmoexex_3 wal fmoexex_1 fmoexex_3 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_2 fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_1 fmoexex_3 moim spsd syl6 exlimi fmoexex_0 fmoexex_2 wex wn fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo wi fmoexex_0 fmoexex_2 wmo fmoexex_0 fmoexex_2 wex wn fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_1 fmoexex_3 wmo fmoexex_2 wal fmoexex_0 fmoexex_2 wex wn fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wex wn fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wex fmoexex_0 fmoexex_2 wex fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_0 fmoexex_2 wex fmoexex_3 fmoexex_0 fmoexex_3 fmoexex_2 emoexex_0 nfex fmoexex_0 fmoexex_1 fmoexex_2 exsimpl exlimi con3i fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wex fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 wmo fmoexex_0 fmoexex_1 wa fmoexex_2 wex fmoexex_3 exmo ori syl a1d a1d pm2.61i imp $.
$}
$( "At most one" double quantification.  (Contributed by NM,
       26-Jan-1997.) $)
${
	$d y ph $.
	fmoexexv_0 $f wff ph $.
	fmoexexv_1 $f wff ps $.
	fmoexexv_2 $f set x $.
	fmoexexv_3 $f set y $.
	moexexv $p |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) ) $= fmoexexv_0 fmoexexv_1 fmoexexv_2 fmoexexv_3 fmoexexv_0 fmoexexv_3 nfv moexex $.
$}
$( Double quantification with "at most one."  (Contributed by NM,
     3-Dec-2001.) $)
${
	f2moex_0 $f wff ph $.
	f2moex_1 $f set x $.
	f2moex_2 $f set y $.
	2moex $p |- ( E* x E. y ph -> A. y E* x ph ) $= f2moex_0 f2moex_2 wex f2moex_1 wmo f2moex_0 f2moex_1 wmo f2moex_2 f2moex_0 f2moex_2 wex f2moex_2 f2moex_1 f2moex_0 f2moex_2 nfe1 nfmo f2moex_0 f2moex_0 f2moex_2 wex f2moex_1 f2moex_0 f2moex_2 19.8a moimi alrimi $.
$}
$( Double quantification with existential uniqueness.  (Contributed by NM,
     3-Dec-2001.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	f2euex_0 $f wff ph $.
	f2euex_1 $f set x $.
	f2euex_2 $f set y $.
	2euex $p |- ( E! x E. y ph -> E. y E! x ph ) $= f2euex_0 f2euex_2 wex f2euex_1 weu f2euex_0 f2euex_2 wex f2euex_1 wex f2euex_0 f2euex_2 wex f2euex_1 wmo wa f2euex_0 f2euex_1 weu f2euex_2 wex f2euex_0 f2euex_2 wex f2euex_1 eu5 f2euex_0 f2euex_2 wex f2euex_1 wmo f2euex_0 f2euex_2 wex f2euex_1 wex f2euex_0 f2euex_1 weu f2euex_2 wex f2euex_0 f2euex_2 wex f2euex_1 wex f2euex_0 f2euex_1 wex f2euex_2 wex f2euex_0 f2euex_2 wex f2euex_1 wmo f2euex_0 f2euex_1 weu f2euex_2 wex f2euex_0 f2euex_1 f2euex_2 excom f2euex_0 f2euex_2 wex f2euex_1 wmo f2euex_0 f2euex_1 wex f2euex_0 f2euex_1 weu f2euex_2 f2euex_0 f2euex_2 wex f2euex_2 f2euex_1 f2euex_0 f2euex_2 nfe1 nfmo f2euex_0 f2euex_2 wex f2euex_1 wmo f2euex_0 f2euex_1 wmo f2euex_0 f2euex_1 wex f2euex_0 f2euex_1 weu wi f2euex_0 f2euex_0 f2euex_2 wex f2euex_1 f2euex_0 f2euex_2 19.8a moimi f2euex_0 f2euex_1 df-mo sylib eximd syl5bi impcom sylbi $.
$}
$( Double quantification with existential uniqueness and "at most one."
     (Contributed by NM, 3-Dec-2001.) $)
${
	f2eumo_0 $f wff ph $.
	f2eumo_1 $f set x $.
	f2eumo_2 $f set y $.
	2eumo $p |- ( E! x E* y ph -> E* x E! y ph ) $= f2eumo_0 f2eumo_2 weu f2eumo_0 f2eumo_2 wmo wi f2eumo_0 f2eumo_2 wmo f2eumo_1 weu f2eumo_0 f2eumo_2 weu f2eumo_1 wmo wi f2eumo_1 f2eumo_0 f2eumo_2 weu f2eumo_0 f2eumo_2 wmo f2eumo_1 euimmo f2eumo_0 f2eumo_2 eumo mpg $.
$}
$( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
${
	f2eu2ex_0 $f wff ph $.
	f2eu2ex_1 $f set x $.
	f2eu2ex_2 $f set y $.
	2eu2ex $p |- ( E! x E! y ph -> E. x E. y ph ) $= f2eu2ex_0 f2eu2ex_2 weu f2eu2ex_1 weu f2eu2ex_0 f2eu2ex_2 weu f2eu2ex_1 wex f2eu2ex_0 f2eu2ex_2 wex f2eu2ex_1 wex f2eu2ex_0 f2eu2ex_2 weu f2eu2ex_1 euex f2eu2ex_0 f2eu2ex_2 weu f2eu2ex_0 f2eu2ex_2 wex f2eu2ex_1 f2eu2ex_0 f2eu2ex_2 euex eximi syl $.
$}
$( A condition allowing swap of "at most one" and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
${
	f2moswap_0 $f wff ph $.
	f2moswap_1 $f set x $.
	f2moswap_2 $f set y $.
	2moswap $p |- ( A. x E* y ph -> ( E* x E. y ph -> E* y E. x ph ) ) $= f2moswap_0 f2moswap_2 wmo f2moswap_1 wal f2moswap_0 f2moswap_2 wex f2moswap_1 wmo f2moswap_0 f2moswap_2 wex f2moswap_0 wa f2moswap_1 wex f2moswap_2 wmo f2moswap_0 f2moswap_1 wex f2moswap_2 wmo f2moswap_0 f2moswap_2 wex f2moswap_1 wmo f2moswap_0 f2moswap_2 wmo f2moswap_1 wal f2moswap_0 f2moswap_2 wex f2moswap_0 wa f2moswap_1 wex f2moswap_2 wmo f2moswap_0 f2moswap_2 wex f2moswap_0 f2moswap_1 f2moswap_2 f2moswap_0 f2moswap_2 nfe1 moexex expcom f2moswap_0 f2moswap_1 wex f2moswap_0 f2moswap_2 wex f2moswap_0 wa f2moswap_1 wex f2moswap_2 f2moswap_0 f2moswap_0 f2moswap_2 wex f2moswap_0 wa f2moswap_1 f2moswap_0 f2moswap_0 f2moswap_2 wex f2moswap_0 f2moswap_2 19.8a pm4.71ri exbii mobii syl6ibr $.
$}
$( A condition allowing swap of uniqueness and existential quantifiers.
     (Contributed by NM, 10-Apr-2004.) $)
${
	f2euswap_0 $f wff ph $.
	f2euswap_1 $f set x $.
	f2euswap_2 $f set y $.
	2euswap $p |- ( A. x E* y ph -> ( E! x E. y ph -> E! y E. x ph ) ) $= f2euswap_0 f2euswap_2 wmo f2euswap_1 wal f2euswap_0 f2euswap_2 wex f2euswap_1 wex f2euswap_0 f2euswap_2 wex f2euswap_1 wmo wa f2euswap_0 f2euswap_1 wex f2euswap_2 wex f2euswap_0 f2euswap_1 wex f2euswap_2 wmo wa f2euswap_0 f2euswap_2 wex f2euswap_1 weu f2euswap_0 f2euswap_1 wex f2euswap_2 weu f2euswap_0 f2euswap_2 wmo f2euswap_1 wal f2euswap_0 f2euswap_2 wex f2euswap_1 wex f2euswap_0 f2euswap_1 wex f2euswap_2 wex f2euswap_0 f2euswap_2 wex f2euswap_1 wmo f2euswap_0 f2euswap_1 wex f2euswap_2 wmo f2euswap_0 f2euswap_2 wex f2euswap_1 wex f2euswap_0 f2euswap_1 wex f2euswap_2 wex wi f2euswap_0 f2euswap_2 wmo f2euswap_1 wal f2euswap_0 f2euswap_1 f2euswap_2 excomim a1i f2euswap_0 f2euswap_1 f2euswap_2 2moswap anim12d f2euswap_0 f2euswap_2 wex f2euswap_1 eu5 f2euswap_0 f2euswap_1 wex f2euswap_2 eu5 3imtr4g $.
$}
$( Double existential uniqueness implies double uniqueness quantification.
     (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro,
     22-Dec-2016.) $)
${
	f2exeu_0 $f wff ph $.
	f2exeu_1 $f set x $.
	f2exeu_2 $f set y $.
	2exeu $p |- ( ( E! x E. y ph /\ E! y E. x ph ) -> E! x E! y ph ) $= f2exeu_0 f2exeu_2 wex f2exeu_1 weu f2exeu_0 f2exeu_1 wex f2exeu_2 weu wa f2exeu_0 f2exeu_2 weu f2exeu_1 wex f2exeu_0 f2exeu_2 weu f2exeu_1 wmo wa f2exeu_0 f2exeu_2 weu f2exeu_1 weu f2exeu_0 f2exeu_2 wex f2exeu_1 weu f2exeu_0 f2exeu_2 weu f2exeu_1 wmo f2exeu_0 f2exeu_1 wex f2exeu_2 weu f2exeu_0 f2exeu_2 weu f2exeu_1 wex f2exeu_0 f2exeu_2 wex f2exeu_1 weu f2exeu_0 f2exeu_2 wex f2exeu_1 wmo f2exeu_0 f2exeu_2 weu f2exeu_1 wmo f2exeu_0 f2exeu_2 wex f2exeu_1 eumo f2exeu_0 f2exeu_2 weu f2exeu_0 f2exeu_2 wex f2exeu_1 f2exeu_0 f2exeu_2 euex moimi syl f2exeu_0 f2exeu_2 f2exeu_1 2euex anim12ci f2exeu_0 f2exeu_2 weu f2exeu_1 eu5 sylibr $.
$}
$( Two equivalent expressions for double "at most one."  (Contributed by
       NM, 2-Feb-2005.)  (Revised by Mario Carneiro, 17-Oct-2016.) $)
${
	$d x y z w v u $.
	$d z w v u ph $.
	i2mo_0 $f set v $.
	i2mo_1 $f set u $.
	f2mo_0 $f wff ph $.
	f2mo_1 $f set x $.
	f2mo_2 $f set y $.
	f2mo_3 $f set z $.
	f2mo_4 $f set w $.
	2mo $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ [ z / x ] [ w / y ] ph ) -> ( x = z /\ y = w ) ) ) $= f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal i2mo_1 wex i2mo_0 wex f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal i2mo_0 i2mo_1 f2mo_3 f2mo_4 i2mo_0 cv f2mo_3 cv wceq i2mo_1 cv f2mo_4 cv wceq wa f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_1 f2mo_2 i2mo_0 cv f2mo_3 cv wceq i2mo_1 cv f2mo_4 cv wceq wa f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_0 i2mo_0 cv f2mo_3 cv wceq f2mo_1 cv i2mo_0 cv wceq f2mo_1 cv f2mo_3 cv wceq i2mo_1 cv f2mo_4 cv wceq f2mo_2 cv i2mo_1 cv wceq f2mo_2 cv f2mo_4 cv wceq i2mo_0 f2mo_3 f2mo_1 equequ2 i2mo_1 f2mo_4 f2mo_2 equequ2 bi2anan9 imbi2d 2albidv cbvex2v f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal i2mo_0 i2mo_1 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal f2mo_3 wal wa f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_1 f2mo_2 f2mo_3 f2mo_4 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_3 nfv f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_4 nfv f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_1 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 nfs1v f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_1 nfv nfim f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 f2mo_2 f2mo_0 f2mo_2 f2mo_4 nfs1v nfsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 nfv nfim f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 cv f2mo_4 cv wceq f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 cv f2mo_3 cv wceq f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_2 f2mo_4 sbequ12 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 sbequ12 sylan9bbr f2mo_1 cv f2mo_3 cv wceq f2mo_1 cv i2mo_0 cv wceq f2mo_3 cv i2mo_0 cv wceq f2mo_2 cv f2mo_4 cv wceq f2mo_2 cv i2mo_1 cv wceq f2mo_4 cv i2mo_1 cv wceq f2mo_1 f2mo_3 i2mo_0 equequ1 f2mo_2 f2mo_4 i2mo_1 equequ1 bi2anan9 imbi12d cbval2 biimpi ancli f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal wa f2mo_3 wal f2mo_1 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal f2mo_3 wal wa f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal wa f2mo_3 wal f2mo_1 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_2 wal f2mo_3 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal wa f2mo_3 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_2 f2mo_3 alcom f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_2 wal f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal wa f2mo_3 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_2 f2mo_4 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_4 nfv f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 f2mo_2 f2mo_0 f2mo_2 f2mo_4 nfs1v nfsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 nfv nfim aaan albii bitri albii f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_4 wal f2mo_1 f2mo_3 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_2 wal f2mo_3 nfv f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi f2mo_1 f2mo_4 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_1 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 nfs1v f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_1 nfv nfim nfal aaan bitri sylibr f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_1 f2mo_2 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_3 f2mo_4 f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa wi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wi wa f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_0 f2mo_1 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq wa f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_3 cv i2mo_0 cv wceq f2mo_4 cv i2mo_1 cv wceq wa prth f2mo_1 cv i2mo_0 cv wceq f2mo_3 cv i2mo_0 cv wceq f2mo_2 cv i2mo_1 cv wceq f2mo_4 cv i2mo_1 cv wceq f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_1 cv i2mo_0 cv wceq f2mo_3 cv i2mo_0 cv wceq wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv i2mo_1 cv wceq f2mo_4 cv i2mo_1 cv wceq wa f2mo_2 cv f2mo_4 cv wceq f2mo_1 f2mo_3 i2mo_0 equtr2 f2mo_2 f2mo_4 i2mo_1 equtr2 anim12i an4s syl6 2alimi 2alimi syl exlimivv sylbir f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex wi f2mo_3 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex wi f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_4 wal f2mo_3 wal f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex wi f2mo_3 wal f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_1 f2mo_2 f2mo_3 f2mo_4 alrot4 f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex wi f2mo_3 f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal wi f2mo_4 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex wi f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal wi f2mo_4 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 nfs1v f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 f2mo_2 f2mo_0 f2mo_2 f2mo_4 nfs1v nfsb f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wa f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 pm3.21 imim1d alimd alimd com12 alimi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 exim syl alimi sylbi f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 exim syl f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_3 wex wn f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex wn f2mo_3 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_3 wex wn f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_4 wal f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex wn f2mo_3 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 alnex albii f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_4 wex f2mo_3 alnex bitri f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_4 wal f2mo_3 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_4 wal f2mo_3 wal f2mo_0 wn f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 wn f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb wn f2mo_1 f2mo_2 f2mo_3 f2mo_4 f2mo_0 wn f2mo_3 nfv f2mo_0 wn f2mo_4 nfv f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_1 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 nfs1v nfn f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_2 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 f2mo_2 f2mo_0 f2mo_2 f2mo_4 nfs1v nfsb nfn f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_2 cv f2mo_4 cv wceq f2mo_0 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 cv f2mo_3 cv wceq f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 wsb f2mo_0 f2mo_2 f2mo_4 sbequ12 f2mo_0 f2mo_2 f2mo_4 wsb f2mo_1 f2mo_3 sbequ12 sylan9bbr notbid cbval2 f2mo_0 wn f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_1 f2mo_2 f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa pm2.21 2alimi sylbir f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 wex f2mo_4 f2mo_0 f2mo_1 cv f2mo_3 cv wceq f2mo_2 cv f2mo_4 cv wceq wa wi f2mo_2 wal f2mo_1 wal f2mo_4 wex f2mo_3 19.8a 19.23bi syl sylbir pm2.61d1 impbii $.
$}
$( Double "exists at most one", using implicit substitution.  (Contributed
       by NM, 10-Feb-2005.) $)
${
	$d z w ph $.
	$d x y ps $.
	$d x y z w $.
	f2mos_0 $f wff ph $.
	f2mos_1 $f wff ps $.
	f2mos_2 $f set x $.
	f2mos_3 $f set y $.
	f2mos_4 $f set z $.
	f2mos_5 $f set w $.
	e2mos_0 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
	2mos $p |- ( E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) <-> A. x A. y A. z A. w ( ( ph /\ ps ) -> ( x = z /\ y = w ) ) ) $= f2mos_0 f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_3 wal f2mos_2 wal f2mos_5 wex f2mos_4 wex f2mos_0 f2mos_0 f2mos_3 f2mos_5 wsb f2mos_2 f2mos_4 wsb wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_5 wal f2mos_4 wal f2mos_3 wal f2mos_2 wal f2mos_0 f2mos_1 wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_5 wal f2mos_4 wal f2mos_3 wal f2mos_2 wal f2mos_0 f2mos_2 f2mos_3 f2mos_4 f2mos_5 2mo f2mos_0 f2mos_0 f2mos_3 f2mos_5 wsb f2mos_2 f2mos_4 wsb wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_5 wal f2mos_4 wal f2mos_0 f2mos_1 wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_5 wal f2mos_4 wal f2mos_2 f2mos_3 f2mos_0 f2mos_0 f2mos_3 f2mos_5 wsb f2mos_2 f2mos_4 wsb wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_0 f2mos_1 wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa wi f2mos_4 f2mos_5 f2mos_0 f2mos_0 f2mos_3 f2mos_5 wsb f2mos_2 f2mos_4 wsb wa f2mos_0 f2mos_1 wa f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq wa f2mos_0 f2mos_3 f2mos_5 wsb f2mos_2 f2mos_4 wsb f2mos_1 f2mos_0 f2mos_0 f2mos_3 f2mos_5 wsb f2mos_1 f2mos_2 f2mos_4 f2mos_1 f2mos_2 nfv f2mos_2 cv f2mos_4 cv wceq f2mos_0 f2mos_3 f2mos_5 wsb f2mos_1 f2mos_2 cv f2mos_4 cv wceq f2mos_0 f2mos_3 f2mos_5 wsb wi f2mos_2 cv f2mos_4 cv wceq f2mos_0 wi f2mos_3 f2mos_5 wsb f2mos_2 cv f2mos_4 cv wceq f2mos_1 wi f2mos_2 cv f2mos_4 cv wceq f2mos_0 f2mos_3 f2mos_5 f2mos_2 cv f2mos_4 cv wceq f2mos_3 nfv sbrim f2mos_2 cv f2mos_4 cv wceq f2mos_0 wi f2mos_2 cv f2mos_4 cv wceq f2mos_1 wi f2mos_3 f2mos_5 f2mos_2 cv f2mos_4 cv wceq f2mos_1 wi f2mos_3 nfv f2mos_3 cv f2mos_5 cv wceq f2mos_2 cv f2mos_4 cv wceq f2mos_0 f2mos_1 f2mos_2 cv f2mos_4 cv wceq f2mos_3 cv f2mos_5 cv wceq f2mos_0 f2mos_1 wb e2mos_0 expcom pm5.74d sbie bitr3i pm5.74ri sbie anbi2i imbi1i 2albii 2albii bitri $.
$}
$( Double existential uniqueness.  This theorem shows a condition under which
     a "naive" definition matches the correct one.  (Contributed by NM,
     3-Dec-2001.) $)
${
	f2eu1_0 $f wff ph $.
	f2eu1_1 $f set x $.
	f2eu1_2 $f set y $.
	2eu1 $p |- ( A. x E* y ph -> ( E! x E! y ph <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $= f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_1 weu f2eu1_0 f2eu1_1 wex f2eu1_2 weu wa f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 weu f2eu1_0 f2eu1_1 wex f2eu1_2 weu wa f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wex wa f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa wa f2eu1_0 f2eu1_2 wex f2eu1_1 weu f2eu1_0 f2eu1_1 wex f2eu1_2 weu wa f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wex wa f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa wi f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 weu f2eu1_1 wex f2eu1_0 f2eu1_2 weu f2eu1_1 wmo wa f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo wa f2eu1_0 f2eu1_2 weu f2eu1_1 eu5 f2eu1_0 f2eu1_2 weu f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wex f2eu1_0 f2eu1_2 weu f2eu1_1 wmo f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 weu f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 f2eu1_0 f2eu1_2 eu5 exbii f2eu1_0 f2eu1_2 weu f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 f2eu1_0 f2eu1_2 eu5 mobii anbi12i bitri simprbi f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal wa f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex wa f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo wi f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex wa f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_1 f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo wa f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wmo f2eu1_0 f2eu1_2 wex f2eu1_0 f2eu1_2 wmo f2eu1_1 sp anim2i ancoms moimi f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 f2eu1_0 f2eu1_2 wmo f2eu1_1 nfa1 moanim sylib ancrd f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_1 wex f2eu1_2 wmo f2eu1_0 f2eu1_2 wmo f2eu1_1 wal f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo f2eu1_0 f2eu1_1 f2eu1_2 2moswap com12 imdistani syl6 syl f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wex f2eu1_0 f2eu1_1 f2eu1_2 2eu2ex f2eu1_0 f2eu1_2 weu f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wex f2eu1_0 f2eu1_1 f2eu1_2 2eu2ex f2eu1_0 f2eu1_1 f2eu1_2 excom sylib jca jctild f2eu1_0 f2eu1_2 wex f2eu1_1 weu f2eu1_0 f2eu1_1 wex f2eu1_2 weu wa f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_1 wmo wa f2eu1_0 f2eu1_1 wex f2eu1_2 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa wa f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wex wa f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa wa f2eu1_0 f2eu1_2 wex f2eu1_1 weu f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_1 wmo wa f2eu1_0 f2eu1_1 wex f2eu1_2 weu f2eu1_0 f2eu1_1 wex f2eu1_2 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wmo wa f2eu1_0 f2eu1_2 wex f2eu1_1 eu5 f2eu1_0 f2eu1_1 wex f2eu1_2 eu5 anbi12i f2eu1_0 f2eu1_2 wex f2eu1_1 wex f2eu1_0 f2eu1_2 wex f2eu1_1 wmo f2eu1_0 f2eu1_1 wex f2eu1_2 wex f2eu1_0 f2eu1_1 wex f2eu1_2 wmo an4 bitri syl6ibr com12 f2eu1_0 f2eu1_1 f2eu1_2 2exeu impbid1 $.
$}
$( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
${
	f2eu2_0 $f wff ph $.
	f2eu2_1 $f set x $.
	f2eu2_2 $f set y $.
	2eu2 $p |- ( E! y E. x ph -> ( E! x E! y ph <-> E! x E. y ph ) ) $= f2eu2_0 f2eu2_1 wex f2eu2_2 weu f2eu2_0 f2eu2_2 weu f2eu2_1 weu f2eu2_0 f2eu2_2 wex f2eu2_1 weu f2eu2_0 f2eu2_1 wex f2eu2_2 weu f2eu2_0 f2eu2_1 wex f2eu2_2 wmo f2eu2_0 f2eu2_2 wmo f2eu2_1 wal f2eu2_0 f2eu2_2 weu f2eu2_1 weu f2eu2_0 f2eu2_2 wex f2eu2_1 weu wi f2eu2_0 f2eu2_1 wex f2eu2_2 eumo f2eu2_0 f2eu2_2 f2eu2_1 2moex f2eu2_0 f2eu2_2 wmo f2eu2_1 wal f2eu2_0 f2eu2_2 weu f2eu2_1 weu f2eu2_0 f2eu2_2 wex f2eu2_1 weu f2eu2_0 f2eu2_1 wex f2eu2_2 weu wa f2eu2_0 f2eu2_2 wex f2eu2_1 weu f2eu2_0 f2eu2_1 f2eu2_2 2eu1 f2eu2_0 f2eu2_2 wex f2eu2_1 weu f2eu2_0 f2eu2_1 wex f2eu2_2 weu simpl syl6bi 3syl f2eu2_0 f2eu2_2 wex f2eu2_1 weu f2eu2_0 f2eu2_1 wex f2eu2_2 weu f2eu2_0 f2eu2_2 weu f2eu2_1 weu f2eu2_0 f2eu2_1 f2eu2_2 2exeu expcom impbid $.
$}
$( Double existential uniqueness.  (Contributed by NM, 3-Dec-2001.) $)
${
	f2eu3_0 $f wff ph $.
	f2eu3_1 $f set x $.
	f2eu3_2 $f set y $.
	2eu3 $p |- ( A. x A. y ( E* x ph \/ E* y ph ) -> ( ( E! x E! y ph /\ E! y E! x ph ) <-> ( E! x E. y ph /\ E! y E. x ph ) ) ) $= f2eu3_0 f2eu3_1 wmo f2eu3_0 f2eu3_2 wmo wo f2eu3_2 wal f2eu3_1 wal f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo f2eu3_1 wal wo f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_1 weu f2eu3_2 weu wa f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa wb f2eu3_0 f2eu3_1 wmo f2eu3_0 f2eu3_2 wmo wo f2eu3_2 wal f2eu3_1 wal f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo wo f2eu3_1 wal f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo f2eu3_1 wal wo f2eu3_0 f2eu3_1 wmo f2eu3_0 f2eu3_2 wmo wo f2eu3_2 wal f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo wo f2eu3_1 f2eu3_0 f2eu3_1 wmo f2eu3_0 f2eu3_2 wmo f2eu3_2 f2eu3_0 f2eu3_2 nfmo1 19.31 albii f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo f2eu3_1 f2eu3_0 f2eu3_1 wmo f2eu3_1 f2eu3_2 f2eu3_0 f2eu3_1 nfmo1 nfal 19.32 bitri f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 wmo f2eu3_1 wal wo f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_1 weu f2eu3_2 weu wa f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_1 weu f2eu3_2 weu wa f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa wi f2eu3_0 f2eu3_2 wmo f2eu3_1 wal f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu wa f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_1 wmo f2eu3_2 wal f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu wa f2eu3_0 f2eu3_2 f2eu3_1 2eu1 biimpd f2eu3_0 f2eu3_1 wex f2eu3_2 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu ancom syl6ib adantld f2eu3_0 f2eu3_2 wmo f2eu3_1 wal f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_2 wmo f2eu3_1 wal f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_1 f2eu3_2 2eu1 biimpd adantrd jaoi f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 wex f2eu3_2 weu wa f2eu3_0 f2eu3_2 weu f2eu3_1 weu f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_1 f2eu3_2 2exeu f2eu3_0 f2eu3_1 wex f2eu3_2 weu f2eu3_0 f2eu3_2 wex f2eu3_1 weu f2eu3_0 f2eu3_1 weu f2eu3_2 weu f2eu3_0 f2eu3_2 f2eu3_1 2exeu ancoms jca impbid1 sylbi $.
$}
$( This theorem provides us with a definition of double existential
       uniqueness ("exactly one ` x ` and exactly one ` y ` ").  Naively one
       might think (incorrectly) that it could be defined by
       ` E! x E! y ph ` .  See ~ 2eu1 for a condition under which the naive
       definition holds and ~ 2exeu for a one-way implication.  See ~ 2eu5 and
       ~ 2eu8 for alternate definitions.  (Contributed by NM, 3-Dec-2001.) $)
${
	$d x y z w $.
	$d z w ph $.
	f2eu4_0 $f wff ph $.
	f2eu4_1 $f set x $.
	f2eu4_2 $f set y $.
	f2eu4_3 $f set z $.
	f2eu4_4 $f set w $.
	2eu4 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $= f2eu4_0 f2eu4_2 wex f2eu4_1 weu f2eu4_0 f2eu4_1 wex f2eu4_2 weu wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex wa f2eu4_0 f2eu4_1 wex f2eu4_2 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex wa wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_1 wex f2eu4_2 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex wa wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_4 wex f2eu4_3 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 weu f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex wa f2eu4_0 f2eu4_1 wex f2eu4_2 weu f2eu4_0 f2eu4_1 wex f2eu4_2 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 f2eu4_3 f2eu4_0 f2eu4_2 wex f2eu4_3 nfv eu3 f2eu4_0 f2eu4_1 wex f2eu4_2 f2eu4_4 f2eu4_0 f2eu4_1 wex f2eu4_4 nfv eu3 anbi12i f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex f2eu4_0 f2eu4_1 wex f2eu4_2 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex an4 f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_1 wex f2eu4_2 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_4 wex f2eu4_3 wex f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_1 wex f2eu4_2 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 wex wa f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_1 wex f2eu4_2 wex f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 wex f2eu4_1 wex f2eu4_0 f2eu4_2 f2eu4_1 excom anbi2i f2eu4_0 f2eu4_2 wex f2eu4_1 wex anidm bitri f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_4 wex f2eu4_3 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_4 wex f2eu4_3 wex f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_3 wex f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_4 wex wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_3 f2eu4_4 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal wa f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi wa f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal wa f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_1 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_1 19.26 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_1 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_1 f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 nfa1 19.3 anbi2i f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_1 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi wa f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq wa wi f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi wa f2eu4_2 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 cv f2eu4_4 cv wceq jcab albii f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 19.26 bitri albii f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 19.26 bitri bitr4i bitr2i f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal wa f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_1 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal wa f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal f2eu4_2 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal wa f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal f2eu4_2 19.26 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_2 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_1 wal f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_2 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 nfa1 19.3 f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 f2eu4_1 alcom anbi12i bitri albii bitr4i f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal wa f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi wa f2eu4_1 f2eu4_2 f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_2 wal f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 wal f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_0 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 19.23v f2eu4_0 f2eu4_2 cv f2eu4_4 cv wceq f2eu4_1 19.23v anbi12i 2albii f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_1 f2eu4_2 f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 f2eu4_0 f2eu4_2 nfe1 f2eu4_1 cv f2eu4_3 cv wceq f2eu4_2 nfv nfim f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq f2eu4_1 f2eu4_0 f2eu4_1 nfe1 f2eu4_2 cv f2eu4_4 cv wceq f2eu4_1 nfv nfim aaan 3bitri 2exbii f2eu4_0 f2eu4_2 wex f2eu4_1 cv f2eu4_3 cv wceq wi f2eu4_1 wal f2eu4_0 f2eu4_1 wex f2eu4_2 cv f2eu4_4 cv wceq wi f2eu4_2 wal f2eu4_3 f2eu4_4 eeanv bitr2i anbi12i 3bitri $.
$}
$( An alternate definition of double existential uniqueness (see ~ 2eu4 ).
       A mistake sometimes made in the literature is to use ` E! x E! y ` to
       mean "exactly one ` x ` and exactly one ` y ` ."  (For example, see
       Proposition 7.53 of [TakeutiZaring] p. 53.)  It turns out that this is
       actually a weaker assertion, as can be seen by expanding out the formal
       definitions.  This theorem shows that the erroneous definition can be
       repaired by conjoining ` A. x E* y ph ` as an additional condition.  The
       correct definition apparently has never been published.  ( ` E* ` means
       "exists at most one.") (Contributed by NM, 26-Oct-2003.) $)
${
	$d x y z w $.
	$d z w ph $.
	f2eu5_0 $f wff ph $.
	f2eu5_1 $f set x $.
	f2eu5_2 $f set y $.
	f2eu5_3 $f set z $.
	f2eu5_4 $f set w $.
	2eu5 $p |- ( ( E! x E! y ph /\ A. x E* y ph ) <-> ( E. x E. y ph /\ E. z E. w A. x A. y ( ph -> ( x = z /\ y = w ) ) ) ) $= f2eu5_0 f2eu5_2 weu f2eu5_1 weu f2eu5_0 f2eu5_2 wmo f2eu5_1 wal wa f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 weu wa f2eu5_0 f2eu5_2 wmo f2eu5_1 wal wa f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 weu wa f2eu5_0 f2eu5_2 wex f2eu5_1 wex f2eu5_0 f2eu5_1 f2eu5_3 weq f2eu5_2 f2eu5_4 weq wa wi f2eu5_2 wal f2eu5_1 wal f2eu5_4 wex f2eu5_3 wex wa f2eu5_0 f2eu5_2 wmo f2eu5_1 wal f2eu5_0 f2eu5_2 weu f2eu5_1 weu f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 weu wa f2eu5_0 f2eu5_1 f2eu5_2 2eu1 pm5.32ri f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 weu wa f2eu5_0 f2eu5_2 wmo f2eu5_1 wal f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 weu wa f2eu5_0 f2eu5_1 wex f2eu5_2 wmo f2eu5_0 f2eu5_2 wmo f2eu5_1 wal f2eu5_0 f2eu5_1 wex f2eu5_2 weu f2eu5_0 f2eu5_1 wex f2eu5_2 wmo f2eu5_0 f2eu5_2 wex f2eu5_1 weu f2eu5_0 f2eu5_1 wex f2eu5_2 eumo adantl f2eu5_0 f2eu5_2 f2eu5_1 2moex syl pm4.71i f2eu5_0 f2eu5_1 f2eu5_2 f2eu5_3 f2eu5_4 2eu4 3bitr2i $.
$}
$( Two equivalent expressions for double existential uniqueness.
       (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
       17-Oct-2016.) $)
${
	$d x y z w v u $.
	$d z w v u ph $.
	i2eu6_0 $f set v $.
	i2eu6_1 $f set u $.
	f2eu6_0 $f wff ph $.
	f2eu6_1 $f set x $.
	f2eu6_2 $f set y $.
	f2eu6_3 $f set z $.
	f2eu6_4 $f set w $.
	2eu6 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E. z E. w A. x A. y ( ph <-> ( x = z /\ y = w ) ) ) $= f2eu6_0 f2eu6_2 wex f2eu6_1 weu f2eu6_0 f2eu6_1 wex f2eu6_2 weu wa f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex wa f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 f2eu6_2 f2eu6_3 f2eu6_4 2eu4 f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex wa f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_4 wal f2eu6_3 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_1 f2eu6_2 f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_3 nfv f2eu6_0 f2eu6_4 nfv f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 nfs1v f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 nfs1v nfsb f2eu6_2 cv f2eu6_4 cv wceq f2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 cv f2eu6_3 cv wceq f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 sbequ12 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 sbequ12 sylan9bbr cbvex2 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal i2eu6_1 wex i2eu6_0 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_4 wal f2eu6_3 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_3 f2eu6_4 i2eu6_0 i2eu6_1 f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_1 f2eu6_2 f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa f2eu6_0 f2eu6_3 cv i2eu6_0 cv wceq f2eu6_1 cv f2eu6_3 cv wceq f2eu6_1 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq f2eu6_2 cv f2eu6_4 cv wceq f2eu6_2 cv i2eu6_1 cv wceq f2eu6_3 i2eu6_0 f2eu6_1 equequ2 f2eu6_4 i2eu6_1 f2eu6_2 equequ2 bi2anan9 imbi2d 2albidv cbvex2v f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal i2eu6_1 wex i2eu6_0 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi f2eu6_4 wal f2eu6_3 wal i2eu6_1 wex i2eu6_0 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_4 wal f2eu6_3 wal f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi f2eu6_4 wal f2eu6_3 wal i2eu6_0 i2eu6_1 f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi f2eu6_1 f2eu6_2 f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_3 nfv f2eu6_0 f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa wi f2eu6_4 nfv f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 nfs1v f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 nfv nfim f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 nfs1v nfsb f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_2 nfv nfim f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_2 cv f2eu6_4 cv wceq f2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 cv f2eu6_3 cv wceq f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 sbequ12 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 sbequ12 sylan9bbr f2eu6_1 cv f2eu6_3 cv wceq f2eu6_1 cv i2eu6_0 cv wceq f2eu6_3 cv i2eu6_0 cv wceq f2eu6_2 cv f2eu6_4 cv wceq f2eu6_2 cv i2eu6_1 cv wceq f2eu6_4 cv i2eu6_1 cv wceq f2eu6_1 f2eu6_3 i2eu6_0 equequ1 f2eu6_2 f2eu6_4 i2eu6_1 equequ1 bi2anan9 imbi12d cbval2 2exbii f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 f2eu6_4 i2eu6_0 i2eu6_1 2mo bitri bitri f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_3 f2eu6_4 19.29r2 syl2anb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_1 f2eu6_2 2albiim f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal ancom bitri 2exbii f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wi wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi i2eu6_1 wal i2eu6_0 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa wi f2eu6_1 f2eu6_2 i2eu6_0 i2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi i2eu6_0 nfv f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi i2eu6_1 nfv f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 nfs1v f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 f2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 f2eu6_1 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 nfs1v nfsb nfsb nfan f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 nfv nfim f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 nfs1v nfsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 nfs1v nfsb nfsb nfsb nfan f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_2 nfv nfim f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa f2eu6_3 cv i2eu6_0 cv wceq f2eu6_4 cv i2eu6_1 cv wceq wa f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa f2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_1 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq wa f2eu6_0 f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_2 cv i2eu6_1 cv wceq f2eu6_0 f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 cv i2eu6_0 cv wceq f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 i2eu6_0 wsb f2eu6_0 f2eu6_2 i2eu6_1 sbequ12 f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 i2eu6_0 sbequ12 sylan9bbr f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_1 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_0 f2eu6_2 i2eu6_1 wsb f2eu6_1 i2eu6_0 f2eu6_0 f2eu6_2 i2eu6_1 f2eu6_4 f2eu6_0 f2eu6_4 nfv sbco2 sbbii f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_1 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_1 f2eu6_3 wsb f2eu6_3 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_1 i2eu6_0 f2eu6_3 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 nfv sbco2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_4 i2eu6_1 wsb f2eu6_3 i2eu6_0 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_4 i2eu6_1 f2eu6_1 f2eu6_3 sbcom2 sbbii bitr3i bitr3i syl6bb anbi2d f2eu6_1 cv i2eu6_0 cv wceq f2eu6_3 cv f2eu6_1 cv wceq f2eu6_3 cv i2eu6_0 cv wceq f2eu6_2 cv i2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq f2eu6_4 cv i2eu6_1 cv wceq f2eu6_1 i2eu6_0 f2eu6_3 equequ2 f2eu6_2 i2eu6_1 f2eu6_4 equequ2 bi2anan9 imbi12d cbval2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi wi f2eu6_1 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi wi f2eu6_3 cv f2eu6_1 cv wceq f2eu6_4 cv f2eu6_2 cv wceq wa f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 wa f2eu6_3 cv f2eu6_1 cv wceq f2eu6_1 cv f2eu6_3 cv wceq f2eu6_4 cv f2eu6_2 cv wceq f2eu6_2 cv f2eu6_4 cv wceq f2eu6_3 f2eu6_1 equcom f2eu6_4 f2eu6_2 equcom anbi12i imbi2i f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa impexp bitri 2albii bitr3i f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_1 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 nfs1v f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 f2eu6_2 f2eu6_0 f2eu6_2 f2eu6_4 nfs1v nfsb 19.21-2 bitri anbi2i f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal abai bitr4i f2eu6_0 f2eu6_2 f2eu6_4 wsb f2eu6_1 f2eu6_3 wsb f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 f2eu6_2 f2eu6_3 f2eu6_4 2sb6 anbi1i bitri 2exbii bitr4i sylibr f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_4 wex f2eu6_3 wex f2eu6_0 f2eu6_2 wex f2eu6_1 wex f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_2 wal f2eu6_1 wal f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa f2eu6_0 wi f2eu6_1 f2eu6_2 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa bi2 2alimi 2eximi f2eu6_0 f2eu6_1 f2eu6_2 f2eu6_3 f2eu6_4 2exsb sylibr f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_2 wal f2eu6_1 wal f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_2 wal f2eu6_1 wal f2eu6_3 f2eu6_4 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wb f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa wi f2eu6_1 f2eu6_2 f2eu6_0 f2eu6_1 cv f2eu6_3 cv wceq f2eu6_2 cv f2eu6_4 cv wceq wa bi1 2alimi 2eximi jca impbii bitri $.
$}
$( Two equivalent expressions for double existential uniqueness.
     (Contributed by NM, 19-Feb-2005.) $)
${
	f2eu7_0 $f wff ph $.
	f2eu7_1 $f set x $.
	f2eu7_2 $f set y $.
	2eu7 $p |- ( ( E! x E. y ph /\ E! y E. x ph ) <-> E! x E! y ( E. x ph /\ E. y ph ) ) $= f2eu7_0 f2eu7_1 wex f2eu7_2 weu f2eu7_0 f2eu7_2 wex wa f2eu7_1 weu f2eu7_0 f2eu7_1 wex f2eu7_2 weu f2eu7_0 f2eu7_2 wex f2eu7_1 weu wa f2eu7_0 f2eu7_1 wex f2eu7_0 f2eu7_2 wex wa f2eu7_2 weu f2eu7_1 weu f2eu7_0 f2eu7_2 wex f2eu7_1 weu f2eu7_0 f2eu7_1 wex f2eu7_2 weu wa f2eu7_0 f2eu7_1 wex f2eu7_2 weu f2eu7_0 f2eu7_2 wex f2eu7_1 f2eu7_0 f2eu7_1 wex f2eu7_1 f2eu7_2 f2eu7_0 f2eu7_1 nfe1 nfeu euan f2eu7_0 f2eu7_1 wex f2eu7_0 f2eu7_2 wex wa f2eu7_2 weu f2eu7_0 f2eu7_1 wex f2eu7_2 weu f2eu7_0 f2eu7_2 wex wa f2eu7_1 f2eu7_0 f2eu7_1 wex f2eu7_0 f2eu7_2 wex wa f2eu7_2 weu f2eu7_0 f2eu7_2 wex f2eu7_0 f2eu7_1 wex wa f2eu7_2 weu f2eu7_0 f2eu7_2 wex f2eu7_0 f2eu7_1 wex f2eu7_2 weu wa f2eu7_0 f2eu7_1 wex f2eu7_2 weu f2eu7_0 f2eu7_2 wex wa f2eu7_0 f2eu7_1 wex f2eu7_0 f2eu7_2 wex wa f2eu7_0 f2eu7_2 wex f2eu7_0 f2eu7_1 wex wa f2eu7_2 f2eu7_0 f2eu7_1 wex f2eu7_0 f2eu7_2 wex ancom eubii f2eu7_0 f2eu7_2 wex f2eu7_0 f2eu7_1 wex f2eu7_2 f2eu7_0 f2eu7_2 nfe1 euan f2eu7_0 f2eu7_2 wex f2eu7_0 f2eu7_1 wex f2eu7_2 weu ancom 3bitri eubii f2eu7_0 f2eu7_2 wex f2eu7_1 weu f2eu7_0 f2eu7_1 wex f2eu7_2 weu ancom 3bitr4ri $.
$}
$( Two equivalent expressions for double existential uniqueness.  Curiously,
     we can put ` E! ` on either of the internal conjuncts but not both.  We
     can also commute ` E! x E! y ` using ~ 2eu7 .  (Contributed by NM,
     20-Feb-2005.) $)
${
	f2eu8_0 $f wff ph $.
	f2eu8_1 $f set x $.
	f2eu8_2 $f set y $.
	2eu8 $p |- ( E! x E! y ( E. x ph /\ E. y ph ) <-> E! x E! y ( E! x ph /\ E. y ph ) ) $= f2eu8_0 f2eu8_2 wex f2eu8_1 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu wa f2eu8_0 f2eu8_2 wex f2eu8_1 weu f2eu8_0 f2eu8_1 wex f2eu8_2 weu wa f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex wa f2eu8_2 weu f2eu8_1 weu f2eu8_0 f2eu8_1 wex f2eu8_0 f2eu8_2 wex wa f2eu8_2 weu f2eu8_1 weu f2eu8_0 f2eu8_2 wex f2eu8_1 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_1 wex f2eu8_2 weu f2eu8_0 f2eu8_2 f2eu8_1 2eu2 pm5.32i f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_2 wex wa f2eu8_1 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_2 wex f2eu8_1 weu wa f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex wa f2eu8_2 weu f2eu8_1 weu f2eu8_0 f2eu8_2 wex f2eu8_1 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu wa f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_2 wex f2eu8_1 f2eu8_0 f2eu8_1 weu f2eu8_1 f2eu8_2 f2eu8_0 f2eu8_1 nfeu1 nfeu euan f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex wa f2eu8_2 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_2 wex wa f2eu8_1 f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex wa f2eu8_2 weu f2eu8_0 f2eu8_2 wex f2eu8_0 f2eu8_1 weu wa f2eu8_2 weu f2eu8_0 f2eu8_2 wex f2eu8_0 f2eu8_1 weu f2eu8_2 weu wa f2eu8_0 f2eu8_1 weu f2eu8_2 weu f2eu8_0 f2eu8_2 wex wa f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex wa f2eu8_0 f2eu8_2 wex f2eu8_0 f2eu8_1 weu wa f2eu8_2 f2eu8_0 f2eu8_1 weu f2eu8_0 f2eu8_2 wex ancom eubii f2eu8_0 f2eu8_2 wex f2eu8_0 f2eu8_1 weu f2eu8_2 f2eu8_0 f2eu8_2 nfe1 euan f2eu8_0 f2eu8_2 wex f2eu8_0 f2eu8_1 weu f2eu8_2 weu ancom 3bitri eubii f2eu8_0 f2eu8_2 wex f2eu8_1 weu f2eu8_0 f2eu8_1 weu f2eu8_2 weu ancom 3bitr4ri f2eu8_0 f2eu8_1 f2eu8_2 2eu7 3bitr3ri $.
$}
$( Equality has existential uniqueness.  Special case of ~ eueq1 proved
       using only predicate calculus.  (Contributed by Stefan Allan,
       4-Dec-2008.) $)
${
	$d x y z $.
	ieuequ1_0 $f set z $.
	feuequ1_0 $f set x $.
	feuequ1_1 $f set y $.
	euequ1 $p |- E! x x = y $= feuequ1_0 feuequ1_1 weq feuequ1_0 weu feuequ1_0 feuequ1_1 weq feuequ1_0 wex feuequ1_0 feuequ1_1 weq ieuequ1_0 feuequ1_1 weq wa feuequ1_0 ieuequ1_0 weq wi ieuequ1_0 wal feuequ1_0 wal feuequ1_0 feuequ1_1 a9ev feuequ1_0 feuequ1_1 weq ieuequ1_0 feuequ1_1 weq wa feuequ1_0 ieuequ1_0 weq wi feuequ1_0 ieuequ1_0 feuequ1_0 ieuequ1_0 feuequ1_1 equtr2 gen2 feuequ1_0 feuequ1_1 weq ieuequ1_0 feuequ1_1 weq feuequ1_0 ieuequ1_0 feuequ1_0 ieuequ1_0 feuequ1_1 equequ1 eu4 mpbir2an $.
$}
$( Two ways to express "only one thing exists."  The left-hand side
       requires only one variable to express this.  Both sides are false in set
       theory; see theorem ~ dtru .  (Contributed by NM, 5-Apr-2004.) $)
${
	$d x y $.
	fexists1_0 $f set x $.
	fexists1_1 $f set y $.
	exists1 $p |- ( E! x x = x <-> A. x x = y ) $= fexists1_0 cv fexists1_0 cv wceq fexists1_0 weu fexists1_0 cv fexists1_0 cv wceq fexists1_0 cv fexists1_1 cv wceq wb fexists1_0 wal fexists1_1 wex fexists1_0 cv fexists1_1 cv wceq fexists1_0 wal fexists1_1 wex fexists1_0 cv fexists1_1 cv wceq fexists1_0 wal fexists1_0 cv fexists1_0 cv wceq fexists1_0 fexists1_1 df-eu fexists1_0 cv fexists1_1 cv wceq fexists1_0 wal fexists1_0 cv fexists1_0 cv wceq fexists1_0 cv fexists1_1 cv wceq wb fexists1_0 wal fexists1_1 fexists1_0 cv fexists1_1 cv wceq fexists1_0 cv fexists1_0 cv wceq fexists1_0 cv fexists1_1 cv wceq wb fexists1_0 fexists1_0 cv fexists1_1 cv wceq fexists1_0 cv fexists1_1 cv wceq fexists1_0 cv fexists1_0 cv wceq wb fexists1_0 cv fexists1_0 cv wceq fexists1_0 cv fexists1_1 cv wceq wb fexists1_0 cv fexists1_0 cv wceq fexists1_0 cv fexists1_1 cv wceq fexists1_0 equid tbt fexists1_0 cv fexists1_1 cv wceq fexists1_0 cv fexists1_0 cv wceq bicom bitri albii exbii fexists1_0 cv fexists1_1 cv wceq fexists1_0 wal fexists1_1 fexists1_0 fexists1_1 fexists1_1 nfae 19.9 3bitr2i $.
$}
$( A condition implying that at least two things exist.  (Contributed by
       NM, 10-Apr-2004.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$d x y $.
	iexists2_0 $f set y $.
	fexists2_0 $f wff ph $.
	fexists2_1 $f set x $.
	exists2 $p |- ( ( E. x ph /\ E. x -. ph ) -> -. E! x x = x ) $= fexists2_0 fexists2_1 wex fexists2_0 wn fexists2_1 wex fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu wn fexists2_0 fexists2_1 wex fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu fexists2_0 wn fexists2_1 wex fexists2_0 fexists2_1 wex fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu fexists2_0 fexists2_1 wal fexists2_0 wn fexists2_1 wex wn fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu fexists2_0 fexists2_1 wex fexists2_0 fexists2_1 wal fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu fexists2_0 fexists2_0 fexists2_1 wal fexists2_1 fexists2_1 cv fexists2_1 cv wceq fexists2_1 nfeu1 fexists2_0 fexists2_1 nfa1 fexists2_1 cv fexists2_1 cv wceq fexists2_1 weu fexists2_1 cv iexists2_0 cv wceq fexists2_1 wal fexists2_0 fexists2_0 fexists2_1 wal wi fexists2_1 iexists2_0 exists1 fexists2_0 fexists2_1 iexists2_0 ax16 sylbi exlimd com12 fexists2_0 fexists2_1 alex syl6ib con2d imp $.
$}

