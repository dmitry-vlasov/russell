$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Introduce_the_Axiom_of_Replacement.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Derive the Axiom of Separation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Separation Scheme, which is an axiom scheme of Zermelo's original
       theory.  Scheme Sep of [BellMachover] p. 463.  As we show here, it is
       redundant if we assume Replacement in the form of ~ ax-rep .  Some
       textbooks present Separation as a separate axiom scheme in order to show
       that much of set theory can be derived without the stronger
       Replacement.  The Separation Scheme is a weak form of Frege's Axiom of
       Comprehension, conditioning it (with ` x e. z ` ) so that it asserts the
       existence of a collection only if it is smaller than some other
       collection ` z ` that already exists.  This prevents Russell's paradox
       ~ ru .  In some texts, this scheme is called "Aussonderung" or the
       Subset Axiom.

       The variable ` x ` can appear free in the wff ` ph ` , which in
       textbooks is often written ` ph ( x ) ` .  To specify this in the
       Metamath language, we _omit_ the distinct variable requirement ($d) that
       ` x ` not appear in ` ph ` .

       For a version using a class variable, see ~ zfauscl , which requires the
       Axiom of Extensionality as well as Separation for its derivation.

       If we omit the requirement that ` y ` not occur in ` ph ` , we can
       derive a contradiction, as ~ notzfaus shows (contradicting ~ zfauscl ).
       However, as ~ axsep2 shows, we can eliminate the restriction that ` z `
       not occur in ` ph ` .

       Note: the distinct variable restriction that ` z ` not occur in ` ph `
       is actually redundant in this particular proof, but we keep it since its
       purpose is to demonstrate the derivation of the exact ~ ax-sep from
       ~ ax-rep .

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-sep below so that the uses of the Axiom of Separation can be more
       easily identified.  (Contributed by NM, 11-Sep-2006.)
       (New usage is discouraged.) $)

${
	$v ph x y z  $.
	$d x y z w  $.
	$d y z ph w  $.
	f0_axsep $f wff ph $.
	f1_axsep $f set x $.
	f2_axsep $f set y $.
	f3_axsep $f set z $.
	i0_axsep $f set w $.
	p_axsep $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $= i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa f2_axsep p_nfv i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa i0_axsep f1_axsep f2_axsep f3_axsep p_axrep5 f2_axsep i0_axsep f1_axsep p_equtr f2_axsep f1_axsep p_equcomi f2_axsep a_sup_set_class i0_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f2_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq p_syl6 f2_axsep a_sup_set_class i0_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq f0_axsep p_adantrd f2_axsep a_sup_set_class i0_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq a_wi f1_axsep p_alrimiv f2_axsep a_sup_set_class i0_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq a_wi f1_axsep a_wal i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel p_a1d i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq a_wi f1_axsep a_wal f2_axsep i0_axsep p_spimev i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wceq a_wi f1_axsep a_wal f2_axsep a_wex a_wi f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex a_wb f1_axsep a_wal f2_axsep a_wex i0_axsep p_mpg i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep p_an12 i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa a_wa i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep p_exbii f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa i0_axsep p_nfv i0_axsep f1_axsep f3_axsep p_elequ1 i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep p_anbi1d i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa i0_axsep f1_axsep p_equsex i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa a_wa i0_axsep a_wex f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa p_bitr3i i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel p_bibi2i f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex a_wb f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa a_wb f1_axsep p_albii f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex a_wb f1_axsep a_wal f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa a_wb f1_axsep a_wal f2_axsep p_exbii f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel i0_axsep a_sup_set_class f1_axsep a_sup_set_class a_wceq f0_axsep a_wa a_wa i0_axsep a_wex a_wb f1_axsep a_wal f2_axsep a_wex f1_axsep a_sup_set_class f2_axsep a_sup_set_class a_wcel f1_axsep a_sup_set_class f3_axsep a_sup_set_class a_wcel f0_axsep a_wa a_wb f1_axsep a_wal f2_axsep a_wex p_mpbi $.
$}

$(The Axiom of Separation of ZF set theory.  See ~ axsep for more
       information.  It was derived as ~ axsep above and is therefore
       redundant, but we state it as a separate axiom here so that its uses can
       be identified more easily.  (Contributed by NM, 11-Sep-2006.) $)

${
	$v ph x y z  $.
	$d x y z  $.
	$d y z ph  $.
	f0_ax-sep $f wff ph $.
	f1_ax-sep $f set x $.
	f2_ax-sep $f set y $.
	f3_ax-sep $f set z $.
	a_ax-sep $a |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $.
$}

$(A less restrictive version of the Separation Scheme ~ axsep , where
       variables ` x ` and ` z ` can both appear free in the wff ` ph ` , which
       can therefore be thought of as ` ph ( x , z ) ` .  This version was
       derived from the more restrictive ~ ax-sep with no additional set theory
       axioms.  (Contributed by NM, 10-Dec-2006.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)

${
	$v ph x y z  $.
	$d x y z w  $.
	$d y ph w  $.
	$d z w  $.
	f0_axsep2 $f wff ph $.
	f1_axsep2 $f set x $.
	f2_axsep2 $f set y $.
	f3_axsep2 $f set z $.
	i0_axsep2 $f set w $.
	p_axsep2 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $= i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class f1_axsep2 a_sup_set_class p_eleq2 i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wceq f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa p_anbi1d f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 p_anabs5 i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wceq f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa p_syl6bb i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wceq f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel p_bibi2d i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wceq f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa a_wb f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wb f1_axsep2 p_albidv i0_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wceq f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa a_wb f1_axsep2 a_wal f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wb f1_axsep2 a_wal f2_axsep2 p_exbidv f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa f1_axsep2 f2_axsep2 i0_axsep2 a_ax-sep f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class i0_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wa a_wb f1_axsep2 a_wal f2_axsep2 a_wex f1_axsep2 a_sup_set_class f2_axsep2 a_sup_set_class a_wcel f1_axsep2 a_sup_set_class f3_axsep2 a_sup_set_class a_wcel f0_axsep2 a_wa a_wb f1_axsep2 a_wal f2_axsep2 a_wex i0_axsep2 f3_axsep2 p_chvarv $.
$}

$(Separation Scheme (Aussonderung) using a class variable.  To derive this
       from ~ ax-sep , we invoke the Axiom of Extensionality (indirectly via
       ~ vtocl ), which is needed for the justification of class variable
       notation.

       If we omit the requirement that ` y ` not occur in ` ph ` , we can
       derive a contradiction, as ~ notzfaus shows.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v ph x y A  $.
	$d x y A z  $.
	$d y ph z  $.
	f0_zfauscl $f wff ph $.
	f1_zfauscl $f set x $.
	f2_zfauscl $f set y $.
	f3_zfauscl $f class A $.
	i0_zfauscl $f set z $.
	e0_zfauscl $e |- A e. _V $.
	p_zfauscl $p |- E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $= e0_zfauscl i0_zfauscl a_sup_set_class f3_zfauscl f1_zfauscl a_sup_set_class p_eleq2 i0_zfauscl a_sup_set_class f3_zfauscl a_wceq f1_zfauscl a_sup_set_class i0_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class f3_zfauscl a_wcel f0_zfauscl p_anbi1d i0_zfauscl a_sup_set_class f3_zfauscl a_wceq f1_zfauscl a_sup_set_class i0_zfauscl a_sup_set_class a_wcel f0_zfauscl a_wa f1_zfauscl a_sup_set_class f3_zfauscl a_wcel f0_zfauscl a_wa f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel p_bibi2d i0_zfauscl a_sup_set_class f3_zfauscl a_wceq f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class i0_zfauscl a_sup_set_class a_wcel f0_zfauscl a_wa a_wb f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class f3_zfauscl a_wcel f0_zfauscl a_wa a_wb f1_zfauscl p_albidv i0_zfauscl a_sup_set_class f3_zfauscl a_wceq f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class i0_zfauscl a_sup_set_class a_wcel f0_zfauscl a_wa a_wb f1_zfauscl a_wal f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class f3_zfauscl a_wcel f0_zfauscl a_wa a_wb f1_zfauscl a_wal f2_zfauscl p_exbidv f0_zfauscl f1_zfauscl f2_zfauscl i0_zfauscl a_ax-sep f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class i0_zfauscl a_sup_set_class a_wcel f0_zfauscl a_wa a_wb f1_zfauscl a_wal f2_zfauscl a_wex f1_zfauscl a_sup_set_class f2_zfauscl a_sup_set_class a_wcel f1_zfauscl a_sup_set_class f3_zfauscl a_wcel f0_zfauscl a_wa a_wb f1_zfauscl a_wal f2_zfauscl a_wex i0_zfauscl f3_zfauscl p_vtocl $.
$}

$(Convert implication to equivalence using the Separation Scheme
       (Aussonderung) ~ ax-sep .  Similar to Theorem 1.3ii of [BellMachover]
       p. 463.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v ph x y  $.
	$d x ph z  $.
	$d x y z  $.
	f0_bm1.3ii $f wff ph $.
	f1_bm1.3ii $f set x $.
	f2_bm1.3ii $f set y $.
	i0_bm1.3ii $f set z $.
	e0_bm1.3ii $e |- E. x A. y ( ph -> y e. x ) $.
	p_bm1.3ii $p |- E. x A. y ( y e. x <-> ph ) $= e0_bm1.3ii f1_bm1.3ii i0_bm1.3ii f2_bm1.3ii p_elequ2 f1_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wceq f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii p_imbi2d f1_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wceq f0_bm1.3ii f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel a_wi f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii p_albidv f0_bm1.3ii f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f1_bm1.3ii i0_bm1.3ii p_cbvexv f0_bm1.3ii f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f1_bm1.3ii a_wex f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal i0_bm1.3ii a_wex p_mpbi f0_bm1.3ii f2_bm1.3ii f1_bm1.3ii i0_bm1.3ii a_ax-sep f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal i0_bm1.3ii a_wex f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex p_pm3.2i f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex i0_bm1.3ii p_exan f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii p_19.42v f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel p_bimsc1 f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wb f2_bm1.3ii p_alanimi f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal a_wa f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wb f2_bm1.3ii a_wal f1_bm1.3ii p_eximi f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex a_wa f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal a_wa f1_bm1.3ii a_wex f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex p_sylbir f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex a_wa f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex i0_bm1.3ii p_exlimiv f0_bm1.3ii f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel a_wi f2_bm1.3ii a_wal f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f2_bm1.3ii a_sup_set_class i0_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wa a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex a_wa i0_bm1.3ii a_wex f2_bm1.3ii a_sup_set_class f1_bm1.3ii a_sup_set_class a_wcel f0_bm1.3ii a_wb f2_bm1.3ii a_wal f1_bm1.3ii a_wex a_ax-mp $.
$}

$(Derive a weakened version of ~ ax9 ( i.e. ~ ax9v ), where ` x ` and
       ` y ` must be distinct, from Separation ~ ax-sep and Extensionality
       ~ ax-ext .  See ~ ax9 for the derivation of ~ ax9 from ~ ax9v .
       (Contributed by NM, 12-Nov-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v x y  $.
	$d x y z  $.
	f0_ax9vsep $f set x $.
	f1_ax9vsep $f set y $.
	i0_ax9vsep $f set z $.
	p_ax9vsep $p |- -. A. x -. x = y $= i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi i0_ax9vsep f0_ax9vsep f1_ax9vsep a_ax-sep i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq p_id i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel p_biantru i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel p_bibi2i i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel a_wb i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa a_wb p_biimpri i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa a_wb i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel a_wb i0_ax9vsep p_alimi f0_ax9vsep f1_ax9vsep i0_ax9vsep a_ax-ext i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa a_wb i0_ax9vsep a_wal i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel a_wb i0_ax9vsep a_wal f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq p_syl i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa a_wb i0_ax9vsep a_wal f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq f0_ax9vsep p_eximi i0_ax9vsep a_sup_set_class f0_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wcel i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq i0_ax9vsep a_sup_set_class i0_ax9vsep a_sup_set_class a_wceq a_wi a_wa a_wb i0_ax9vsep a_wal f0_ax9vsep a_wex f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq f0_ax9vsep a_wex a_ax-mp f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq f0_ax9vsep a_df-ex f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq f0_ax9vsep a_wex f0_ax9vsep a_sup_set_class f1_ax9vsep a_sup_set_class a_wceq a_wn f0_ax9vsep a_wal a_wn p_mpbi $.
$}


