$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Introduce_the_Axiom_of_Replacement.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Derive the Axiom of Separation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Separation Scheme, which is an axiom scheme of Zermelo's original
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
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	$d y z ph w $.
	iaxsep_0 $f set w $.
	faxsep_0 $f wff ph $.
	faxsep_1 $f set x $.
	faxsep_2 $f set y $.
	faxsep_3 $f set z $.
	axsep $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $= faxsep_1 sup_set_class faxsep_2 sup_set_class wcel iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex wb faxsep_1 wal faxsep_2 wex faxsep_1 sup_set_class faxsep_2 sup_set_class wcel faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa wb faxsep_1 wal faxsep_2 wex iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa faxsep_1 sup_set_class faxsep_2 sup_set_class wceq wi faxsep_1 wal faxsep_2 wex wi faxsep_1 sup_set_class faxsep_2 sup_set_class wcel iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex wb faxsep_1 wal faxsep_2 wex iaxsep_0 iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa iaxsep_0 faxsep_1 faxsep_2 faxsep_3 iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa faxsep_2 nfv axrep5 iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa faxsep_1 sup_set_class faxsep_2 sup_set_class wceq wi faxsep_1 wal faxsep_2 iaxsep_0 faxsep_2 sup_set_class iaxsep_0 sup_set_class wceq iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa faxsep_1 sup_set_class faxsep_2 sup_set_class wceq wi faxsep_1 wal iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_2 sup_set_class iaxsep_0 sup_set_class wceq iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa faxsep_1 sup_set_class faxsep_2 sup_set_class wceq wi faxsep_1 faxsep_2 sup_set_class iaxsep_0 sup_set_class wceq iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_1 sup_set_class faxsep_2 sup_set_class wceq faxsep_0 faxsep_2 sup_set_class iaxsep_0 sup_set_class wceq iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_2 sup_set_class faxsep_1 sup_set_class wceq faxsep_1 sup_set_class faxsep_2 sup_set_class wceq faxsep_2 iaxsep_0 faxsep_1 equtr faxsep_2 faxsep_1 equcomi syl6 adantrd alrimiv a1d spimev mpg faxsep_1 sup_set_class faxsep_2 sup_set_class wcel iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex wb faxsep_1 wal faxsep_1 sup_set_class faxsep_2 sup_set_class wcel faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa wb faxsep_1 wal faxsep_2 faxsep_1 sup_set_class faxsep_2 sup_set_class wcel iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex wb faxsep_1 sup_set_class faxsep_2 sup_set_class wcel faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa wb faxsep_1 iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa faxsep_1 sup_set_class faxsep_2 sup_set_class wcel iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 wex iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa wa iaxsep_0 wex faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa wa iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq faxsep_0 wa wa iaxsep_0 iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 an12 exbii iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa iaxsep_0 faxsep_1 faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 wa iaxsep_0 nfv iaxsep_0 sup_set_class faxsep_1 sup_set_class wceq iaxsep_0 sup_set_class faxsep_3 sup_set_class wcel faxsep_1 sup_set_class faxsep_3 sup_set_class wcel faxsep_0 iaxsep_0 faxsep_1 faxsep_3 elequ1 anbi1d equsex bitr3i bibi2i albii exbii mpbi $.
$}
$( The Axiom of Separation of ZF set theory.  See ~ axsep for more
       information.  It was derived as ~ axsep above and is therefore
       redundant, but we state it as a separate axiom here so that its uses can
       be identified more easily.  (Contributed by NM, 11-Sep-2006.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	$d y z ph $.
	fax-sep_0 $f wff ph $.
	fax-sep_1 $f set x $.
	fax-sep_2 $f set y $.
	fax-sep_3 $f set z $.
	ax-sep $a |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $.
$}
$( A less restrictive version of the Separation Scheme ~ axsep , where
       variables ` x ` and ` z ` can both appear free in the wff ` ph ` , which
       can therefore be thought of as ` ph ( x , z ) ` .  This version was
       derived from the more restrictive ~ ax-sep with no additional set theory
       axioms.  (Contributed by NM, 10-Dec-2006.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	$d y ph w $.
	$d z w $.
	iaxsep2_0 $f set w $.
	faxsep2_0 $f wff ph $.
	faxsep2_1 $f set x $.
	faxsep2_2 $f set y $.
	faxsep2_3 $f set z $.
	axsep2 $p |- E. y A. x ( x e. y <-> ( x e. z /\ ph ) ) $= faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa wb faxsep2_1 wal faxsep2_2 wex faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wb faxsep2_1 wal faxsep2_2 wex iaxsep2_0 faxsep2_3 iaxsep2_0 sup_set_class faxsep2_3 sup_set_class wceq faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa wb faxsep2_1 wal faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wb faxsep2_1 wal faxsep2_2 iaxsep2_0 sup_set_class faxsep2_3 sup_set_class wceq faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa wb faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wb faxsep2_1 iaxsep2_0 sup_set_class faxsep2_3 sup_set_class wceq faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa faxsep2_1 sup_set_class faxsep2_2 sup_set_class wcel iaxsep2_0 sup_set_class faxsep2_3 sup_set_class wceq faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa wa faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa iaxsep2_0 sup_set_class faxsep2_3 sup_set_class wceq faxsep2_1 sup_set_class iaxsep2_0 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa iaxsep2_0 sup_set_class faxsep2_3 sup_set_class faxsep2_1 sup_set_class eleq2 anbi1d faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 anabs5 syl6bb bibi2d albidv exbidv faxsep2_1 sup_set_class faxsep2_3 sup_set_class wcel faxsep2_0 wa faxsep2_1 faxsep2_2 iaxsep2_0 ax-sep chvarv $.
$}
$( Separation Scheme (Aussonderung) using a class variable.  To derive this
       from ~ ax-sep , we invoke the Axiom of Extensionality (indirectly via
       ~ vtocl ), which is needed for the justification of class variable
       notation.

       If we omit the requirement that ` y ` not occur in ` ph ` , we can
       derive a contradiction, as ~ notzfaus shows.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v z $.
	$d x y A z $.
	$d y ph z $.
	izfauscl_0 $f set z $.
	fzfauscl_0 $f wff ph $.
	fzfauscl_1 $f set x $.
	fzfauscl_2 $f set y $.
	fzfauscl_3 $f class A $.
	ezfauscl_0 $e |- A e. _V $.
	zfauscl $p |- E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $= fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class izfauscl_0 sup_set_class wcel fzfauscl_0 wa wb fzfauscl_1 wal fzfauscl_2 wex fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class fzfauscl_3 wcel fzfauscl_0 wa wb fzfauscl_1 wal fzfauscl_2 wex izfauscl_0 fzfauscl_3 ezfauscl_0 izfauscl_0 sup_set_class fzfauscl_3 wceq fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class izfauscl_0 sup_set_class wcel fzfauscl_0 wa wb fzfauscl_1 wal fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class fzfauscl_3 wcel fzfauscl_0 wa wb fzfauscl_1 wal fzfauscl_2 izfauscl_0 sup_set_class fzfauscl_3 wceq fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class izfauscl_0 sup_set_class wcel fzfauscl_0 wa wb fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel fzfauscl_1 sup_set_class fzfauscl_3 wcel fzfauscl_0 wa wb fzfauscl_1 izfauscl_0 sup_set_class fzfauscl_3 wceq fzfauscl_1 sup_set_class izfauscl_0 sup_set_class wcel fzfauscl_0 wa fzfauscl_1 sup_set_class fzfauscl_3 wcel fzfauscl_0 wa fzfauscl_1 sup_set_class fzfauscl_2 sup_set_class wcel izfauscl_0 sup_set_class fzfauscl_3 wceq fzfauscl_1 sup_set_class izfauscl_0 sup_set_class wcel fzfauscl_1 sup_set_class fzfauscl_3 wcel fzfauscl_0 izfauscl_0 sup_set_class fzfauscl_3 fzfauscl_1 sup_set_class eleq2 anbi1d bibi2d albidv exbidv fzfauscl_0 fzfauscl_1 fzfauscl_2 izfauscl_0 ax-sep vtocl $.
$}
$( Convert implication to equivalence using the Separation Scheme
       (Aussonderung) ~ ax-sep .  Similar to Theorem 1.3ii of [BellMachover]
       p. 463.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$d x ph z $.
	$d x y z $.
	ibm1.3ii_0 $f set z $.
	fbm1.3ii_0 $f wff ph $.
	fbm1.3ii_1 $f set x $.
	fbm1.3ii_2 $f set y $.
	ebm1.3ii_0 $e |- E. x A. y ( ph -> y e. x ) $.
	bm1.3ii $p |- E. x A. y ( y e. x <-> ph ) $= fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 wex wa ibm1.3ii_0 wex fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_0 wb fbm1.3ii_2 wal fbm1.3ii_1 wex fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 wex ibm1.3ii_0 fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal ibm1.3ii_0 wex fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 wex fbm1.3ii_0 fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_1 wex fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal ibm1.3ii_0 wex ebm1.3ii_0 fbm1.3ii_0 fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_1 ibm1.3ii_0 fbm1.3ii_1 sup_set_class ibm1.3ii_0 sup_set_class wceq fbm1.3ii_0 fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel wi fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 fbm1.3ii_1 sup_set_class ibm1.3ii_0 sup_set_class wceq fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 fbm1.3ii_1 ibm1.3ii_0 fbm1.3ii_2 elequ2 imbi2d albidv cbvexv mpbi fbm1.3ii_0 fbm1.3ii_2 fbm1.3ii_1 ibm1.3ii_0 ax-sep pm3.2i exan fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 wex wa fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_0 wb fbm1.3ii_2 wal fbm1.3ii_1 wex ibm1.3ii_0 fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 wex wa fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal wa fbm1.3ii_1 wex fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_0 wb fbm1.3ii_2 wal fbm1.3ii_1 wex fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal fbm1.3ii_1 19.42v fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 wal fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 wal wa fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_0 wb fbm1.3ii_2 wal fbm1.3ii_1 fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel wi fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_0 wa wb fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel fbm1.3ii_0 wb fbm1.3ii_2 fbm1.3ii_0 fbm1.3ii_2 sup_set_class ibm1.3ii_0 sup_set_class wcel fbm1.3ii_2 sup_set_class fbm1.3ii_1 sup_set_class wcel bimsc1 alanimi eximi sylbir exlimiv ax-mp $.
$}
$( Derive a weakened version of ~ ax9 ( i.e. ~ ax9v ), where ` x ` and
       ` y ` must be distinct, from Separation ~ ax-sep and Extensionality
       ~ ax-ext .  See ~ ax9 for the derivation of ~ ax9 from ~ ax9v .
       (Contributed by NM, 12-Nov-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	iax9vsep_0 $f set z $.
	fax9vsep_0 $f set x $.
	fax9vsep_1 $f set y $.
	ax9vsep $p |- -. A. x -. x = y $= fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq fax9vsep_0 wex fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq wn fax9vsep_0 wal wn iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa wb iax9vsep_0 wal fax9vsep_0 wex fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq fax9vsep_0 wex iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi iax9vsep_0 fax9vsep_0 fax9vsep_1 ax-sep iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa wb iax9vsep_0 wal fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq fax9vsep_0 iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa wb iax9vsep_0 wal iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel wb iax9vsep_0 wal fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa wb iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel wb iax9vsep_0 iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel wb iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa wb iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi wa iax9vsep_0 sup_set_class fax9vsep_0 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq wi iax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wcel iax9vsep_0 sup_set_class iax9vsep_0 sup_set_class wceq id biantru bibi2i biimpri alimi fax9vsep_0 fax9vsep_1 iax9vsep_0 ax-ext syl eximi ax-mp fax9vsep_0 sup_set_class fax9vsep_1 sup_set_class wceq fax9vsep_0 df-ex mpbi $.
$}

