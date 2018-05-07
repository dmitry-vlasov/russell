$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Introduce the Axiom of Replacement

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Axiom of Replacement.  An axiom scheme of Zermelo-Fraenkel set theory.
       Axiom 5 of [TakeutiZaring] p. 19.  It tells us that the image of any set
       under a function is also a set (see the variant ~ funimaex ).  Although
       ` ph ` may be any wff whatsoever, this axiom is useful (i.e. its
       antecedent is satisfied) when we are given some function and ` ph `
       encodes the predicate "the value of the function at ` w ` is ` z ` ."
       Thus, ` ph ` will ordinarily have free variables ` w ` and ` z ` - think
       of it informally as ` ph ( w , z ) ` .  We prefix ` ph ` with the
       quantifier ` A. y ` in order to "protect" the axiom from any ` ph `
       containing ` y ` , thus allowing us to eliminate any restrictions on
       ` ph ` .  This makes the axiom usable in a formalization that omits the
       logically redundant axiom ~ ax-17 .  Another common variant is derived
       as ~ axrep5 , where you can find some further remarks.  A slightly more
       compact version is shown as ~ axrep2 .  A quite different variant is
       ~ zfrep6 , which if used in place of ~ ax-rep would also require that
       the Separation Scheme ~ axsep be stated as a separate axiom.

       There is very a strong generalization of Replacement that doesn't demand
       function-like behavior of ` ph ` .  Two versions of this generalization
       are called the Collection Principle ~ cp and the Boundedness Axiom
       ~ bnd .

       Many developments of set theory distinguish the uses of Replacement from
       uses the weaker axioms of Separation ~ axsep , Null Set ~ axnul , and
       Pairing ~ axpr , all of which we derive from Replacement.  In order to
       make it easier to identify the uses of those redundant axioms, we
       restate them as axioms ~ ax-sep , ~ ax-nul , and ~ ax-pr below the
       theorems that prove them.  (Contributed by NM, 23-Dec-1993.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	fax-rep_0 $f wff ph $.
	fax-rep_1 $f set x $.
	fax-rep_2 $f set y $.
	fax-rep_3 $f set z $.
	fax-rep_4 $f set w $.
	ax-rep $a |- ( A. w E. y A. z ( A. y ph -> z = y ) -> E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) ) $.
$}
$( The version of the Axiom of Replacement used in the Metamath Solitaire
       applet ~ http://us.metamath.org/mmsolitaire/mms.html .  Equivalence is
       shown via the path ~ ax-rep ` -> ` ~ axrep1 ` -> ` ~ axrep2 ` -> `
       ~ axrepnd ` -> ` ~ zfcndrep = ~ ax-rep .  (Contributed by NM,
       19-Nov-2005.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w y ph $.
	$d w x y z $.
	iaxrep1_0 $f set w $.
	faxrep1_0 $f wff ph $.
	faxrep1_1 $f set x $.
	faxrep1_2 $f set y $.
	faxrep1_3 $f set z $.
	axrep1 $p |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ ph ) ) ) $= faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 wal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 wex wi faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 wal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 wex wi iaxrep1_0 faxrep1_2 iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 wex faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 wex faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 wal iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 wa faxrep1_1 iaxrep1_0 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_1 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_0 iaxrep1_0 sup_set_class faxrep1_2 sup_set_class faxrep1_1 sup_set_class eleq2 anbi1d exbidv bibi2d albidv exbidv imbi2d faxrep1_0 faxrep1_2 wal faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 wal faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_2 wex faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 wal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_1 wex faxrep1_0 iaxrep1_0 faxrep1_2 faxrep1_3 faxrep1_1 ax-rep faxrep1_0 faxrep1_2 wal faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 wex faxrep1_1 faxrep1_0 faxrep1_2 wal faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 wal faxrep1_2 faxrep1_0 faxrep1_2 wal faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq wi faxrep1_3 faxrep1_0 faxrep1_2 wal faxrep1_0 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wceq faxrep1_0 faxrep1_2 faxrep1_0 faxrep1_2 nfv 19.3 imbi1i albii exbii albii faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_2 faxrep1_1 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex wb faxrep1_1 faxrep1_3 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex faxrep1_1 faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 nfv faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 nfe1 nfbi nfal faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 wal faxrep1_2 nfv faxrep1_2 sup_set_class faxrep1_1 sup_set_class wceq faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex wb faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_3 faxrep1_2 sup_set_class faxrep1_1 sup_set_class wceq faxrep1_3 sup_set_class faxrep1_2 sup_set_class wcel faxrep1_3 sup_set_class faxrep1_1 sup_set_class wcel faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex faxrep1_2 faxrep1_1 faxrep1_3 elequ2 faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 wex faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 wex wb faxrep1_2 sup_set_class faxrep1_1 sup_set_class wceq faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 wal wa faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 wa faxrep1_1 faxrep1_0 faxrep1_2 wal faxrep1_0 faxrep1_1 sup_set_class iaxrep1_0 sup_set_class wcel faxrep1_0 faxrep1_2 faxrep1_0 faxrep1_2 nfv 19.3 anbi2i exbii a1i bibi12d albidv cbvex 3imtr3i chvarv 19.35ri $.
$}
$( Axiom of Replacement expressed with the fewest number of different
       variables and without any restrictions on ` ph ` .  (Contributed by NM,
       15-Aug-2003.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w ph $.
	$d w x y z $.
	iaxrep2_0 $f set w $.
	faxrep2_0 $f wff ph $.
	faxrep2_1 $f set x $.
	faxrep2_2 $f set y $.
	faxrep2_3 $f set z $.
	axrep2 $p |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) $= faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 wex faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 wex faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 wex faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 wex iaxrep2_0 faxrep2_2 faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi iaxrep2_0 faxrep2_1 faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal iaxrep2_0 faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 nfe1 faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal iaxrep2_0 nfv nfim nfex iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 iaxrep2_0 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_1 sup_set_class iaxrep2_0 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal iaxrep2_0 faxrep2_2 faxrep2_1 elequ2 anbi1d exbidv bibi2d albidv imbi2d exbidv faxrep2_0 faxrep2_2 wal faxrep2_1 iaxrep2_0 faxrep2_3 axrep1 chvar faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal wi faxrep2_1 faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 wex faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_3 sup_set_class faxrep2_1 sup_set_class wcel faxrep2_1 sup_set_class faxrep2_2 sup_set_class wcel faxrep2_0 faxrep2_2 wal wa faxrep2_1 wex wb faxrep2_3 wal faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 wex faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 wex faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 wex faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 faxrep2_0 faxrep2_2 wal faxrep2_0 faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_0 faxrep2_2 sp imim1i alimi eximi faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 wal faxrep2_2 iaxrep2_0 faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_3 wal iaxrep2_0 nfv faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_2 faxrep2_3 faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq faxrep2_2 faxrep2_0 faxrep2_2 nfa1 faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq faxrep2_2 nfv nfim nfal faxrep2_2 sup_set_class iaxrep2_0 sup_set_class wceq faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq wi faxrep2_0 faxrep2_2 wal faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq wi faxrep2_3 faxrep2_2 sup_set_class iaxrep2_0 sup_set_class wceq faxrep2_3 sup_set_class faxrep2_2 sup_set_class wceq faxrep2_3 sup_set_class iaxrep2_0 sup_set_class wceq faxrep2_0 faxrep2_2 wal faxrep2_2 iaxrep2_0 faxrep2_3 equequ2 imbi2d albidv cbvex sylib imim1i eximi ax-mp $.
$}
$( Axiom of Replacement slightly strengthened from ~ axrep2 ; ` w ` may
       occur free in ` ph ` .  (Contributed by NM, 2-Jan-1997.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d w x y z $.
	faxrep3_0 $f wff ph $.
	faxrep3_1 $f set x $.
	faxrep3_2 $f set y $.
	faxrep3_3 $f set z $.
	faxrep3_4 $f set w $.
	axrep3 $p |- E. x ( E. y A. z ( ph -> z = y ) -> A. z ( z e. x <-> E. x ( x e. w /\ A. y ph ) ) ) $= faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal wi faxrep3_1 wex faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal wi faxrep3_1 wex faxrep3_2 faxrep3_4 faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal wi faxrep3_2 faxrep3_1 faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal faxrep3_2 faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 nfe1 faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_2 faxrep3_3 faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex faxrep3_2 faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_2 nfv faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_2 faxrep3_1 faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal faxrep3_2 faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_2 nfv faxrep3_0 faxrep3_2 nfa1 nfan nfex nfbi nfal nfim nfex faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal wi faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal wi faxrep3_1 faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 wal faxrep3_0 faxrep3_3 sup_set_class faxrep3_2 sup_set_class wceq wi faxrep3_3 wal faxrep3_2 wex faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex wb faxrep3_3 faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 wex faxrep3_3 sup_set_class faxrep3_1 sup_set_class wcel faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal wa faxrep3_1 faxrep3_2 sup_set_class faxrep3_4 sup_set_class wceq faxrep3_1 sup_set_class faxrep3_2 sup_set_class wcel faxrep3_1 sup_set_class faxrep3_4 sup_set_class wcel faxrep3_0 faxrep3_2 wal faxrep3_2 faxrep3_4 faxrep3_1 elequ2 anbi1d exbidv bibi2d albidv imbi2d exbidv faxrep3_0 faxrep3_1 faxrep3_2 faxrep3_3 axrep2 chvar $.
$}
$( A more traditional version of the Axiom of Replacement.  (Contributed by
       NM, 14-Aug-1994.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	faxrep4_0 $f wff ph $.
	faxrep4_1 $f set x $.
	faxrep4_2 $f set y $.
	faxrep4_3 $f set z $.
	faxrep4_4 $f set w $.
	eaxrep4_0 $e |- F/ z ph $.
	axrep4 $p |- ( A. x E. z A. y ( ph -> y = z ) -> E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) ) $= faxrep4_0 faxrep4_2 sup_set_class faxrep4_3 sup_set_class wceq wi faxrep4_2 wal faxrep4_3 wex faxrep4_1 wal faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex wb faxrep4_2 wal faxrep4_1 wex faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex wb faxrep4_2 wal faxrep4_3 wex faxrep4_0 faxrep4_2 sup_set_class faxrep4_3 sup_set_class wceq wi faxrep4_2 wal faxrep4_3 wex faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex wb faxrep4_2 wal faxrep4_1 faxrep4_0 faxrep4_1 faxrep4_3 faxrep4_2 faxrep4_4 axrep3 19.35i faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex wb faxrep4_2 wal faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex wb faxrep4_2 wal faxrep4_1 faxrep4_3 faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex wb faxrep4_3 faxrep4_2 faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex faxrep4_3 faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_3 nfv faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_3 faxrep4_1 faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal faxrep4_3 faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_3 nfv faxrep4_0 faxrep4_3 nfa1 nfan nfex nfbi nfal faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex wb faxrep4_1 faxrep4_2 faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex faxrep4_1 faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 nfv faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 nfe1 nfbi nfal faxrep4_1 sup_set_class faxrep4_3 sup_set_class wceq faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex wb faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex wb faxrep4_2 faxrep4_1 sup_set_class faxrep4_3 sup_set_class wceq faxrep4_2 sup_set_class faxrep4_1 sup_set_class wcel faxrep4_2 sup_set_class faxrep4_3 sup_set_class wcel faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex faxrep4_1 faxrep4_3 faxrep4_2 elequ2 faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 wex faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 wex wb faxrep4_1 sup_set_class faxrep4_3 sup_set_class wceq faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 wal wa faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 wa faxrep4_1 faxrep4_0 faxrep4_3 wal faxrep4_0 faxrep4_1 sup_set_class faxrep4_4 sup_set_class wcel faxrep4_0 faxrep4_3 eaxrep4_0 19.3 anbi2i exbii a1i bibi12d albidv cbvex sylib $.
$}
$( Axiom of Replacement (similar to Axiom Rep of [BellMachover] p. 463).
       The antecedent tells us ` ph ` is analogous to a "function" from ` x `
       to ` y ` (although it is not really a function since it is a wff and not
       a class).  In the consequent we postulate the existence of a set ` z `
       that corresponds to the "image" of ` ph ` restricted to some other set
       ` w ` .  The hypothesis says ` z ` must not be free in ` ph ` .
       (Contributed by NM, 26-Nov-1995.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y z w $.
	faxrep5_0 $f wff ph $.
	faxrep5_1 $f set x $.
	faxrep5_2 $f set y $.
	faxrep5_3 $f set z $.
	faxrep5_4 $f set w $.
	eaxrep5_0 $e |- F/ z ph $.
	axrep5 $p |- ( A. x ( x e. w -> E. z A. y ( ph -> y = z ) ) -> E. z A. y ( y e. z <-> E. x ( x e. w /\ ph ) ) ) $= faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex wi faxrep5_1 wal faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 wex wb faxrep5_2 wal faxrep5_3 wex faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 wex wb faxrep5_2 wal faxrep5_3 wex faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex wi faxrep5_1 wal faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex faxrep5_1 wal faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 wex wb faxrep5_2 wal faxrep5_3 wex faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex wi faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex faxrep5_1 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex wi faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal wi faxrep5_3 wex faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 wex faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 19.37v faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal wi faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_3 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi wi faxrep5_2 wal faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 wal wi faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi wi faxrep5_2 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq impexp albii faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wceq wi faxrep5_2 19.21v bitr2i exbii bitr3i albii faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 faxrep5_2 faxrep5_3 faxrep5_4 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 faxrep5_3 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_3 nfv eaxrep5_0 nfan axrep4 sylbi faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 wex wb faxrep5_2 wal faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 wex wb faxrep5_2 wal faxrep5_3 faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 wex wb faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 wex wb faxrep5_2 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 wex faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 wex faxrep5_2 sup_set_class faxrep5_3 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa wa faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 wa faxrep5_1 faxrep5_1 sup_set_class faxrep5_4 sup_set_class wcel faxrep5_0 anabs5 exbii bibi2i albii exbii sylib $.
$}
$( An inference rule based on the Axiom of Replacement.  Typically, ` ph `
       defines a function from ` x ` to ` y ` .  (Contributed by NM,
       26-Nov-1995.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v v $.
	$d y z A v $.
	$d z ph v $.
	$d A v $.
	$d x y z v $.
	$d x v $.
	izfrepclf_0 $f set v $.
	fzfrepclf_0 $f wff ph $.
	fzfrepclf_1 $f set x $.
	fzfrepclf_2 $f set y $.
	fzfrepclf_3 $f set z $.
	fzfrepclf_4 $f class A $.
	ezfrepclf_0 $e |- F/_ x A $.
	ezfrepclf_1 $e |- A e. _V $.
	ezfrepclf_2 $e |- ( x e. A -> E. z A. y ( ph -> y = z ) ) $.
	zfrepclf $p |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) ) $= fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_3 wex izfrepclf_0 fzfrepclf_4 ezfrepclf_1 izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_3 wex fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_3 wex izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wceq wi fzfrepclf_2 wal fzfrepclf_3 wex wi fzfrepclf_1 wal fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_3 wex izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wceq wi fzfrepclf_2 wal fzfrepclf_3 wex wi fzfrepclf_1 fzfrepclf_1 izfrepclf_0 sup_set_class fzfrepclf_4 ezfrepclf_0 nfeq2 izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wceq wi fzfrepclf_2 wal fzfrepclf_3 wex izfrepclf_0 sup_set_class fzfrepclf_4 fzfrepclf_1 sup_set_class eleq2 ezfrepclf_2 syl6bi alrimi fzfrepclf_0 fzfrepclf_1 fzfrepclf_2 fzfrepclf_3 izfrepclf_0 fzfrepclf_0 fzfrepclf_3 nfv axrep5 syl izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 wal fzfrepclf_3 izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 wex wb fzfrepclf_2 izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 wex fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 wex fzfrepclf_2 sup_set_class fzfrepclf_3 sup_set_class wcel izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_0 wa fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 wa fzfrepclf_1 fzfrepclf_1 izfrepclf_0 sup_set_class fzfrepclf_4 ezfrepclf_0 nfeq2 izfrepclf_0 sup_set_class fzfrepclf_4 wceq fzfrepclf_1 sup_set_class izfrepclf_0 sup_set_class wcel fzfrepclf_1 sup_set_class fzfrepclf_4 wcel fzfrepclf_0 izfrepclf_0 sup_set_class fzfrepclf_4 fzfrepclf_1 sup_set_class eleq2 anbi1d exbid bibi2d albidv exbidv mpbid vtocle $.
$}
$( An inference rule based on the Axiom of Replacement.  Typically, ` ph `
       defines a function from ` x ` to ` y ` .  (Contributed by NM,
       26-Nov-1995.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$d x y z A $.
	$d z ph $.
	fzfrep3cl_0 $f wff ph $.
	fzfrep3cl_1 $f set x $.
	fzfrep3cl_2 $f set y $.
	fzfrep3cl_3 $f set z $.
	fzfrep3cl_4 $f class A $.
	ezfrep3cl_0 $e |- A e. _V $.
	ezfrep3cl_1 $e |- ( x e. A -> E. z A. y ( ph -> y = z ) ) $.
	zfrep3cl $p |- E. z A. y ( y e. z <-> E. x ( x e. A /\ ph ) ) $= fzfrep3cl_0 fzfrep3cl_1 fzfrep3cl_2 fzfrep3cl_3 fzfrep3cl_4 fzfrep3cl_1 fzfrep3cl_4 nfcv ezfrep3cl_0 ezfrep3cl_1 zfrepclf $.
$}
$( A version of Replacement using class abstractions.  (Contributed by NM,
       26-Nov-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$v z $.
	$d ph y z $.
	$d ps z $.
	$d x y z $.
	fzfrep4_0 $f wff ph $.
	fzfrep4_1 $f wff ps $.
	fzfrep4_2 $f set x $.
	fzfrep4_3 $f set y $.
	fzfrep4_4 $f set z $.
	ezfrep4_0 $e |- { x | ph } e. _V $.
	ezfrep4_1 $e |- ( ph -> E. z A. y ( ps -> y = z ) ) $.
	zfrep4 $p |- { y | E. x ( ph /\ ps ) } e. _V $= fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 cab fzfrep4_0 fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 cab cvv fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_0 fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_0 fzfrep4_1 wa fzfrep4_2 fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_0 fzfrep4_1 fzfrep4_0 fzfrep4_2 abid anbi1i exbii abbii fzfrep4_4 fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 cab fzfrep4_4 sup_set_class fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 cab wceq fzfrep4_4 wex fzfrep4_3 sup_set_class fzfrep4_4 sup_set_class wcel fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex wb fzfrep4_3 wal fzfrep4_4 wex fzfrep4_1 fzfrep4_2 fzfrep4_3 fzfrep4_4 fzfrep4_0 fzfrep4_2 cab fzfrep4_0 fzfrep4_2 nfab1 ezfrep4_0 fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_0 fzfrep4_1 fzfrep4_3 sup_set_class fzfrep4_4 sup_set_class wceq wi fzfrep4_3 wal fzfrep4_4 wex fzfrep4_0 fzfrep4_2 abid ezfrep4_1 sylbi zfrepclf fzfrep4_4 sup_set_class fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 cab wceq fzfrep4_3 sup_set_class fzfrep4_4 sup_set_class wcel fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex wb fzfrep4_3 wal fzfrep4_4 fzfrep4_2 sup_set_class fzfrep4_0 fzfrep4_2 cab wcel fzfrep4_1 wa fzfrep4_2 wex fzfrep4_3 fzfrep4_4 sup_set_class abeq2 exbii mpbir issetri eqeltrri $.
$}

