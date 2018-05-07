$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Transfinite_induction.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The natural numbers (i.e. finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new symbol. $)
$c om  $.
$( Greek letter omega $)
$( Extend class notation to include the class of natural numbers. $)
${
	com $a class om $.
$}
$( Define the class of natural numbers, which are all ordinal numbers that
       are less than every limit ordinal, i.e. all finite ordinals.  Our
       definition is a variant of the Definition of N of [BellMachover]
       p. 471.  See ~ dfom2 for an alternate definition.  Later, when we assume
       the Axiom of Infinity, we show ` om ` is a set in ~ omex , and ` om `
       can then be defined per ~ dfom3 (the smallest inductive set) and
       ~ dfom4 .

       _Note_: the natural numbers ` om ` are a subset of the ordinal numbers
       ~ df-on .  They are completely different from the natural numbers ` NN `
       ( ~ df-nn ) that are a subset of the complex numbers defined much later
       in our development, although the two sets have analogous properties and
       operations defined on them.  (Contributed by NM, 15-May-1994.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fdf-om_0 $f set x $.
	fdf-om_1 $f set y $.
	df-om $a |- om = { x e. On | A. y ( Lim y -> x e. y ) } $.
$}
$( An alternate definition of the set of natural numbers ` om ` .
       Definition 7.28 of [TakeutiZaring] p. 42, who use the symbol K_I for the
       inner class builder of non-limit ordinal numbers (see ~ nlimon ).
       (Contributed by NM, 1-Nov-2004.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x z $.
	$d y z $.
	idfom2_0 $f set z $.
	fdfom2_0 $f set x $.
	fdfom2_1 $f set y $.
	dfom2 $p |- om = { x e. On | suc x C_ { y e. On | -. Lim y } } $= com idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 wal fdfom2_0 con0 crab fdfom2_0 sup_set_class csuc fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wss fdfom2_0 con0 crab fdfom2_0 idfom2_0 df-om idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 wal fdfom2_0 sup_set_class csuc fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wss fdfom2_0 con0 fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 wal idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi idfom2_0 wal fdfom2_0 sup_set_class csuc fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wss fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi idfom2_0 fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi wi idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi wi idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wi wi idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wi fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel wa idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn wb idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class con0 wcel wa idfom2_0 sup_set_class fdfom2_0 sup_set_class wss idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class fdfom2_0 sup_set_class onsssuc idfom2_0 sup_set_class fdfom2_0 sup_set_class ontri1 bitr3d ancoms idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wb fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel wa fdfom2_1 sup_set_class wlim wn idfom2_0 sup_set_class wlim wn fdfom2_1 idfom2_0 sup_set_class con0 fdfom2_1 sup_set_class idfom2_0 sup_set_class wceq fdfom2_1 sup_set_class wlim idfom2_0 sup_set_class wlim fdfom2_1 sup_set_class idfom2_0 sup_set_class limeq notbid elrab a1i imbi12d pm5.74da idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wa fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi wi idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wi wi idfom2_0 sup_set_class wlim idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wa fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel idfom2_0 sup_set_class wlim idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class cvv wcel idfom2_0 sup_set_class wlim idfom2_0 sup_set_class con0 wcel idfom2_0 vex idfom2_0 sup_set_class cvv limelon mpan pm4.71ri imbi1i idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel impexp idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wi idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wi fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class wlim wn wi idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa wi idfom2_0 sup_set_class wlim fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel con34b idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn wa fdfom2_0 sup_set_class idfom2_0 sup_set_class wcel wn idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class wlim wn ibar imbi2d syl5bb pm5.74i 3bitri syl6rbbr idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi wi idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel wa idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel wi idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel impexp fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel wa idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab wcel fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel wa idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel simpr fdfom2_0 sup_set_class con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class csuc con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class con0 wcel wi fdfom2_0 sup_set_class suceloni fdfom2_0 sup_set_class csuc con0 wcel idfom2_0 sup_set_class fdfom2_0 sup_set_class csuc wcel idfom2_0 sup_set_class con0 wcel fdfom2_0 sup_set_class csuc idfom2_0 sup_set_class onelon ex syl ancrd impbid2 imbi1d syl5bbr bitrd albidv idfom2_0 fdfom2_0 sup_set_class csuc fdfom2_1 sup_set_class wlim wn fdfom2_1 con0 crab dfss2 syl6bbr rabbiia eqtri $.
$}
$( Membership in omega.  The left conjunct can be eliminated if we assume
       the Axiom of Infinity; see ~ elom3 .  (Contributed by NM,
       15-May-1994.) $)
${
	$v x $.
	$v A $.
	$v y $.
	$d A x y $.
	ielom_0 $f set y $.
	felom_0 $f set x $.
	felom_1 $f class A $.
	elom $p |- ( A e. om <-> ( A e. On /\ A. x ( Lim x -> A e. x ) ) ) $= felom_0 sup_set_class wlim ielom_0 sup_set_class felom_0 sup_set_class wcel wi felom_0 wal felom_0 sup_set_class wlim felom_1 felom_0 sup_set_class wcel wi felom_0 wal ielom_0 felom_1 con0 com ielom_0 sup_set_class felom_1 wceq felom_0 sup_set_class wlim ielom_0 sup_set_class felom_0 sup_set_class wcel wi felom_0 sup_set_class wlim felom_1 felom_0 sup_set_class wcel wi felom_0 ielom_0 sup_set_class felom_1 wceq ielom_0 sup_set_class felom_0 sup_set_class wcel felom_1 felom_0 sup_set_class wcel felom_0 sup_set_class wlim ielom_0 sup_set_class felom_1 felom_0 sup_set_class eleq1 imbi2d albidv ielom_0 felom_0 df-om elrab2 $.
$}
$( Omega is a subset of ` On ` .  (Contributed by NM, 13-Jun-1994.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	iomsson_0 $f set x $.
	iomsson_1 $f set y $.
	omsson $p |- om C_ On $= com iomsson_0 sup_set_class csuc iomsson_1 sup_set_class wlim wn iomsson_1 con0 crab wss iomsson_0 con0 crab con0 iomsson_0 iomsson_1 dfom2 iomsson_0 sup_set_class csuc iomsson_1 sup_set_class wlim wn iomsson_1 con0 crab wss iomsson_0 con0 ssrab2 eqsstri $.
$}
$( The class of natural numbers is a subclass of any (infinite) limit
       ordinal.  Exercise 1 of [TakeutiZaring] p. 44.  Remarkably, our proof
       does not require the Axiom of Infinity.  (Contributed by NM,
       30-Oct-2003.) $)
${
	$v A $.
	$v x $.
	$v y $.
	$d x y A $.
	ilimomss_0 $f set x $.
	ilimomss_1 $f set y $.
	flimomss_0 $f class A $.
	limomss $p |- ( Lim A -> om C_ A ) $= flimomss_0 word flimomss_0 wlim com flimomss_0 wss flimomss_0 limord flimomss_0 word flimomss_0 con0 wcel flimomss_0 con0 wceq wo flimomss_0 wlim com flimomss_0 wss wi flimomss_0 ordeleqon flimomss_0 con0 wcel flimomss_0 wlim com flimomss_0 wss wi flimomss_0 con0 wceq flimomss_0 con0 wcel flimomss_0 wlim com flimomss_0 wss flimomss_0 con0 wcel flimomss_0 wlim wa ilimomss_0 com flimomss_0 flimomss_0 con0 wcel flimomss_0 wlim ilimomss_0 sup_set_class com wcel ilimomss_0 sup_set_class flimomss_0 wcel wi flimomss_0 con0 wcel ilimomss_0 sup_set_class com wcel flimomss_0 wlim ilimomss_0 sup_set_class flimomss_0 wcel ilimomss_0 sup_set_class com wcel ilimomss_1 sup_set_class wlim ilimomss_0 sup_set_class ilimomss_1 sup_set_class wcel wi ilimomss_1 wal flimomss_0 con0 wcel flimomss_0 wlim ilimomss_0 sup_set_class flimomss_0 wcel wi ilimomss_0 sup_set_class com wcel ilimomss_0 sup_set_class con0 wcel ilimomss_1 sup_set_class wlim ilimomss_0 sup_set_class ilimomss_1 sup_set_class wcel wi ilimomss_1 wal ilimomss_1 ilimomss_0 sup_set_class elom simprbi ilimomss_1 sup_set_class wlim ilimomss_0 sup_set_class ilimomss_1 sup_set_class wcel wi flimomss_0 wlim ilimomss_0 sup_set_class flimomss_0 wcel wi ilimomss_1 flimomss_0 con0 ilimomss_1 sup_set_class flimomss_0 wceq ilimomss_1 sup_set_class wlim flimomss_0 wlim ilimomss_0 sup_set_class ilimomss_1 sup_set_class wcel ilimomss_0 sup_set_class flimomss_0 wcel ilimomss_1 sup_set_class flimomss_0 limeq ilimomss_1 sup_set_class flimomss_0 ilimomss_0 sup_set_class eleq2 imbi12d spcgv syl5 com23 imp ssrdv ex flimomss_0 con0 wceq com flimomss_0 wss flimomss_0 wlim flimomss_0 con0 wceq com flimomss_0 wss com con0 wss omsson flimomss_0 con0 com sseq2 mpbiri a1d jaoi sylbi mpcom $.
$}
$( A natural number is an ordinal number.  (Contributed by NM,
     27-Jun-1994.) $)
${
	$v A $.
	fnnon_0 $f class A $.
	nnon $p |- ( A e. om -> A e. On ) $= com con0 fnnon_0 omsson sseli $.
$}
$( A natural number is an ordinal number.  (Contributed by NM,
       27-Jun-1994.) $)
${
	$v A $.
	fnnoni_0 $f class A $.
	ennoni_0 $e |- A e. om $.
	nnoni $p |- A e. On $= fnnoni_0 com wcel fnnoni_0 con0 wcel ennoni_0 fnnoni_0 nnon ax-mp $.
$}
$( A natural number is ordinal.  (Contributed by NM, 17-Oct-1995.) $)
${
	$v A $.
	fnnord_0 $f class A $.
	nnord $p |- ( A e. om -> Ord A ) $= fnnord_0 com wcel fnnord_0 con0 wcel fnnord_0 word fnnord_0 nnon fnnord_0 eloni syl $.
$}
$( Omega is ordinal.  Theorem 7.32 of [TakeutiZaring] p. 43.  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	iordom_0 $f set x $.
	iordom_1 $f set y $.
	iordom_2 $f set z $.
	ordom $p |- Ord om $= com wtr com con0 wss con0 word com word com wtr iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class com wcel wa iordom_1 sup_set_class com wcel wi iordom_0 wal iordom_1 iordom_1 iordom_0 com dftr2 iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class com wcel wa iordom_1 sup_set_class com wcel wi iordom_0 iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class com wcel iordom_1 sup_set_class com wcel iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class con0 wcel iordom_2 sup_set_class wlim iordom_0 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 wal wa iordom_1 sup_set_class con0 wcel iordom_2 sup_set_class wlim iordom_1 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 wal wa iordom_0 sup_set_class com wcel iordom_1 sup_set_class com wcel iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class con0 wcel iordom_1 sup_set_class con0 wcel iordom_2 sup_set_class wlim iordom_0 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 wal iordom_2 sup_set_class wlim iordom_1 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 wal iordom_0 sup_set_class con0 wcel iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_1 sup_set_class con0 wcel iordom_0 sup_set_class iordom_1 sup_set_class onelon expcom iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_2 sup_set_class wlim iordom_0 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 sup_set_class wlim iordom_1 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_2 sup_set_class wlim iordom_0 sup_set_class iordom_2 sup_set_class wcel iordom_1 sup_set_class iordom_2 sup_set_class wcel iordom_2 sup_set_class wlim iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class iordom_2 sup_set_class wcel iordom_1 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 sup_set_class wlim iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class iordom_2 sup_set_class wcel iordom_1 sup_set_class iordom_2 sup_set_class wcel iordom_2 sup_set_class wlim iordom_2 sup_set_class word iordom_2 sup_set_class wtr iordom_1 sup_set_class iordom_0 sup_set_class wcel iordom_0 sup_set_class iordom_2 sup_set_class wcel wa iordom_1 sup_set_class iordom_2 sup_set_class wcel wi iordom_2 sup_set_class limord iordom_2 sup_set_class ordtr iordom_2 sup_set_class iordom_1 sup_set_class iordom_0 sup_set_class trel 3syl exp3a com12 a2d alimdv anim12d iordom_2 iordom_0 sup_set_class elom iordom_2 iordom_1 sup_set_class elom 3imtr4g imp ax-gen mpgbir omsson ordon com con0 trssord mp3an $.
$}
$( A member of a natural number is a natural number.  (Contributed by NM,
     21-Jun-1998.) $)
${
	$v A $.
	$v B $.
	felnn_0 $f class A $.
	felnn_1 $f class B $.
	elnn $p |- ( ( A e. B /\ B e. om ) -> A e. om ) $= com word com wtr felnn_0 felnn_1 wcel felnn_1 com wcel wa felnn_0 com wcel wi ordom com ordtr com felnn_0 felnn_1 trel mp2b $.
$}
$( The class of natural numbers ` om ` is either an ordinal number (if we
     accept the Axiom of Infinity) or the proper class of all ordinal numbers
     (if we deny the Axiom of Infinity).  Remark in [TakeutiZaring] p. 43.
     (Contributed by NM, 10-May-1998.) $)
${
	omon $p |- ( om e. On \/ om = On ) $= com word com con0 wcel com con0 wceq wo ordom com ordeleqon mpbi $.
$}
$( Omega is an ordinal number.  (Contributed by Mario Carneiro,
       30-Jan-2013.) $)
${
	omelon2 $p |- ( om e. _V -> om e. On ) $= com con0 wcel com cvv wcel com con0 wcel wn com con0 wceq com cvv wcel wn com con0 wcel com con0 wceq omon ori com con0 wceq com cvv wcel con0 cvv wcel onprc com con0 cvv eleq1 mtbiri syl con4i $.
$}
$( A natural number is not a limit ordinal.  (Contributed by NM,
       18-Oct-1995.) $)
${
	$v A $.
	$v x $.
	$d x A $.
	innlim_0 $f set x $.
	fnnlim_0 $f class A $.
	nnlim $p |- ( A e. om -> -. Lim A ) $= fnnlim_0 com wcel fnnlim_0 wlim fnnlim_0 fnnlim_0 wcel fnnlim_0 com wcel fnnlim_0 word fnnlim_0 fnnlim_0 wcel wn fnnlim_0 nnord fnnlim_0 ordirr syl fnnlim_0 com wcel innlim_0 sup_set_class wlim fnnlim_0 innlim_0 sup_set_class wcel wi innlim_0 wal fnnlim_0 wlim fnnlim_0 fnnlim_0 wcel wi fnnlim_0 com wcel fnnlim_0 con0 wcel innlim_0 sup_set_class wlim fnnlim_0 innlim_0 sup_set_class wcel wi innlim_0 wal innlim_0 fnnlim_0 elom simprbi innlim_0 sup_set_class wlim fnnlim_0 innlim_0 sup_set_class wcel wi fnnlim_0 wlim fnnlim_0 fnnlim_0 wcel wi innlim_0 fnnlim_0 com innlim_0 sup_set_class fnnlim_0 wceq innlim_0 sup_set_class wlim fnnlim_0 wlim fnnlim_0 innlim_0 sup_set_class wcel fnnlim_0 fnnlim_0 wcel innlim_0 sup_set_class fnnlim_0 limeq innlim_0 sup_set_class fnnlim_0 fnnlim_0 eleq2 imbi12d spcgv mpd mtod $.
$}
$( The class of natural numbers is a subclass of the class of non-limit
       ordinal numbers.  Exercise 4 of [TakeutiZaring] p. 42.  (Contributed by
       NM, 2-Nov-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$v x $.
	fomssnlim_0 $f set x $.
	omssnlim $p |- om C_ { x e. On | -. Lim x } $= com fomssnlim_0 sup_set_class wlim wn fomssnlim_0 con0 crab wss com con0 wss fomssnlim_0 sup_set_class wlim wn fomssnlim_0 com wral omsson fomssnlim_0 sup_set_class wlim wn fomssnlim_0 com fomssnlim_0 sup_set_class nnlim rgen fomssnlim_0 sup_set_class wlim wn fomssnlim_0 con0 com ssrab mpbir2an $.
$}
$( Omega is a limit ordinal.  Theorem 2.8 of [BellMachover] p. 473.  Our
     proof, however, does not require the Axiom of Infinity.  (Contributed by
     NM, 26-Mar-1995.)  (Proof shortened by Mario Carneiro, 2-Sep-2015.) $)
${
	$v x $.
	ilimom_0 $f set x $.
	limom $p |- Lim om $= com word com wlim ordom com word com con0 wcel com con0 wceq wo com wlim com ordeleqon com con0 wcel com wlim com con0 wceq com con0 wcel ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel wi ilimom_0 wal com wlim com con0 wcel com com wcel ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel wi ilimom_0 wal com word com com wcel wn ordom com ordirr ax-mp com com wcel com con0 wcel ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel wi ilimom_0 wal ilimom_0 com elom baib mtbii com wlim wn ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel wi ilimom_0 ilimom_0 sup_set_class wlim com wlim wn com ilimom_0 sup_set_class wcel ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel com wlim ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel wn com ilimom_0 sup_set_class wceq com wlim ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wcel com ilimom_0 sup_set_class wceq ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class wss com ilimom_0 sup_set_class wcel com ilimom_0 sup_set_class wceq wo ilimom_0 sup_set_class limomss ilimom_0 sup_set_class wlim com word ilimom_0 sup_set_class word com ilimom_0 sup_set_class wss com ilimom_0 sup_set_class wcel com ilimom_0 sup_set_class wceq wo wb ordom ilimom_0 sup_set_class limord com ilimom_0 sup_set_class ordsseleq sylancr mpbid ord com ilimom_0 sup_set_class wceq com wlim ilimom_0 sup_set_class wlim com ilimom_0 sup_set_class limeq biimprcd syld con1d com12 alrimiv nsyl2 com con0 wceq com wlim con0 wlim limon com con0 limeq mpbiri jaoi sylbi ax-mp $.
$}
$( A class belongs to omega iff its successor does.  (Contributed by NM,
     3-Dec-1995.) $)
${
	$v A $.
	fpeano2b_0 $f class A $.
	peano2b $p |- ( A e. om <-> suc A e. om ) $= com wlim fpeano2b_0 com wcel fpeano2b_0 csuc com wcel wb limom com fpeano2b_0 limsuc ax-mp $.
$}
$( A nonzero natural number is a successor.  (Contributed by NM,
       18-Feb-2004.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	fnnsuc_0 $f set x $.
	fnnsuc_1 $f class A $.
	nnsuc $p |- ( ( A e. om /\ A =/= (/) ) -> E. x e. om A = suc x ) $= fnnsuc_1 com wcel fnnsuc_1 c0 wne wa fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 com wrex fnnsuc_1 com wcel fnnsuc_1 c0 wne wa fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex fnnsuc_1 wlim fnnsuc_1 com wcel fnnsuc_1 wlim wn fnnsuc_1 c0 wne fnnsuc_1 nnlim adantr fnnsuc_1 com wcel fnnsuc_1 word fnnsuc_1 c0 wne fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex wn fnnsuc_1 wlim wi fnnsuc_1 nnord fnnsuc_1 word fnnsuc_1 c0 wne wa fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex wn fnnsuc_1 fnnsuc_1 cuni wceq fnnsuc_1 wlim fnnsuc_1 word fnnsuc_1 fnnsuc_1 cuni wceq fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex wn wb fnnsuc_1 c0 wne fnnsuc_0 fnnsuc_1 orduninsuc adantr fnnsuc_1 word fnnsuc_1 c0 wne fnnsuc_1 fnnsuc_1 cuni wceq fnnsuc_1 wlim fnnsuc_1 wlim fnnsuc_1 word fnnsuc_1 c0 wne fnnsuc_1 fnnsuc_1 cuni wceq w3a fnnsuc_1 df-lim biimpri 3expia sylbird sylan mt3d fnnsuc_1 com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 wrex fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 com wrex wi fnnsuc_1 c0 wne fnnsuc_1 com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 con0 com fnnsuc_1 com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 sup_set_class com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq wa fnnsuc_0 sup_set_class con0 wcel fnnsuc_1 com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 sup_set_class com wcel fnnsuc_1 com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_0 sup_set_class csuc com wcel fnnsuc_0 sup_set_class com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc wceq fnnsuc_1 com wcel fnnsuc_0 sup_set_class csuc com wcel fnnsuc_1 fnnsuc_0 sup_set_class csuc com eleq1 biimpcd fnnsuc_0 sup_set_class peano2b syl6ibr ancrd adantld reximdv2 adantr mpd $.
$}
$( An ordinal subclass of non-limit ordinals is a class of natural
       numbers.  Exercise 7 of [TakeutiZaring] p. 42.  (Contributed by NM,
       2-Nov-2004.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	fssnlim_0 $f set x $.
	fssnlim_1 $f class A $.
	ssnlim $p |- ( ( Ord A /\ A C_ { x e. On | -. Lim x } ) -> A C_ om ) $= fssnlim_1 word fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wss wa fssnlim_1 com wss com fssnlim_1 wcel wn fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wss com fssnlim_1 wcel wn fssnlim_1 word fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wss com fssnlim_1 wcel com wlim limom fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wss com fssnlim_1 wcel com fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wcel com wlim wn fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab com ssel com fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wcel com con0 wcel com wlim wn fssnlim_0 sup_set_class wlim wn com wlim wn fssnlim_0 com con0 fssnlim_0 sup_set_class com wceq fssnlim_0 sup_set_class wlim com wlim fssnlim_0 sup_set_class com limeq notbid elrab simprbi syl6 mt2i adantl fssnlim_1 word fssnlim_1 com wss com fssnlim_1 wcel wn wb fssnlim_1 fssnlim_0 sup_set_class wlim wn fssnlim_0 con0 crab wss fssnlim_1 word com word fssnlim_1 com wss com fssnlim_1 wcel wn wb ordom fssnlim_1 com ordtri1 mpan2 adantr mpbird $.
$}

