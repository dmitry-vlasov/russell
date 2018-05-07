$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets_into_classes.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Define basic set operations and relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new symbols. $)
$c \  $.
$( Backslash (difference) $)
$c u.  $.
$( Cup (union) $)
$c i^i  $.
$( Cap (intersection) $)
$c C_  $.
$( Subclass or subset symbol $)
$c C.  $.
$( Proper subclass or subset symbol $)
$( Extend class notation to include class difference (read:  " ` A ` minus
     ` B ` "). $)
${
	$v A $.
	$v B $.
	fcdif_0 $f class A $.
	fcdif_1 $f class B $.
	cdif $a class ( A \ B ) $.
$}
$( Extend class notation to include union of two classes (read:  " ` A `
     union ` B ` "). $)
${
	$v A $.
	$v B $.
	fcun_0 $f class A $.
	fcun_1 $f class B $.
	cun $a class ( A u. B ) $.
$}
$( Extend class notation to include the intersection of two classes
     (read:  " ` A ` intersect ` B ` "). $)
${
	$v A $.
	$v B $.
	fcin_0 $f class A $.
	fcin_1 $f class B $.
	cin $a class ( A i^i B ) $.
$}
$( Extend wff notation to include the subclass relation.  This is
     read " ` A ` is a subclass of ` B ` " or " ` B ` includes ` A ` ."  When
     ` A ` exists as a set, it is also read " ` A ` is a subset of ` B ` ." $)
${
	$v A $.
	$v B $.
	fwss_0 $f class A $.
	fwss_1 $f class B $.
	wss $a wff A C_ B $.
$}
$( Extend wff notation with proper subclass relation. $)
${
	$v A $.
	$v B $.
	fwpss_0 $f class A $.
	fwpss_1 $f class B $.
	wpss $a wff A C. B $.
$}
$( Soundness justification theorem for ~ df-dif .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d y A $.
	$d y B $.
	$d z x $.
	$d z y $.
	$d z A $.
	$d z B $.
	idifjust_0 $f set z $.
	fdifjust_0 $f set x $.
	fdifjust_1 $f set y $.
	fdifjust_2 $f class A $.
	fdifjust_3 $f class B $.
	difjust $p |- { x | ( x e. A /\ -. x e. B ) } = { y | ( y e. A /\ -. y e. B ) } $= fdifjust_0 cv fdifjust_2 wcel fdifjust_0 cv fdifjust_3 wcel wn wa fdifjust_0 cab idifjust_0 cv fdifjust_2 wcel idifjust_0 cv fdifjust_3 wcel wn wa idifjust_0 cab fdifjust_1 cv fdifjust_2 wcel fdifjust_1 cv fdifjust_3 wcel wn wa fdifjust_1 cab fdifjust_0 cv fdifjust_2 wcel fdifjust_0 cv fdifjust_3 wcel wn wa idifjust_0 cv fdifjust_2 wcel idifjust_0 cv fdifjust_3 wcel wn wa fdifjust_0 idifjust_0 fdifjust_0 cv idifjust_0 cv wceq fdifjust_0 cv fdifjust_2 wcel idifjust_0 cv fdifjust_2 wcel fdifjust_0 cv fdifjust_3 wcel wn idifjust_0 cv fdifjust_3 wcel wn fdifjust_0 cv idifjust_0 cv fdifjust_2 eleq1 fdifjust_0 cv idifjust_0 cv wceq fdifjust_0 cv fdifjust_3 wcel idifjust_0 cv fdifjust_3 wcel fdifjust_0 cv idifjust_0 cv fdifjust_3 eleq1 notbid anbi12d cbvabv idifjust_0 cv fdifjust_2 wcel idifjust_0 cv fdifjust_3 wcel wn wa fdifjust_1 cv fdifjust_2 wcel fdifjust_1 cv fdifjust_3 wcel wn wa idifjust_0 fdifjust_1 idifjust_0 cv fdifjust_1 cv wceq idifjust_0 cv fdifjust_2 wcel fdifjust_1 cv fdifjust_2 wcel idifjust_0 cv fdifjust_3 wcel wn fdifjust_1 cv fdifjust_3 wcel wn idifjust_0 cv fdifjust_1 cv fdifjust_2 eleq1 idifjust_0 cv fdifjust_1 cv wceq idifjust_0 cv fdifjust_3 wcel fdifjust_1 cv fdifjust_3 wcel idifjust_0 cv fdifjust_1 cv fdifjust_3 eleq1 notbid anbi12d cbvabv eqtri $.
$}
$( Define class difference, also called relative complement.  Definition
       5.12 of [TakeutiZaring] p. 20.  For example,
       ` ( { 1 , 3 } \ { 1 , 8 } ) = { 3 } ` ( ~ ex-dif ).  Contrast this
       operation with union ` ( A u. B ) ` ( ~ df-un ) and intersection
       ` ( A i^i B ) ` ( ~ df-in ).  Several notations are used in the
       literature; we chose the ` \ ` convention used in Definition 5.3 of
       [Eisenberg] p. 67 instead of the more common minus sign to reserve the
       latter for later use in, e.g., arithmetic.  We will use the
       terminology " ` A ` excludes ` B ` " to mean ` A \ B ` .  We will
       use " ` B ` is removed from ` A ` " to mean ` A \ { B } ` i.e. the
       removal of an element or equivalently the exclusion of a singleton.
       (Contributed by NM, 29-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdf-dif_0 $f set x $.
	fdf-dif_1 $f class A $.
	fdf-dif_2 $f class B $.
	df-dif $a |- ( A \ B ) = { x | ( x e. A /\ -. x e. B ) } $.
$}
$( Soundness justification theorem for ~ df-un .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d y A $.
	$d y B $.
	$d z x $.
	$d z y $.
	$d z A $.
	$d z B $.
	iunjust_0 $f set z $.
	funjust_0 $f set x $.
	funjust_1 $f set y $.
	funjust_2 $f class A $.
	funjust_3 $f class B $.
	unjust $p |- { x | ( x e. A \/ x e. B ) } = { y | ( y e. A \/ y e. B ) } $= funjust_0 cv funjust_2 wcel funjust_0 cv funjust_3 wcel wo funjust_0 cab iunjust_0 cv funjust_2 wcel iunjust_0 cv funjust_3 wcel wo iunjust_0 cab funjust_1 cv funjust_2 wcel funjust_1 cv funjust_3 wcel wo funjust_1 cab funjust_0 cv funjust_2 wcel funjust_0 cv funjust_3 wcel wo iunjust_0 cv funjust_2 wcel iunjust_0 cv funjust_3 wcel wo funjust_0 iunjust_0 funjust_0 cv iunjust_0 cv wceq funjust_0 cv funjust_2 wcel iunjust_0 cv funjust_2 wcel funjust_0 cv funjust_3 wcel iunjust_0 cv funjust_3 wcel funjust_0 cv iunjust_0 cv funjust_2 eleq1 funjust_0 cv iunjust_0 cv funjust_3 eleq1 orbi12d cbvabv iunjust_0 cv funjust_2 wcel iunjust_0 cv funjust_3 wcel wo funjust_1 cv funjust_2 wcel funjust_1 cv funjust_3 wcel wo iunjust_0 funjust_1 iunjust_0 cv funjust_1 cv wceq iunjust_0 cv funjust_2 wcel funjust_1 cv funjust_2 wcel iunjust_0 cv funjust_3 wcel funjust_1 cv funjust_3 wcel iunjust_0 cv funjust_1 cv funjust_2 eleq1 iunjust_0 cv funjust_1 cv funjust_3 eleq1 orbi12d cbvabv eqtri $.
$}
$( Define the union of two classes.  Definition 5.6 of [TakeutiZaring]
       p. 16.  For example, ` ( { 1 , 3 } u. { 1 , 8 } ) = { 1 , 3 , 8 } `
       ( ~ ex-un ).  Contrast this operation with difference ` ( A \ B ) `
       ( ~ df-dif ) and intersection ` ( A i^i B ) ` ( ~ df-in ).  For an
       alternate definition in terms of class difference, requiring no dummy
       variables, see ~ dfun2 .  For union defined in terms of intersection,
       see ~ dfun3 .  (Contributed by NM, 23-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdf-un_0 $f set x $.
	fdf-un_1 $f class A $.
	fdf-un_2 $f class B $.
	df-un $a |- ( A u. B ) = { x | ( x e. A \/ x e. B ) } $.
$}
$( Soundness justification theorem for ~ df-in .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d y A $.
	$d y B $.
	$d z x $.
	$d z y $.
	$d z A $.
	$d z B $.
	iinjust_0 $f set z $.
	finjust_0 $f set x $.
	finjust_1 $f set y $.
	finjust_2 $f class A $.
	finjust_3 $f class B $.
	injust $p |- { x | ( x e. A /\ x e. B ) } = { y | ( y e. A /\ y e. B ) } $= finjust_0 cv finjust_2 wcel finjust_0 cv finjust_3 wcel wa finjust_0 cab iinjust_0 cv finjust_2 wcel iinjust_0 cv finjust_3 wcel wa iinjust_0 cab finjust_1 cv finjust_2 wcel finjust_1 cv finjust_3 wcel wa finjust_1 cab finjust_0 cv finjust_2 wcel finjust_0 cv finjust_3 wcel wa iinjust_0 cv finjust_2 wcel iinjust_0 cv finjust_3 wcel wa finjust_0 iinjust_0 finjust_0 cv iinjust_0 cv wceq finjust_0 cv finjust_2 wcel iinjust_0 cv finjust_2 wcel finjust_0 cv finjust_3 wcel iinjust_0 cv finjust_3 wcel finjust_0 cv iinjust_0 cv finjust_2 eleq1 finjust_0 cv iinjust_0 cv finjust_3 eleq1 anbi12d cbvabv iinjust_0 cv finjust_2 wcel iinjust_0 cv finjust_3 wcel wa finjust_1 cv finjust_2 wcel finjust_1 cv finjust_3 wcel wa iinjust_0 finjust_1 iinjust_0 cv finjust_1 cv wceq iinjust_0 cv finjust_2 wcel finjust_1 cv finjust_2 wcel iinjust_0 cv finjust_3 wcel finjust_1 cv finjust_3 wcel iinjust_0 cv finjust_1 cv finjust_2 eleq1 iinjust_0 cv finjust_1 cv finjust_3 eleq1 anbi12d cbvabv eqtri $.
$}
$( Define the intersection of two classes.  Definition 5.6 of
       [TakeutiZaring] p. 16.  For example,
       ` ( { 1 , 3 } i^i { 1 , 8 } ) = { 1 } ` ( ~ ex-in ).  Contrast this
       operation with union ` ( A u. B ) ` ( ~ df-un ) and difference
       ` ( A \ B ) ` ( ~ df-dif ).  For alternate definitions in terms of class
       difference, requiring no dummy variables, see ~ dfin2 and ~ dfin4 .  For
       intersection defined in terms of union, see ~ dfin3 .  (Contributed by
       NM, 29-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdf-in_0 $f set x $.
	fdf-in_1 $f class A $.
	fdf-in_2 $f class B $.
	df-in $a |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) } $.
$}
$( Alternate definition for the intersection of two classes.  (Contributed
       by NM, 6-Jul-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdfin5_0 $f set x $.
	fdfin5_1 $f class A $.
	fdfin5_2 $f class B $.
	dfin5 $p |- ( A i^i B ) = { x e. A | x e. B } $= fdfin5_1 fdfin5_2 cin fdfin5_0 cv fdfin5_1 wcel fdfin5_0 cv fdfin5_2 wcel wa fdfin5_0 cab fdfin5_0 cv fdfin5_2 wcel fdfin5_0 fdfin5_1 crab fdfin5_0 fdfin5_1 fdfin5_2 df-in fdfin5_0 cv fdfin5_2 wcel fdfin5_0 fdfin5_1 df-rab eqtr4i $.
$}
$( Alternate definition of class difference.  (Contributed by NM,
       25-Mar-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdfdif2_0 $f set x $.
	fdfdif2_1 $f class A $.
	fdfdif2_2 $f class B $.
	dfdif2 $p |- ( A \ B ) = { x e. A | -. x e. B } $= fdfdif2_1 fdfdif2_2 cdif fdfdif2_0 cv fdfdif2_1 wcel fdfdif2_0 cv fdfdif2_2 wcel wn wa fdfdif2_0 cab fdfdif2_0 cv fdfdif2_2 wcel wn fdfdif2_0 fdfdif2_1 crab fdfdif2_0 fdfdif2_1 fdfdif2_2 df-dif fdfdif2_0 cv fdfdif2_2 wcel wn fdfdif2_0 fdfdif2_1 df-rab eqtr4i $.
$}
$( Expansion of membership in a class difference.  (Contributed by NM,
       29-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	ieldif_0 $f set x $.
	feldif_0 $f class A $.
	feldif_1 $f class B $.
	feldif_2 $f class C $.
	eldif $p |- ( A e. ( B \ C ) <-> ( A e. B /\ -. A e. C ) ) $= feldif_0 feldif_1 feldif_2 cdif wcel feldif_0 cvv wcel feldif_0 feldif_1 wcel feldif_0 feldif_2 wcel wn wa feldif_0 feldif_1 feldif_2 cdif elex feldif_0 feldif_1 wcel feldif_0 cvv wcel feldif_0 feldif_2 wcel wn feldif_0 feldif_1 elex adantr ieldif_0 cv feldif_1 wcel ieldif_0 cv feldif_2 wcel wn wa feldif_0 feldif_1 wcel feldif_0 feldif_2 wcel wn wa ieldif_0 feldif_0 feldif_1 feldif_2 cdif cvv ieldif_0 cv feldif_0 wceq ieldif_0 cv feldif_1 wcel feldif_0 feldif_1 wcel ieldif_0 cv feldif_2 wcel wn feldif_0 feldif_2 wcel wn ieldif_0 cv feldif_0 feldif_1 eleq1 ieldif_0 cv feldif_0 wceq ieldif_0 cv feldif_2 wcel feldif_0 feldif_2 wcel ieldif_0 cv feldif_0 feldif_2 eleq1 notbid anbi12d ieldif_0 feldif_1 feldif_2 df-dif elab2g pm5.21nii $.
$}
$( If a class is in one class and not another, it is also in their
       difference.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feldifd_0 $f wff ph $.
	feldifd_1 $f class A $.
	feldifd_2 $f class B $.
	feldifd_3 $f class C $.
	eeldifd_0 $e |- ( ph -> A e. B ) $.
	eeldifd_1 $e |- ( ph -> -. A e. C ) $.
	eldifd $p |- ( ph -> A e. ( B \ C ) ) $= feldifd_0 feldifd_1 feldifd_2 wcel feldifd_1 feldifd_3 wcel wn feldifd_1 feldifd_2 feldifd_3 cdif wcel eeldifd_0 eeldifd_1 feldifd_1 feldifd_2 feldifd_3 eldif sylanbrc $.
$}
$( If a class is in the difference of two classes, it is also in the
       minuend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feldifad_0 $f wff ph $.
	feldifad_1 $f class A $.
	feldifad_2 $f class B $.
	feldifad_3 $f class C $.
	eeldifad_0 $e |- ( ph -> A e. ( B \ C ) ) $.
	eldifad $p |- ( ph -> A e. B ) $= feldifad_0 feldifad_1 feldifad_2 wcel feldifad_1 feldifad_3 wcel wn feldifad_0 feldifad_1 feldifad_2 feldifad_3 cdif wcel feldifad_1 feldifad_2 wcel feldifad_1 feldifad_3 wcel wn wa eeldifad_0 feldifad_1 feldifad_2 feldifad_3 eldif sylib simpld $.
$}
$( If a class is in the difference of two classes, it is not in the
       subtrahend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feldifbd_0 $f wff ph $.
	feldifbd_1 $f class A $.
	feldifbd_2 $f class B $.
	feldifbd_3 $f class C $.
	eeldifbd_0 $e |- ( ph -> A e. ( B \ C ) ) $.
	eldifbd $p |- ( ph -> -. A e. C ) $= feldifbd_0 feldifbd_1 feldifbd_2 wcel feldifbd_1 feldifbd_3 wcel wn feldifbd_0 feldifbd_1 feldifbd_2 feldifbd_3 cdif wcel feldifbd_1 feldifbd_2 wcel feldifbd_1 feldifbd_3 wcel wn wa eeldifbd_0 feldifbd_1 feldifbd_2 feldifbd_3 eldif sylib simprd $.
$}

