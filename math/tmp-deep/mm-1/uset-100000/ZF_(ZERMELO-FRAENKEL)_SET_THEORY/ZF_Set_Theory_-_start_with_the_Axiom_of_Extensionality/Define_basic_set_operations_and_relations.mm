$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets_into_classes.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Define basic set operations and relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new symbols. $)

$c \ $.

$(Backslash (difference) $)

$c u. $.

$(Cup (union) $)

$c i^i $.

$(Cap (intersection) $)

$c C_ $.

$(Subclass or subset symbol $)

$c C. $.

$(Proper subclass or subset symbol $)

$(Extend class notation to include class difference (read:  " ` A ` minus
     ` B ` "). $)

${
	$v A B  $.
	f0_cdif $f class A $.
	f1_cdif $f class B $.
	a_cdif $a class ( A \ B ) $.
$}

$(Extend class notation to include union of two classes (read:  " ` A `
     union ` B ` "). $)

${
	$v A B  $.
	f0_cun $f class A $.
	f1_cun $f class B $.
	a_cun $a class ( A u. B ) $.
$}

$(Extend class notation to include the intersection of two classes
     (read:  " ` A ` intersect ` B ` "). $)

${
	$v A B  $.
	f0_cin $f class A $.
	f1_cin $f class B $.
	a_cin $a class ( A i^i B ) $.
$}

$(Extend wff notation to include the subclass relation.  This is
     read " ` A ` is a subclass of ` B ` " or " ` B ` includes ` A ` ."  When
     ` A ` exists as a set, it is also read " ` A ` is a subset of ` B ` ." $)

${
	$v A B  $.
	f0_wss $f class A $.
	f1_wss $f class B $.
	a_wss $a wff A C_ B $.
$}

$(Extend wff notation with proper subclass relation. $)

${
	$v A B  $.
	f0_wpss $f class A $.
	f1_wpss $f class B $.
	a_wpss $a wff A C. B $.
$}

$(Soundness justification theorem for ~ df-dif .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v x y A B  $.
	$d x A  $.
	$d x B  $.
	$d y A  $.
	$d y B  $.
	$d z x  $.
	$d z y  $.
	$d z A  $.
	$d z B  $.
	f0_difjust $f set x $.
	f1_difjust $f set y $.
	f2_difjust $f class A $.
	f3_difjust $f class B $.
	i0_difjust $f set z $.
	p_difjust $p |- { x | ( x e. A /\ -. x e. B ) } = { y | ( y e. A /\ -. y e. B ) } $= f0_difjust a_sup_set_class i0_difjust a_sup_set_class f2_difjust p_eleq1 f0_difjust a_sup_set_class i0_difjust a_sup_set_class f3_difjust p_eleq1 f0_difjust a_sup_set_class i0_difjust a_sup_set_class a_wceq f0_difjust a_sup_set_class f3_difjust a_wcel i0_difjust a_sup_set_class f3_difjust a_wcel p_notbid f0_difjust a_sup_set_class i0_difjust a_sup_set_class a_wceq f0_difjust a_sup_set_class f2_difjust a_wcel i0_difjust a_sup_set_class f2_difjust a_wcel f0_difjust a_sup_set_class f3_difjust a_wcel a_wn i0_difjust a_sup_set_class f3_difjust a_wcel a_wn p_anbi12d f0_difjust a_sup_set_class f2_difjust a_wcel f0_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa i0_difjust a_sup_set_class f2_difjust a_wcel i0_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa f0_difjust i0_difjust p_cbvabv i0_difjust a_sup_set_class f1_difjust a_sup_set_class f2_difjust p_eleq1 i0_difjust a_sup_set_class f1_difjust a_sup_set_class f3_difjust p_eleq1 i0_difjust a_sup_set_class f1_difjust a_sup_set_class a_wceq i0_difjust a_sup_set_class f3_difjust a_wcel f1_difjust a_sup_set_class f3_difjust a_wcel p_notbid i0_difjust a_sup_set_class f1_difjust a_sup_set_class a_wceq i0_difjust a_sup_set_class f2_difjust a_wcel f1_difjust a_sup_set_class f2_difjust a_wcel i0_difjust a_sup_set_class f3_difjust a_wcel a_wn f1_difjust a_sup_set_class f3_difjust a_wcel a_wn p_anbi12d i0_difjust a_sup_set_class f2_difjust a_wcel i0_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa f1_difjust a_sup_set_class f2_difjust a_wcel f1_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa i0_difjust f1_difjust p_cbvabv f0_difjust a_sup_set_class f2_difjust a_wcel f0_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa f0_difjust a_cab i0_difjust a_sup_set_class f2_difjust a_wcel i0_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa i0_difjust a_cab f1_difjust a_sup_set_class f2_difjust a_wcel f1_difjust a_sup_set_class f3_difjust a_wcel a_wn a_wa f1_difjust a_cab p_eqtri $.
$}

$(Define class difference, also called relative complement.  Definition
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
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_df-dif $f set x $.
	f1_df-dif $f class A $.
	f2_df-dif $f class B $.
	a_df-dif $a |- ( A \ B ) = { x | ( x e. A /\ -. x e. B ) } $.
$}

$(Soundness justification theorem for ~ df-un .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v x y A B  $.
	$d x A  $.
	$d x B  $.
	$d y A  $.
	$d y B  $.
	$d z x  $.
	$d z y  $.
	$d z A  $.
	$d z B  $.
	f0_unjust $f set x $.
	f1_unjust $f set y $.
	f2_unjust $f class A $.
	f3_unjust $f class B $.
	i0_unjust $f set z $.
	p_unjust $p |- { x | ( x e. A \/ x e. B ) } = { y | ( y e. A \/ y e. B ) } $= f0_unjust a_sup_set_class i0_unjust a_sup_set_class f2_unjust p_eleq1 f0_unjust a_sup_set_class i0_unjust a_sup_set_class f3_unjust p_eleq1 f0_unjust a_sup_set_class i0_unjust a_sup_set_class a_wceq f0_unjust a_sup_set_class f2_unjust a_wcel i0_unjust a_sup_set_class f2_unjust a_wcel f0_unjust a_sup_set_class f3_unjust a_wcel i0_unjust a_sup_set_class f3_unjust a_wcel p_orbi12d f0_unjust a_sup_set_class f2_unjust a_wcel f0_unjust a_sup_set_class f3_unjust a_wcel a_wo i0_unjust a_sup_set_class f2_unjust a_wcel i0_unjust a_sup_set_class f3_unjust a_wcel a_wo f0_unjust i0_unjust p_cbvabv i0_unjust a_sup_set_class f1_unjust a_sup_set_class f2_unjust p_eleq1 i0_unjust a_sup_set_class f1_unjust a_sup_set_class f3_unjust p_eleq1 i0_unjust a_sup_set_class f1_unjust a_sup_set_class a_wceq i0_unjust a_sup_set_class f2_unjust a_wcel f1_unjust a_sup_set_class f2_unjust a_wcel i0_unjust a_sup_set_class f3_unjust a_wcel f1_unjust a_sup_set_class f3_unjust a_wcel p_orbi12d i0_unjust a_sup_set_class f2_unjust a_wcel i0_unjust a_sup_set_class f3_unjust a_wcel a_wo f1_unjust a_sup_set_class f2_unjust a_wcel f1_unjust a_sup_set_class f3_unjust a_wcel a_wo i0_unjust f1_unjust p_cbvabv f0_unjust a_sup_set_class f2_unjust a_wcel f0_unjust a_sup_set_class f3_unjust a_wcel a_wo f0_unjust a_cab i0_unjust a_sup_set_class f2_unjust a_wcel i0_unjust a_sup_set_class f3_unjust a_wcel a_wo i0_unjust a_cab f1_unjust a_sup_set_class f2_unjust a_wcel f1_unjust a_sup_set_class f3_unjust a_wcel a_wo f1_unjust a_cab p_eqtri $.
$}

$(Define the union of two classes.  Definition 5.6 of [TakeutiZaring]
       p. 16.  For example, ` ( { 1 , 3 } u. { 1 , 8 } ) = { 1 , 3 , 8 } `
       ( ~ ex-un ).  Contrast this operation with difference ` ( A \ B ) `
       ( ~ df-dif ) and intersection ` ( A i^i B ) ` ( ~ df-in ).  For an
       alternate definition in terms of class difference, requiring no dummy
       variables, see ~ dfun2 .  For union defined in terms of intersection,
       see ~ dfun3 .  (Contributed by NM, 23-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_df-un $f set x $.
	f1_df-un $f class A $.
	f2_df-un $f class B $.
	a_df-un $a |- ( A u. B ) = { x | ( x e. A \/ x e. B ) } $.
$}

$(Soundness justification theorem for ~ df-in .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)

${
	$v x y A B  $.
	$d x A  $.
	$d x B  $.
	$d y A  $.
	$d y B  $.
	$d z x  $.
	$d z y  $.
	$d z A  $.
	$d z B  $.
	f0_injust $f set x $.
	f1_injust $f set y $.
	f2_injust $f class A $.
	f3_injust $f class B $.
	i0_injust $f set z $.
	p_injust $p |- { x | ( x e. A /\ x e. B ) } = { y | ( y e. A /\ y e. B ) } $= f0_injust a_sup_set_class i0_injust a_sup_set_class f2_injust p_eleq1 f0_injust a_sup_set_class i0_injust a_sup_set_class f3_injust p_eleq1 f0_injust a_sup_set_class i0_injust a_sup_set_class a_wceq f0_injust a_sup_set_class f2_injust a_wcel i0_injust a_sup_set_class f2_injust a_wcel f0_injust a_sup_set_class f3_injust a_wcel i0_injust a_sup_set_class f3_injust a_wcel p_anbi12d f0_injust a_sup_set_class f2_injust a_wcel f0_injust a_sup_set_class f3_injust a_wcel a_wa i0_injust a_sup_set_class f2_injust a_wcel i0_injust a_sup_set_class f3_injust a_wcel a_wa f0_injust i0_injust p_cbvabv i0_injust a_sup_set_class f1_injust a_sup_set_class f2_injust p_eleq1 i0_injust a_sup_set_class f1_injust a_sup_set_class f3_injust p_eleq1 i0_injust a_sup_set_class f1_injust a_sup_set_class a_wceq i0_injust a_sup_set_class f2_injust a_wcel f1_injust a_sup_set_class f2_injust a_wcel i0_injust a_sup_set_class f3_injust a_wcel f1_injust a_sup_set_class f3_injust a_wcel p_anbi12d i0_injust a_sup_set_class f2_injust a_wcel i0_injust a_sup_set_class f3_injust a_wcel a_wa f1_injust a_sup_set_class f2_injust a_wcel f1_injust a_sup_set_class f3_injust a_wcel a_wa i0_injust f1_injust p_cbvabv f0_injust a_sup_set_class f2_injust a_wcel f0_injust a_sup_set_class f3_injust a_wcel a_wa f0_injust a_cab i0_injust a_sup_set_class f2_injust a_wcel i0_injust a_sup_set_class f3_injust a_wcel a_wa i0_injust a_cab f1_injust a_sup_set_class f2_injust a_wcel f1_injust a_sup_set_class f3_injust a_wcel a_wa f1_injust a_cab p_eqtri $.
$}

$(Define the intersection of two classes.  Definition 5.6 of
       [TakeutiZaring] p. 16.  For example,
       ` ( { 1 , 3 } i^i { 1 , 8 } ) = { 1 } ` ( ~ ex-in ).  Contrast this
       operation with union ` ( A u. B ) ` ( ~ df-un ) and difference
       ` ( A \ B ) ` ( ~ df-dif ).  For alternate definitions in terms of class
       difference, requiring no dummy variables, see ~ dfin2 and ~ dfin4 .  For
       intersection defined in terms of union, see ~ dfin3 .  (Contributed by
       NM, 29-Apr-1994.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_df-in $f set x $.
	f1_df-in $f class A $.
	f2_df-in $f class B $.
	a_df-in $a |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) } $.
$}

$(Alternate definition for the intersection of two classes.  (Contributed
       by NM, 6-Jul-2005.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfin5 $f set x $.
	f1_dfin5 $f class A $.
	f2_dfin5 $f class B $.
	p_dfin5 $p |- ( A i^i B ) = { x e. A | x e. B } $= f0_dfin5 f1_dfin5 f2_dfin5 a_df-in f0_dfin5 a_sup_set_class f2_dfin5 a_wcel f0_dfin5 f1_dfin5 a_df-rab f1_dfin5 f2_dfin5 a_cin f0_dfin5 a_sup_set_class f1_dfin5 a_wcel f0_dfin5 a_sup_set_class f2_dfin5 a_wcel a_wa f0_dfin5 a_cab f0_dfin5 a_sup_set_class f2_dfin5 a_wcel f0_dfin5 f1_dfin5 a_crab p_eqtr4i $.
$}

$(Alternate definition of class difference.  (Contributed by NM,
       25-Mar-2004.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfdif2 $f set x $.
	f1_dfdif2 $f class A $.
	f2_dfdif2 $f class B $.
	p_dfdif2 $p |- ( A \ B ) = { x e. A | -. x e. B } $= f0_dfdif2 f1_dfdif2 f2_dfdif2 a_df-dif f0_dfdif2 a_sup_set_class f2_dfdif2 a_wcel a_wn f0_dfdif2 f1_dfdif2 a_df-rab f1_dfdif2 f2_dfdif2 a_cdif f0_dfdif2 a_sup_set_class f1_dfdif2 a_wcel f0_dfdif2 a_sup_set_class f2_dfdif2 a_wcel a_wn a_wa f0_dfdif2 a_cab f0_dfdif2 a_sup_set_class f2_dfdif2 a_wcel a_wn f0_dfdif2 f1_dfdif2 a_crab p_eqtr4i $.
$}

$(Expansion of membership in a class difference.  (Contributed by NM,
       29-Apr-1994.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_eldif $f class A $.
	f1_eldif $f class B $.
	f2_eldif $f class C $.
	i0_eldif $f set x $.
	p_eldif $p |- ( A e. ( B \ C ) <-> ( A e. B /\ -. A e. C ) ) $= f0_eldif f1_eldif f2_eldif a_cdif p_elex f0_eldif f1_eldif p_elex f0_eldif f1_eldif a_wcel f0_eldif a_cvv a_wcel f0_eldif f2_eldif a_wcel a_wn p_adantr i0_eldif a_sup_set_class f0_eldif f1_eldif p_eleq1 i0_eldif a_sup_set_class f0_eldif f2_eldif p_eleq1 i0_eldif a_sup_set_class f0_eldif a_wceq i0_eldif a_sup_set_class f2_eldif a_wcel f0_eldif f2_eldif a_wcel p_notbid i0_eldif a_sup_set_class f0_eldif a_wceq i0_eldif a_sup_set_class f1_eldif a_wcel f0_eldif f1_eldif a_wcel i0_eldif a_sup_set_class f2_eldif a_wcel a_wn f0_eldif f2_eldif a_wcel a_wn p_anbi12d i0_eldif f1_eldif f2_eldif a_df-dif i0_eldif a_sup_set_class f1_eldif a_wcel i0_eldif a_sup_set_class f2_eldif a_wcel a_wn a_wa f0_eldif f1_eldif a_wcel f0_eldif f2_eldif a_wcel a_wn a_wa i0_eldif f0_eldif f1_eldif f2_eldif a_cdif a_cvv p_elab2g f0_eldif f1_eldif f2_eldif a_cdif a_wcel f0_eldif a_cvv a_wcel f0_eldif f1_eldif a_wcel f0_eldif f2_eldif a_wcel a_wn a_wa p_pm5.21nii $.
$}

$(If a class is in one class and not another, it is also in their
       difference.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_eldifd $f wff ph $.
	f1_eldifd $f class A $.
	f2_eldifd $f class B $.
	f3_eldifd $f class C $.
	e0_eldifd $e |- ( ph -> A e. B ) $.
	e1_eldifd $e |- ( ph -> -. A e. C ) $.
	p_eldifd $p |- ( ph -> A e. ( B \ C ) ) $= e0_eldifd e1_eldifd f1_eldifd f2_eldifd f3_eldifd p_eldif f0_eldifd f1_eldifd f2_eldifd a_wcel f1_eldifd f3_eldifd a_wcel a_wn f1_eldifd f2_eldifd f3_eldifd a_cdif a_wcel p_sylanbrc $.
$}

$(If a class is in the difference of two classes, it is also in the
       minuend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_eldifad $f wff ph $.
	f1_eldifad $f class A $.
	f2_eldifad $f class B $.
	f3_eldifad $f class C $.
	e0_eldifad $e |- ( ph -> A e. ( B \ C ) ) $.
	p_eldifad $p |- ( ph -> A e. B ) $= e0_eldifad f1_eldifad f2_eldifad f3_eldifad p_eldif f0_eldifad f1_eldifad f2_eldifad f3_eldifad a_cdif a_wcel f1_eldifad f2_eldifad a_wcel f1_eldifad f3_eldifad a_wcel a_wn a_wa p_sylib f0_eldifad f1_eldifad f2_eldifad a_wcel f1_eldifad f3_eldifad a_wcel a_wn p_simpld $.
$}

$(If a class is in the difference of two classes, it is not in the
       subtrahend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_eldifbd $f wff ph $.
	f1_eldifbd $f class A $.
	f2_eldifbd $f class B $.
	f3_eldifbd $f class C $.
	e0_eldifbd $e |- ( ph -> A e. ( B \ C ) ) $.
	p_eldifbd $p |- ( ph -> -. A e. C ) $= e0_eldifbd f1_eldifbd f2_eldifbd f3_eldifbd p_eldif f0_eldifbd f1_eldifbd f2_eldifbd f3_eldifbd a_cdif a_wcel f1_eldifbd f2_eldifbd a_wcel f1_eldifbd f3_eldifbd a_wcel a_wn a_wa p_sylib f0_eldifbd f1_eldifbd f2_eldifbd a_wcel f1_eldifbd f3_eldifbd a_wcel a_wn p_simprd $.
$}


