$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_abstractions_(a_k_a__class_builders).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Class form not-free predicate

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c F/_  $.
$( Underlined not-free symbol. $)
$( Extend wff definition to include the not-free predicate for classes. $)
${
	fwnfc_0 $f set x $.
	fwnfc_1 $f class A $.
	wnfc $a wff F/_ x A $.
$}
$( Justification theorem for ~ df-nfc .  (Contributed by Mario Carneiro,
       13-Oct-2016.) $)
${
	$d x y z $.
	$d y z A $.
	fnfcjust_0 $f set x $.
	fnfcjust_1 $f set y $.
	fnfcjust_2 $f set z $.
	fnfcjust_3 $f class A $.
	nfcjust $p |- ( A. y F/ x y e. A <-> A. z F/ x z e. A ) $= fnfcjust_1 sup_set_class fnfcjust_3 wcel fnfcjust_0 wnf fnfcjust_2 sup_set_class fnfcjust_3 wcel fnfcjust_0 wnf fnfcjust_1 fnfcjust_2 fnfcjust_1 sup_set_class fnfcjust_2 sup_set_class wceq fnfcjust_1 sup_set_class fnfcjust_3 wcel fnfcjust_2 sup_set_class fnfcjust_3 wcel fnfcjust_0 fnfcjust_1 sup_set_class fnfcjust_2 sup_set_class wceq fnfcjust_0 nfv fnfcjust_1 sup_set_class fnfcjust_2 sup_set_class fnfcjust_3 eleq1 nfbidf cbvalv $.
$}
$( Define the not-free predicate for classes.  This is read " ` x ` is not
       free in ` A ` ".  Not-free means that the value of ` x ` cannot affect
       the value of ` A ` , e.g., any occurrence of ` x ` in ` A ` is
       effectively bound by a "for all" or something that expands to one (such
       as "there exists").  It is defined in terms of the not-free predicate
       ~ df-nf for wffs; see that definition for more information.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fdf-nfc_0 $f set x $.
	fdf-nfc_1 $f set y $.
	fdf-nfc_2 $f class A $.
	df-nfc $a |- ( F/_ x A <-> A. y F/ x y e. A ) $.
$}
$( Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fnfci_0 $f set x $.
	fnfci_1 $f set y $.
	fnfci_2 $f class A $.
	enfci_0 $e |- F/ x y e. A $.
	nfci $p |- F/_ x A $= fnfci_0 fnfci_2 wnfc fnfci_1 sup_set_class fnfci_2 wcel fnfci_0 wnf fnfci_1 fnfci_0 fnfci_1 fnfci_2 df-nfc enfci_0 mpgbir $.
$}
$( Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fnfcii_0 $f set x $.
	fnfcii_1 $f set y $.
	fnfcii_2 $f class A $.
	enfcii_0 $e |- ( y e. A -> A. x y e. A ) $.
	nfcii $p |- F/_ x A $= fnfcii_0 fnfcii_1 fnfcii_2 fnfcii_1 sup_set_class fnfcii_2 wcel fnfcii_0 enfcii_0 nfi nfci $.
$}
$( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fnfcr_0 $f set x $.
	fnfcr_1 $f set y $.
	fnfcr_2 $f class A $.
	nfcr $p |- ( F/_ x A -> F/ x y e. A ) $= fnfcr_0 fnfcr_2 wnfc fnfcr_1 sup_set_class fnfcr_2 wcel fnfcr_0 wnf fnfcr_1 wal fnfcr_1 sup_set_class fnfcr_2 wcel fnfcr_0 wnf fnfcr_0 fnfcr_1 fnfcr_2 df-nfc fnfcr_1 sup_set_class fnfcr_2 wcel fnfcr_0 wnf fnfcr_1 sp sylbi $.
$}
$( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x y z $.
	$d z A $.
	infcrii_0 $f set z $.
	fnfcrii_0 $f set x $.
	fnfcrii_1 $f set y $.
	fnfcrii_2 $f class A $.
	enfcrii_0 $e |- F/_ x A $.
	nfcrii $p |- ( y e. A -> A. x y e. A ) $= fnfcrii_0 infcrii_0 fnfcrii_1 fnfcrii_2 infcrii_0 sup_set_class fnfcrii_2 wcel fnfcrii_0 fnfcrii_0 fnfcrii_2 wnfc infcrii_0 sup_set_class fnfcrii_2 wcel fnfcrii_0 wnf enfcrii_0 fnfcrii_0 infcrii_0 fnfcrii_2 nfcr ax-mp nfri hblem $.
$}
$( Consequence of the not-free predicate.  (Note that unlike ~ nfcr , this
       does not require ` y ` and ` A ` to be disjoint.)  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	fnfcri_0 $f set x $.
	fnfcri_1 $f set y $.
	fnfcri_2 $f class A $.
	enfcri_0 $e |- F/_ x A $.
	nfcri $p |- F/ x y e. A $= fnfcri_1 sup_set_class fnfcri_2 wcel fnfcri_0 fnfcri_0 fnfcri_1 fnfcri_2 enfcri_0 nfcrii nfi $.
$}
$( Deduce that a class ` A ` does not have ` x ` free in it.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fnfcd_0 $f wff ph $.
	fnfcd_1 $f set x $.
	fnfcd_2 $f set y $.
	fnfcd_3 $f class A $.
	enfcd_0 $e |- F/ y ph $.
	enfcd_1 $e |- ( ph -> F/ x y e. A ) $.
	nfcd $p |- ( ph -> F/_ x A ) $= fnfcd_0 fnfcd_2 sup_set_class fnfcd_3 wcel fnfcd_1 wnf fnfcd_2 wal fnfcd_1 fnfcd_3 wnfc fnfcd_0 fnfcd_2 sup_set_class fnfcd_3 wcel fnfcd_1 wnf fnfcd_2 enfcd_0 enfcd_1 alrimi fnfcd_1 fnfcd_2 fnfcd_3 df-nfc sylibr $.
$}
$( Equality theorem for class not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	infceqi_0 $f set y $.
	fnfceqi_0 $f set x $.
	fnfceqi_1 $f class A $.
	fnfceqi_2 $f class B $.
	enfceqi_0 $e |- A = B $.
	nfceqi $p |- ( F/_ x A <-> F/_ x B ) $= infceqi_0 sup_set_class fnfceqi_1 wcel fnfceqi_0 wnf infceqi_0 wal infceqi_0 sup_set_class fnfceqi_2 wcel fnfceqi_0 wnf infceqi_0 wal fnfceqi_0 fnfceqi_1 wnfc fnfceqi_0 fnfceqi_2 wnfc infceqi_0 sup_set_class fnfceqi_1 wcel fnfceqi_0 wnf infceqi_0 sup_set_class fnfceqi_2 wcel fnfceqi_0 wnf infceqi_0 infceqi_0 sup_set_class fnfceqi_1 wcel infceqi_0 sup_set_class fnfceqi_2 wcel fnfceqi_0 fnfceqi_1 fnfceqi_2 infceqi_0 sup_set_class enfceqi_0 eleq2i nfbii albii fnfceqi_0 infceqi_0 fnfceqi_1 df-nfc fnfceqi_0 infceqi_0 fnfceqi_2 df-nfc 3bitr4i $.
$}
$( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfcxfr_0 $f set x $.
	fnfcxfr_1 $f class A $.
	fnfcxfr_2 $f class B $.
	enfcxfr_0 $e |- A = B $.
	enfcxfr_1 $e |- F/_ x B $.
	nfcxfr $p |- F/_ x A $= fnfcxfr_0 fnfcxfr_1 wnfc fnfcxfr_0 fnfcxfr_2 wnfc enfcxfr_1 fnfcxfr_0 fnfcxfr_1 fnfcxfr_2 enfcxfr_0 nfceqi mpbir $.
$}
$( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	fnfcxfrd_0 $f wff ph $.
	fnfcxfrd_1 $f set x $.
	fnfcxfrd_2 $f class A $.
	fnfcxfrd_3 $f class B $.
	enfcxfrd_0 $e |- A = B $.
	enfcxfrd_1 $e |- ( ph -> F/_ x B ) $.
	nfcxfrd $p |- ( ph -> F/_ x A ) $= fnfcxfrd_0 fnfcxfrd_1 fnfcxfrd_3 wnfc fnfcxfrd_1 fnfcxfrd_2 wnfc enfcxfrd_1 fnfcxfrd_1 fnfcxfrd_2 fnfcxfrd_3 enfcxfrd_0 nfceqi sylibr $.
$}
$( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	$d A y $.
	$d B y $.
	$d ph y $.
	infceqdf_0 $f set y $.
	fnfceqdf_0 $f wff ph $.
	fnfceqdf_1 $f set x $.
	fnfceqdf_2 $f class A $.
	fnfceqdf_3 $f class B $.
	enfceqdf_0 $e |- F/ x ph $.
	enfceqdf_1 $e |- ( ph -> A = B ) $.
	nfceqdf $p |- ( ph -> ( F/_ x A <-> F/_ x B ) ) $= fnfceqdf_0 infceqdf_0 sup_set_class fnfceqdf_2 wcel fnfceqdf_1 wnf infceqdf_0 wal infceqdf_0 sup_set_class fnfceqdf_3 wcel fnfceqdf_1 wnf infceqdf_0 wal fnfceqdf_1 fnfceqdf_2 wnfc fnfceqdf_1 fnfceqdf_3 wnfc fnfceqdf_0 infceqdf_0 sup_set_class fnfceqdf_2 wcel fnfceqdf_1 wnf infceqdf_0 sup_set_class fnfceqdf_3 wcel fnfceqdf_1 wnf infceqdf_0 fnfceqdf_0 infceqdf_0 sup_set_class fnfceqdf_2 wcel infceqdf_0 sup_set_class fnfceqdf_3 wcel fnfceqdf_1 enfceqdf_0 fnfceqdf_0 fnfceqdf_2 fnfceqdf_3 infceqdf_0 sup_set_class enfceqdf_1 eleq2d nfbidf albidv fnfceqdf_1 infceqdf_0 fnfceqdf_2 df-nfc fnfceqdf_1 infceqdf_0 fnfceqdf_3 df-nfc 3bitr4g $.
$}
$( If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y A $.
	infcv_0 $f set y $.
	fnfcv_0 $f set x $.
	fnfcv_1 $f class A $.
	nfcv $p |- F/_ x A $= fnfcv_0 infcv_0 fnfcv_1 infcv_0 sup_set_class fnfcv_1 wcel fnfcv_0 nfv nfci $.
$}
$( If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
${
	$d x A $.
	fnfcvd_0 $f wff ph $.
	fnfcvd_1 $f set x $.
	fnfcvd_2 $f class A $.
	nfcvd $p |- ( ph -> F/_ x A ) $= fnfcvd_1 fnfcvd_2 wnfc fnfcvd_0 fnfcvd_1 fnfcvd_2 nfcv a1i $.
$}
$( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x y $.
	$d y ph $.
	infab1_0 $f set y $.
	fnfab1_0 $f wff ph $.
	fnfab1_1 $f set x $.
	nfab1 $p |- F/_ x { x | ph } $= fnfab1_1 infab1_0 fnfab1_0 fnfab1_1 cab fnfab1_0 fnfab1_1 infab1_0 nfsab1 nfci $.
$}
$( ` x ` is bound in ` F/_ x A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	infnfc1_0 $f set y $.
	fnfnfc1_0 $f set x $.
	fnfnfc1_1 $f class A $.
	nfnfc1 $p |- F/ x F/_ x A $= fnfnfc1_0 fnfnfc1_1 wnfc infnfc1_0 sup_set_class fnfnfc1_1 wcel fnfnfc1_0 wnf infnfc1_0 wal fnfnfc1_0 fnfnfc1_0 infnfc1_0 fnfnfc1_1 df-nfc infnfc1_0 sup_set_class fnfnfc1_1 wcel fnfnfc1_0 wnf fnfnfc1_0 infnfc1_0 infnfc1_0 sup_set_class fnfnfc1_1 wcel fnfnfc1_0 nfnf1 nfal nfxfr $.
$}
$( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	infab_0 $f set z $.
	fnfab_0 $f wff ph $.
	fnfab_1 $f set x $.
	fnfab_2 $f set y $.
	enfab_0 $e |- F/ x ph $.
	nfab $p |- F/_ x { y | ph } $= fnfab_1 infab_0 fnfab_0 fnfab_2 cab fnfab_0 fnfab_1 fnfab_2 infab_0 enfab_0 nfsab nfci $.
$}
$( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 14-Oct-2016.) $)
${
	fnfaba1_0 $f wff ph $.
	fnfaba1_1 $f set x $.
	fnfaba1_2 $f set y $.
	nfaba1 $p |- F/_ x { y | A. x ph } $= fnfaba1_0 fnfaba1_1 wal fnfaba1_1 fnfaba1_2 fnfaba1_0 fnfaba1_1 nfa1 nfab $.
$}
$( Hypothesis builder for ` F/_ y A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z A $.
	infnfc_0 $f set z $.
	fnfnfc_0 $f set x $.
	fnfnfc_1 $f set y $.
	fnfnfc_2 $f class A $.
	enfnfc_0 $e |- F/_ x A $.
	nfnfc $p |- F/ x F/_ y A $= fnfnfc_1 fnfnfc_2 wnfc infnfc_0 sup_set_class fnfnfc_2 wcel fnfnfc_1 wnf infnfc_0 wal fnfnfc_0 fnfnfc_1 infnfc_0 fnfnfc_2 df-nfc infnfc_0 sup_set_class fnfnfc_2 wcel fnfnfc_1 wnf fnfnfc_0 infnfc_0 infnfc_0 sup_set_class fnfnfc_2 wcel fnfnfc_0 fnfnfc_1 fnfnfc_0 infnfc_0 fnfnfc_2 enfnfc_0 nfcri nfnf nfal nfxfr $.
$}
$( Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x z $.
	$d z A $.
	$d z B $.
	infeq_0 $f set z $.
	fnfeq_0 $f set x $.
	fnfeq_1 $f class A $.
	fnfeq_2 $f class B $.
	enfeq_0 $e |- F/_ x A $.
	enfeq_1 $e |- F/_ x B $.
	nfeq $p |- F/ x A = B $= fnfeq_1 fnfeq_2 wceq infeq_0 sup_set_class fnfeq_1 wcel infeq_0 sup_set_class fnfeq_2 wcel wb infeq_0 wal fnfeq_0 infeq_0 fnfeq_1 fnfeq_2 dfcleq infeq_0 sup_set_class fnfeq_1 wcel infeq_0 sup_set_class fnfeq_2 wcel wb fnfeq_0 infeq_0 infeq_0 sup_set_class fnfeq_1 wcel infeq_0 sup_set_class fnfeq_2 wcel fnfeq_0 fnfeq_0 infeq_0 fnfeq_1 enfeq_0 nfcri fnfeq_0 infeq_0 fnfeq_2 enfeq_1 nfcri nfbi nfal nfxfr $.
$}
$( Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x z $.
	$d z A $.
	$d z B $.
	infel_0 $f set z $.
	fnfel_0 $f set x $.
	fnfel_1 $f class A $.
	fnfel_2 $f class B $.
	enfel_0 $e |- F/_ x A $.
	enfel_1 $e |- F/_ x B $.
	nfel $p |- F/ x A e. B $= fnfel_1 fnfel_2 wcel infel_0 sup_set_class fnfel_1 wceq infel_0 sup_set_class fnfel_2 wcel wa infel_0 wex fnfel_0 infel_0 fnfel_1 fnfel_2 df-clel infel_0 sup_set_class fnfel_1 wceq infel_0 sup_set_class fnfel_2 wcel wa fnfel_0 infel_0 infel_0 sup_set_class fnfel_1 wceq infel_0 sup_set_class fnfel_2 wcel fnfel_0 fnfel_0 infel_0 sup_set_class fnfel_1 fnfel_0 infel_0 sup_set_class nfcv enfel_0 nfeq fnfel_0 infel_0 fnfel_2 enfel_1 nfcri nfan nfex nfxfr $.
$}
$( Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
${
	$d x B $.
	fnfeq1_0 $f set x $.
	fnfeq1_1 $f class A $.
	fnfeq1_2 $f class B $.
	enfeq1_0 $e |- F/_ x A $.
	nfeq1 $p |- F/ x A = B $= fnfeq1_0 fnfeq1_1 fnfeq1_2 enfeq1_0 fnfeq1_0 fnfeq1_2 nfcv nfeq $.
$}
$( Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
${
	$d x B $.
	fnfel1_0 $f set x $.
	fnfel1_1 $f class A $.
	fnfel1_2 $f class B $.
	enfel1_0 $e |- F/_ x A $.
	nfel1 $p |- F/ x A e. B $= fnfel1_0 fnfel1_1 fnfel1_2 enfel1_0 fnfel1_0 fnfel1_2 nfcv nfel $.
$}
$( Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
${
	$d x A $.
	fnfeq2_0 $f set x $.
	fnfeq2_1 $f class A $.
	fnfeq2_2 $f class B $.
	enfeq2_0 $e |- F/_ x B $.
	nfeq2 $p |- F/ x A = B $= fnfeq2_0 fnfeq2_1 fnfeq2_2 fnfeq2_0 fnfeq2_1 nfcv enfeq2_0 nfeq $.
$}
$( Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
${
	$d x A $.
	fnfel2_0 $f set x $.
	fnfel2_1 $f class A $.
	fnfel2_2 $f class B $.
	enfel2_0 $e |- F/_ x B $.
	nfel2 $p |- F/ x A e. B $= fnfel2_0 fnfel2_1 fnfel2_2 fnfel2_0 fnfel2_1 nfcv enfel2_0 nfel $.
$}
$( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
${
	$d x y $.
	$d y A $.
	fnfcrd_0 $f wff ph $.
	fnfcrd_1 $f set x $.
	fnfcrd_2 $f set y $.
	fnfcrd_3 $f class A $.
	enfcrd_0 $e |- ( ph -> F/_ x A ) $.
	nfcrd $p |- ( ph -> F/ x y e. A ) $= fnfcrd_0 fnfcrd_1 fnfcrd_3 wnfc fnfcrd_2 sup_set_class fnfcrd_3 wcel fnfcrd_1 wnf enfcrd_0 fnfcrd_1 fnfcrd_2 fnfcrd_3 nfcr syl $.
$}
$( Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	$d y ph $.
	infeqd_0 $f set y $.
	fnfeqd_0 $f wff ph $.
	fnfeqd_1 $f set x $.
	fnfeqd_2 $f class A $.
	fnfeqd_3 $f class B $.
	enfeqd_0 $e |- ( ph -> F/_ x A ) $.
	enfeqd_1 $e |- ( ph -> F/_ x B ) $.
	nfeqd $p |- ( ph -> F/ x A = B ) $= fnfeqd_2 fnfeqd_3 wceq infeqd_0 sup_set_class fnfeqd_2 wcel infeqd_0 sup_set_class fnfeqd_3 wcel wb infeqd_0 wal fnfeqd_0 fnfeqd_1 infeqd_0 fnfeqd_2 fnfeqd_3 dfcleq fnfeqd_0 infeqd_0 sup_set_class fnfeqd_2 wcel infeqd_0 sup_set_class fnfeqd_3 wcel wb fnfeqd_1 infeqd_0 fnfeqd_0 infeqd_0 nfv fnfeqd_0 infeqd_0 sup_set_class fnfeqd_2 wcel infeqd_0 sup_set_class fnfeqd_3 wcel fnfeqd_1 fnfeqd_0 fnfeqd_1 infeqd_0 fnfeqd_2 enfeqd_0 nfcrd fnfeqd_0 fnfeqd_1 infeqd_0 fnfeqd_3 enfeqd_1 nfcrd nfbid nfald nfxfrd $.
$}
$( Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
${
	$d x y $.
	$d y A $.
	$d y B $.
	$d y ph $.
	infeld_0 $f set y $.
	fnfeld_0 $f wff ph $.
	fnfeld_1 $f set x $.
	fnfeld_2 $f class A $.
	fnfeld_3 $f class B $.
	enfeld_0 $e |- ( ph -> F/_ x A ) $.
	enfeld_1 $e |- ( ph -> F/_ x B ) $.
	nfeld $p |- ( ph -> F/ x A e. B ) $= fnfeld_2 fnfeld_3 wcel infeld_0 sup_set_class fnfeld_2 wceq infeld_0 sup_set_class fnfeld_3 wcel wa infeld_0 wex fnfeld_0 fnfeld_1 infeld_0 fnfeld_2 fnfeld_3 df-clel fnfeld_0 infeld_0 sup_set_class fnfeld_2 wceq infeld_0 sup_set_class fnfeld_3 wcel wa fnfeld_1 infeld_0 fnfeld_0 infeld_0 nfv fnfeld_0 infeld_0 sup_set_class fnfeld_2 wceq infeld_0 sup_set_class fnfeld_3 wcel fnfeld_1 fnfeld_0 fnfeld_1 infeld_0 sup_set_class fnfeld_2 fnfeld_0 fnfeld_1 infeld_0 sup_set_class nfcvd enfeld_0 nfeqd fnfeld_0 fnfeld_1 infeld_0 fnfeld_3 enfeld_1 nfcrd nfand nfexd nfxfrd $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
${
	$d w x $.
	$d w y $.
	$d w A $.
	$d w B $.
	idrnfc1_0 $f set w $.
	fdrnfc1_0 $f set x $.
	fdrnfc1_1 $f set y $.
	fdrnfc1_2 $f class A $.
	fdrnfc1_3 $f class B $.
	edrnfc1_0 $e |- ( A. x x = y -> A = B ) $.
	drnfc1 $p |- ( A. x x = y -> ( F/_ x A <-> F/_ y B ) ) $= fdrnfc1_0 sup_set_class fdrnfc1_1 sup_set_class wceq fdrnfc1_0 wal idrnfc1_0 sup_set_class fdrnfc1_2 wcel fdrnfc1_0 wnf idrnfc1_0 wal idrnfc1_0 sup_set_class fdrnfc1_3 wcel fdrnfc1_1 wnf idrnfc1_0 wal fdrnfc1_0 fdrnfc1_2 wnfc fdrnfc1_1 fdrnfc1_3 wnfc idrnfc1_0 sup_set_class fdrnfc1_2 wcel fdrnfc1_0 wnf idrnfc1_0 sup_set_class fdrnfc1_3 wcel fdrnfc1_1 wnf fdrnfc1_0 fdrnfc1_1 idrnfc1_0 idrnfc1_0 sup_set_class fdrnfc1_2 wcel idrnfc1_0 sup_set_class fdrnfc1_3 wcel fdrnfc1_0 fdrnfc1_1 fdrnfc1_0 sup_set_class fdrnfc1_1 sup_set_class wceq fdrnfc1_0 wal fdrnfc1_2 fdrnfc1_3 idrnfc1_0 sup_set_class edrnfc1_0 eleq2d drnf1 dral2 fdrnfc1_0 idrnfc1_0 fdrnfc1_2 df-nfc fdrnfc1_1 idrnfc1_0 fdrnfc1_3 df-nfc 3bitr4g $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
${
	$d w x $.
	$d w y $.
	$d w z $.
	$d w A $.
	$d w B $.
	idrnfc2_0 $f set w $.
	fdrnfc2_0 $f set x $.
	fdrnfc2_1 $f set y $.
	fdrnfc2_2 $f set z $.
	fdrnfc2_3 $f class A $.
	fdrnfc2_4 $f class B $.
	edrnfc2_0 $e |- ( A. x x = y -> A = B ) $.
	drnfc2 $p |- ( A. x x = y -> ( F/_ z A <-> F/_ z B ) ) $= fdrnfc2_0 sup_set_class fdrnfc2_1 sup_set_class wceq fdrnfc2_0 wal idrnfc2_0 sup_set_class fdrnfc2_3 wcel fdrnfc2_2 wnf idrnfc2_0 wal idrnfc2_0 sup_set_class fdrnfc2_4 wcel fdrnfc2_2 wnf idrnfc2_0 wal fdrnfc2_2 fdrnfc2_3 wnfc fdrnfc2_2 fdrnfc2_4 wnfc idrnfc2_0 sup_set_class fdrnfc2_3 wcel fdrnfc2_2 wnf idrnfc2_0 sup_set_class fdrnfc2_4 wcel fdrnfc2_2 wnf fdrnfc2_0 fdrnfc2_1 idrnfc2_0 idrnfc2_0 sup_set_class fdrnfc2_3 wcel idrnfc2_0 sup_set_class fdrnfc2_4 wcel fdrnfc2_0 fdrnfc2_1 fdrnfc2_2 fdrnfc2_0 sup_set_class fdrnfc2_1 sup_set_class wceq fdrnfc2_0 wal fdrnfc2_3 fdrnfc2_4 idrnfc2_0 sup_set_class edrnfc2_0 eleq2d drnf2 dral2 fdrnfc2_2 idrnfc2_0 fdrnfc2_3 df-nfc fdrnfc2_2 idrnfc2_0 fdrnfc2_4 df-nfc 3bitr4g $.
$}
$( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	$d z ps $.
	infabd2_0 $f set z $.
	fnfabd2_0 $f wff ph $.
	fnfabd2_1 $f wff ps $.
	fnfabd2_2 $f set x $.
	fnfabd2_3 $f set y $.
	enfabd2_0 $e |- F/ y ph $.
	enfabd2_1 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
	nfabd2 $p |- ( ph -> F/_ x { y | ps } ) $= fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal fnfabd2_2 fnfabd2_1 fnfabd2_3 cab wnfc fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn fnfabd2_2 fnfabd2_1 fnfabd2_3 cab wnfc fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn wa fnfabd2_2 infabd2_0 fnfabd2_1 fnfabd2_3 cab fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn wa infabd2_0 nfv infabd2_0 sup_set_class fnfabd2_1 fnfabd2_3 cab wcel fnfabd2_1 fnfabd2_3 infabd2_0 wsb fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn wa fnfabd2_2 fnfabd2_1 infabd2_0 fnfabd2_3 df-clab fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn wa fnfabd2_1 fnfabd2_3 infabd2_0 fnfabd2_2 fnfabd2_0 fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal wn fnfabd2_3 enfabd2_0 fnfabd2_2 fnfabd2_3 fnfabd2_3 nfnae nfan enfabd2_1 nfsbd nfxfrd nfcd ex fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal fnfabd2_2 fnfabd2_1 fnfabd2_3 cab wnfc fnfabd2_3 fnfabd2_1 fnfabd2_3 cab wnfc fnfabd2_1 fnfabd2_3 nfab1 fnfabd2_2 fnfabd2_3 fnfabd2_1 fnfabd2_3 cab fnfabd2_1 fnfabd2_3 cab fnfabd2_2 sup_set_class fnfabd2_3 sup_set_class wceq fnfabd2_2 wal fnfabd2_1 fnfabd2_3 cab eqidd drnfc1 mpbiri pm2.61d2 $.
$}
$( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)
${
	fnfabd_0 $f wff ph $.
	fnfabd_1 $f wff ps $.
	fnfabd_2 $f set x $.
	fnfabd_3 $f set y $.
	enfabd_0 $e |- F/ y ph $.
	enfabd_1 $e |- ( ph -> F/ x ps ) $.
	nfabd $p |- ( ph -> F/_ x { y | ps } ) $= fnfabd_0 fnfabd_1 fnfabd_2 fnfabd_3 enfabd_0 fnfabd_0 fnfabd_1 fnfabd_2 wnf fnfabd_2 sup_set_class fnfabd_3 sup_set_class wceq fnfabd_2 wal wn enfabd_1 adantr nfabd2 $.
$}
$( Deduction form of ~ dvelimc .  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
${
	$d w x $.
	$d w y $.
	$d w z $.
	$d w A $.
	$d w B $.
	$d w ph $.
	idvelimdc_0 $f set w $.
	fdvelimdc_0 $f wff ph $.
	fdvelimdc_1 $f set x $.
	fdvelimdc_2 $f set y $.
	fdvelimdc_3 $f set z $.
	fdvelimdc_4 $f class A $.
	fdvelimdc_5 $f class B $.
	edvelimdc_0 $e |- F/ x ph $.
	edvelimdc_1 $e |- F/ z ph $.
	edvelimdc_2 $e |- ( ph -> F/_ x A ) $.
	edvelimdc_3 $e |- ( ph -> F/_ z B ) $.
	edvelimdc_4 $e |- ( ph -> ( z = y -> A = B ) ) $.
	dvelimdc $p |- ( ph -> ( -. A. x x = y -> F/_ x B ) ) $= fdvelimdc_0 fdvelimdc_1 sup_set_class fdvelimdc_2 sup_set_class wceq fdvelimdc_1 wal wn fdvelimdc_1 fdvelimdc_5 wnfc fdvelimdc_0 fdvelimdc_1 sup_set_class fdvelimdc_2 sup_set_class wceq fdvelimdc_1 wal wn wa fdvelimdc_1 idvelimdc_0 fdvelimdc_5 fdvelimdc_0 fdvelimdc_1 sup_set_class fdvelimdc_2 sup_set_class wceq fdvelimdc_1 wal wn wa idvelimdc_0 nfv fdvelimdc_0 fdvelimdc_1 sup_set_class fdvelimdc_2 sup_set_class wceq fdvelimdc_1 wal wn idvelimdc_0 sup_set_class fdvelimdc_5 wcel fdvelimdc_1 wnf fdvelimdc_0 idvelimdc_0 sup_set_class fdvelimdc_4 wcel idvelimdc_0 sup_set_class fdvelimdc_5 wcel fdvelimdc_1 fdvelimdc_2 fdvelimdc_3 edvelimdc_0 edvelimdc_1 fdvelimdc_0 fdvelimdc_1 idvelimdc_0 fdvelimdc_4 edvelimdc_2 nfcrd fdvelimdc_0 fdvelimdc_3 idvelimdc_0 fdvelimdc_5 edvelimdc_3 nfcrd fdvelimdc_0 fdvelimdc_3 sup_set_class fdvelimdc_2 sup_set_class wceq fdvelimdc_4 fdvelimdc_5 wceq idvelimdc_0 sup_set_class fdvelimdc_4 wcel idvelimdc_0 sup_set_class fdvelimdc_5 wcel wb edvelimdc_4 fdvelimdc_4 fdvelimdc_5 idvelimdc_0 sup_set_class eleq2 syl6 dvelimdf imp nfcd ex $.
$}
$( Version of ~ dvelim for classes.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
${
	fdvelimc_0 $f set x $.
	fdvelimc_1 $f set y $.
	fdvelimc_2 $f set z $.
	fdvelimc_3 $f class A $.
	fdvelimc_4 $f class B $.
	edvelimc_0 $e |- F/_ x A $.
	edvelimc_1 $e |- F/_ z B $.
	edvelimc_2 $e |- ( z = y -> A = B ) $.
	dvelimc $p |- ( -. A. x x = y -> F/_ x B ) $= fdvelimc_0 sup_set_class fdvelimc_1 sup_set_class wceq fdvelimc_0 wal wn fdvelimc_0 fdvelimc_4 wnfc wi wtru fdvelimc_0 fdvelimc_1 fdvelimc_2 fdvelimc_3 fdvelimc_4 fdvelimc_0 nftru fdvelimc_2 nftru fdvelimc_0 fdvelimc_3 wnfc wtru edvelimc_0 a1i fdvelimc_2 fdvelimc_4 wnfc wtru edvelimc_1 a1i fdvelimc_2 sup_set_class fdvelimc_1 sup_set_class wceq fdvelimc_3 fdvelimc_4 wceq wi wtru edvelimc_2 a1i dvelimdc trud $.
$}
$( If ` x ` and ` y ` are distinct, then ` x ` is not free in ` y ` .
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
${
	$d x z $.
	$d y z $.
	infcvf_0 $f set z $.
	fnfcvf_0 $f set x $.
	fnfcvf_1 $f set y $.
	nfcvf $p |- ( -. A. x x = y -> F/_ x y ) $= fnfcvf_0 fnfcvf_1 infcvf_0 infcvf_0 sup_set_class fnfcvf_1 sup_set_class fnfcvf_0 infcvf_0 sup_set_class nfcv infcvf_0 fnfcvf_1 sup_set_class nfcv infcvf_0 sup_set_class fnfcvf_1 sup_set_class wceq id dvelimc $.
$}
$( If ` x ` and ` y ` are distinct, then ` y ` is not free in ` x ` .
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)
${
	fnfcvf2_0 $f set x $.
	fnfcvf2_1 $f set y $.
	nfcvf2 $p |- ( -. A. x x = y -> F/_ y x ) $= fnfcvf2_1 fnfcvf2_0 sup_set_class wnfc fnfcvf2_1 fnfcvf2_0 fnfcvf2_1 fnfcvf2_0 nfcvf naecoms $.
$}
$( Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$d y A $.
	$d y B $.
	$d x y $.
	icleqf_0 $f set y $.
	fcleqf_0 $f set x $.
	fcleqf_1 $f class A $.
	fcleqf_2 $f class B $.
	ecleqf_0 $e |- F/_ x A $.
	ecleqf_1 $e |- F/_ x B $.
	cleqf $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $= fcleqf_1 fcleqf_2 wceq icleqf_0 sup_set_class fcleqf_1 wcel icleqf_0 sup_set_class fcleqf_2 wcel wb icleqf_0 wal fcleqf_0 sup_set_class fcleqf_1 wcel fcleqf_0 sup_set_class fcleqf_2 wcel wb fcleqf_0 wal icleqf_0 fcleqf_1 fcleqf_2 dfcleq fcleqf_0 sup_set_class fcleqf_1 wcel fcleqf_0 sup_set_class fcleqf_2 wcel wb icleqf_0 sup_set_class fcleqf_1 wcel icleqf_0 sup_set_class fcleqf_2 wcel wb fcleqf_0 icleqf_0 fcleqf_0 sup_set_class fcleqf_1 wcel fcleqf_0 sup_set_class fcleqf_2 wcel wb icleqf_0 nfv icleqf_0 sup_set_class fcleqf_1 wcel icleqf_0 sup_set_class fcleqf_2 wcel fcleqf_0 fcleqf_0 icleqf_0 fcleqf_1 ecleqf_0 nfcri fcleqf_0 icleqf_0 fcleqf_2 ecleqf_1 nfcri nfbi fcleqf_0 sup_set_class icleqf_0 sup_set_class wceq fcleqf_0 sup_set_class fcleqf_1 wcel icleqf_0 sup_set_class fcleqf_1 wcel fcleqf_0 sup_set_class fcleqf_2 wcel icleqf_0 sup_set_class fcleqf_2 wcel fcleqf_0 sup_set_class icleqf_0 sup_set_class fcleqf_1 eleq1 fcleqf_0 sup_set_class icleqf_0 sup_set_class fcleqf_2 eleq1 bibi12d cbval bitr4i $.
$}
$( A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 5-Sep-2011.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	fabid2f_0 $f set x $.
	fabid2f_1 $f class A $.
	eabid2f_0 $e |- F/_ x A $.
	abid2f $p |- { x | x e. A } = A $= fabid2f_1 fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab fabid2f_1 fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab wceq fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_1 wcel wb fabid2f_0 fabid2f_1 fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab wceq fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab wcel wb fabid2f_0 wal fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_1 wcel wb fabid2f_0 wal fabid2f_0 fabid2f_1 fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab eabid2f_0 fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 nfab1 cleqf fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab wcel wb fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_1 wcel wb fabid2f_0 fabid2f_0 sup_set_class fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 cab wcel fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 sup_set_class fabid2f_1 wcel fabid2f_0 abid bibi2i albii bitri fabid2f_0 sup_set_class fabid2f_1 wcel biid mpgbir eqcomi $.
$}
$( Theorem to move a substitution in and out of a class abstraction.
       (Contributed by NM, 27-Sep-2003.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
${
	$d v A $.
	$d x z v $.
	$d y z v $.
	$d v ph $.
	isbabel_0 $f set v $.
	fsbabel_0 $f wff ph $.
	fsbabel_1 $f set x $.
	fsbabel_2 $f set y $.
	fsbabel_3 $f set z $.
	fsbabel_4 $f class A $.
	esbabel_0 $e |- F/_ x A $.
	sbabel $p |- ( [ y / x ] { z | ph } e. A <-> { z | [ y / x ] ph } e. A ) $= isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 wex fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 wex fsbabel_0 fsbabel_3 cab fsbabel_4 wcel fsbabel_1 fsbabel_2 wsb fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab fsbabel_4 wcel isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 wex fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa fsbabel_1 fsbabel_2 wsb isbabel_0 wex isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 wex isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 fsbabel_1 fsbabel_2 sbex isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_4 wcel fsbabel_1 fsbabel_2 wsb wa isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel fsbabel_1 fsbabel_2 sban isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_4 wcel fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 wb fsbabel_3 wal fsbabel_1 fsbabel_2 wsb fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 fsbabel_1 fsbabel_2 wsb wb fsbabel_3 wal isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq fsbabel_1 fsbabel_2 wsb isbabel_0 sup_set_class fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab wceq fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 wb fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 fsbabel_1 fsbabel_2 wsb wb fsbabel_1 fsbabel_2 fsbabel_3 fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 fsbabel_1 fsbabel_2 fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_1 fsbabel_2 fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_1 nfv sbf sbrbis sbalv isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq fsbabel_3 sup_set_class isbabel_0 sup_set_class wcel fsbabel_0 wb fsbabel_3 wal fsbabel_1 fsbabel_2 fsbabel_0 fsbabel_3 isbabel_0 sup_set_class abeq2 sbbii fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 isbabel_0 sup_set_class abeq2 3bitr4i isbabel_0 sup_set_class fsbabel_4 wcel fsbabel_1 fsbabel_2 fsbabel_1 isbabel_0 fsbabel_4 esbabel_0 nfcri sbf anbi12i bitri exbii bitri fsbabel_0 fsbabel_3 cab fsbabel_4 wcel isbabel_0 sup_set_class fsbabel_0 fsbabel_3 cab wceq isbabel_0 sup_set_class fsbabel_4 wcel wa isbabel_0 wex fsbabel_1 fsbabel_2 isbabel_0 fsbabel_0 fsbabel_3 cab fsbabel_4 df-clel sbbii isbabel_0 fsbabel_0 fsbabel_1 fsbabel_2 wsb fsbabel_3 cab fsbabel_4 df-clel 3bitr4i $.
$}

