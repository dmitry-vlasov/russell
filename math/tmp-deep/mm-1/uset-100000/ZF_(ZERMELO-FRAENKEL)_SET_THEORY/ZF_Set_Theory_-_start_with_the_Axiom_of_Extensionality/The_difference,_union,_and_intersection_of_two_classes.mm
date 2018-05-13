$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Subclasses_and_subsets.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The difference, union, and intersection of two classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_difeq1 $f class A $.
	f1_difeq1 $f class B $.
	f2_difeq1 $f class C $.
	i0_difeq1 $f set x $.
	p_difeq1 $p |- ( A = B -> ( A \ C ) = ( B \ C ) ) $= i0_difeq1 a_sup_set_class f2_difeq1 a_wcel a_wn i0_difeq1 f0_difeq1 f1_difeq1 p_rabeq i0_difeq1 f0_difeq1 f2_difeq1 p_dfdif2 i0_difeq1 f1_difeq1 f2_difeq1 p_dfdif2 f0_difeq1 f1_difeq1 a_wceq i0_difeq1 a_sup_set_class f2_difeq1 a_wcel a_wn i0_difeq1 f0_difeq1 a_crab i0_difeq1 a_sup_set_class f2_difeq1 a_wcel a_wn i0_difeq1 f1_difeq1 a_crab f0_difeq1 f2_difeq1 a_cdif f1_difeq1 f2_difeq1 a_cdif p_3eqtr4g $.
$}

$(Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_difeq2 $f class A $.
	f1_difeq2 $f class B $.
	f2_difeq2 $f class C $.
	i0_difeq2 $f set x $.
	p_difeq2 $p |- ( A = B -> ( C \ A ) = ( C \ B ) ) $= f0_difeq2 f1_difeq2 i0_difeq2 a_sup_set_class p_eleq2 f0_difeq2 f1_difeq2 a_wceq i0_difeq2 a_sup_set_class f0_difeq2 a_wcel i0_difeq2 a_sup_set_class f1_difeq2 a_wcel p_notbid f0_difeq2 f1_difeq2 a_wceq i0_difeq2 a_sup_set_class f0_difeq2 a_wcel a_wn i0_difeq2 a_sup_set_class f1_difeq2 a_wcel a_wn i0_difeq2 f2_difeq2 p_rabbidv i0_difeq2 f2_difeq2 f0_difeq2 p_dfdif2 i0_difeq2 f2_difeq2 f1_difeq2 p_dfdif2 f0_difeq2 f1_difeq2 a_wceq i0_difeq2 a_sup_set_class f0_difeq2 a_wcel a_wn i0_difeq2 f2_difeq2 a_crab i0_difeq2 a_sup_set_class f1_difeq2 a_wcel a_wn i0_difeq2 f2_difeq2 a_crab f2_difeq2 f0_difeq2 a_cdif f2_difeq2 f1_difeq2 a_cdif p_3eqtr4g $.
$}

$(Equality theorem for class difference.  (Contributed by FL,
     31-Aug-2009.) $)

${
	$v A B C D  $.
	f0_difeq12 $f class A $.
	f1_difeq12 $f class B $.
	f2_difeq12 $f class C $.
	f3_difeq12 $f class D $.
	p_difeq12 $p |- ( ( A = B /\ C = D ) -> ( A \ C ) = ( B \ D ) ) $= f0_difeq12 f1_difeq12 f2_difeq12 p_difeq1 f2_difeq12 f3_difeq12 f1_difeq12 p_difeq2 f0_difeq12 f1_difeq12 a_wceq f2_difeq12 f3_difeq12 a_wceq f0_difeq12 f2_difeq12 a_cdif f1_difeq12 f2_difeq12 a_cdif f1_difeq12 f3_difeq12 a_cdif p_sylan9eq $.
$}

$(Inference adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)

${
	$v A B C  $.
	f0_difeq1i $f class A $.
	f1_difeq1i $f class B $.
	f2_difeq1i $f class C $.
	e0_difeq1i $e |- A = B $.
	p_difeq1i $p |- ( A \ C ) = ( B \ C ) $= e0_difeq1i f0_difeq1i f1_difeq1i f2_difeq1i p_difeq1 f0_difeq1i f1_difeq1i a_wceq f0_difeq1i f2_difeq1i a_cdif f1_difeq1i f2_difeq1i a_cdif a_wceq a_ax-mp $.
$}

$(Inference adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)

${
	$v A B C  $.
	f0_difeq2i $f class A $.
	f1_difeq2i $f class B $.
	f2_difeq2i $f class C $.
	e0_difeq2i $e |- A = B $.
	p_difeq2i $p |- ( C \ A ) = ( C \ B ) $= e0_difeq2i f0_difeq2i f1_difeq2i f2_difeq2i p_difeq2 f0_difeq2i f1_difeq2i a_wceq f2_difeq2i f0_difeq2i a_cdif f2_difeq2i f1_difeq2i a_cdif a_wceq a_ax-mp $.
$}

$(Equality inference for class difference.  (Contributed by NM,
         29-Aug-2004.) $)

${
	$v A B C D  $.
	f0_difeq12i $f class A $.
	f1_difeq12i $f class B $.
	f2_difeq12i $f class C $.
	f3_difeq12i $f class D $.
	e0_difeq12i $e |- A = B $.
	e1_difeq12i $e |- C = D $.
	p_difeq12i $p |- ( A \ C ) = ( B \ D ) $= e0_difeq12i f0_difeq12i f1_difeq12i f2_difeq12i p_difeq1i e1_difeq12i f2_difeq12i f3_difeq12i f1_difeq12i p_difeq2i f0_difeq12i f2_difeq12i a_cdif f1_difeq12i f2_difeq12i a_cdif f1_difeq12i f3_difeq12i a_cdif p_eqtri $.
$}

$(Deduction adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)

${
	$v ph A B C  $.
	f0_difeq1d $f wff ph $.
	f1_difeq1d $f class A $.
	f2_difeq1d $f class B $.
	f3_difeq1d $f class C $.
	e0_difeq1d $e |- ( ph -> A = B ) $.
	p_difeq1d $p |- ( ph -> ( A \ C ) = ( B \ C ) ) $= e0_difeq1d f1_difeq1d f2_difeq1d f3_difeq1d p_difeq1 f0_difeq1d f1_difeq1d f2_difeq1d a_wceq f1_difeq1d f3_difeq1d a_cdif f2_difeq1d f3_difeq1d a_cdif a_wceq p_syl $.
$}

$(Deduction adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)

${
	$v ph A B C  $.
	f0_difeq2d $f wff ph $.
	f1_difeq2d $f class A $.
	f2_difeq2d $f class B $.
	f3_difeq2d $f class C $.
	e0_difeq2d $e |- ( ph -> A = B ) $.
	p_difeq2d $p |- ( ph -> ( C \ A ) = ( C \ B ) ) $= e0_difeq2d f1_difeq2d f2_difeq2d f3_difeq2d p_difeq2 f0_difeq2d f1_difeq2d f2_difeq2d a_wceq f3_difeq2d f1_difeq2d a_cdif f3_difeq2d f2_difeq2d a_cdif a_wceq p_syl $.
$}

$(Equality deduction for class difference.  (Contributed by FL,
       29-May-2014.) $)

${
	$v ph A B C D  $.
	f0_difeq12d $f wff ph $.
	f1_difeq12d $f class A $.
	f2_difeq12d $f class B $.
	f3_difeq12d $f class C $.
	f4_difeq12d $f class D $.
	e0_difeq12d $e |- ( ph -> A = B ) $.
	e1_difeq12d $e |- ( ph -> C = D ) $.
	p_difeq12d $p |- ( ph -> ( A \ C ) = ( B \ D ) ) $= e0_difeq12d f0_difeq12d f1_difeq12d f2_difeq12d f3_difeq12d p_difeq1d e1_difeq12d f0_difeq12d f3_difeq12d f4_difeq12d f2_difeq12d p_difeq2d f0_difeq12d f1_difeq12d f3_difeq12d a_cdif f2_difeq12d f3_difeq12d a_cdif f2_difeq12d f4_difeq12d a_cdif p_eqtrd $.
$}

$(Inference from membership to difference.  (Contributed by NM,
       17-May-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_difeqri $f set x $.
	f1_difeqri $f class A $.
	f2_difeqri $f class B $.
	f3_difeqri $f class C $.
	e0_difeqri $e |- ( ( x e. A /\ -. x e. B ) <-> x e. C ) $.
	p_difeqri $p |- ( A \ B ) = C $= f0_difeqri a_sup_set_class f1_difeqri f2_difeqri p_eldif e0_difeqri f0_difeqri a_sup_set_class f1_difeqri f2_difeqri a_cdif a_wcel f0_difeqri a_sup_set_class f1_difeqri a_wcel f0_difeqri a_sup_set_class f2_difeqri a_wcel a_wn a_wa f0_difeqri a_sup_set_class f3_difeqri a_wcel p_bitri f0_difeqri f1_difeqri f2_difeqri a_cdif f3_difeqri p_eqriv $.
$}

$(Bound-variable hypothesis builder for class difference.  (Contributed by
       NM, 3-Dec-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_nfdif $f set x $.
	f1_nfdif $f class A $.
	f2_nfdif $f class B $.
	i0_nfdif $f set y $.
	e0_nfdif $e |- F/_ x A $.
	e1_nfdif $e |- F/_ x B $.
	p_nfdif $p |- F/_ x ( A \ B ) $= i0_nfdif f1_nfdif f2_nfdif p_dfdif2 e1_nfdif f0_nfdif i0_nfdif f2_nfdif p_nfcri i0_nfdif a_sup_set_class f2_nfdif a_wcel f0_nfdif p_nfn e0_nfdif i0_nfdif a_sup_set_class f2_nfdif a_wcel a_wn f0_nfdif i0_nfdif f1_nfdif p_nfrab f0_nfdif f1_nfdif f2_nfdif a_cdif i0_nfdif a_sup_set_class f2_nfdif a_wcel a_wn i0_nfdif f1_nfdif a_crab p_nfcxfr $.
$}

$(Implication of membership in a class difference.  (Contributed by NM,
     29-Apr-1994.) $)

${
	$v A B C  $.
	f0_eldifi $f class A $.
	f1_eldifi $f class B $.
	f2_eldifi $f class C $.
	p_eldifi $p |- ( A e. ( B \ C ) -> A e. B ) $= f0_eldifi f1_eldifi f2_eldifi p_eldif f0_eldifi f1_eldifi f2_eldifi a_cdif a_wcel f0_eldifi f1_eldifi a_wcel f0_eldifi f2_eldifi a_wcel a_wn p_simplbi $.
$}

$(Implication of membership in a class difference.  (Contributed by NM,
     3-May-1994.) $)

${
	$v A B C  $.
	f0_eldifn $f class A $.
	f1_eldifn $f class B $.
	f2_eldifn $f class C $.
	p_eldifn $p |- ( A e. ( B \ C ) -> -. A e. C ) $= f0_eldifn f1_eldifn f2_eldifn p_eldif f0_eldifn f1_eldifn f2_eldifn a_cdif a_wcel f0_eldifn f1_eldifn a_wcel f0_eldifn f2_eldifn a_wcel a_wn p_simprbi $.
$}

$(A set does not belong to a class excluding it.  (Contributed by NM,
     27-Jun-1994.) $)

${
	$v A B C  $.
	f0_elndif $f class A $.
	f1_elndif $f class B $.
	f2_elndif $f class C $.
	p_elndif $p |- ( A e. B -> -. A e. ( C \ B ) ) $= f0_elndif f2_elndif f1_elndif p_eldifn f0_elndif f2_elndif f1_elndif a_cdif a_wcel f0_elndif f1_elndif a_wcel p_con2i $.
$}

$(Implication of membership in a class difference.  (Contributed by NM,
     28-Jun-1994.) $)

${
	$v A B C  $.
	f0_neldif $f class A $.
	f1_neldif $f class B $.
	f2_neldif $f class C $.
	p_neldif $p |- ( ( A e. B /\ -. A e. ( B \ C ) ) -> A e. C ) $= f0_neldif f1_neldif f2_neldif p_eldif f0_neldif f1_neldif f2_neldif a_cdif a_wcel f0_neldif f1_neldif a_wcel f0_neldif f2_neldif a_wcel a_wn p_simplbi2 f0_neldif f1_neldif a_wcel f0_neldif f2_neldif a_wcel f0_neldif f1_neldif f2_neldif a_cdif a_wcel p_con1d f0_neldif f1_neldif a_wcel f0_neldif f1_neldif f2_neldif a_cdif a_wcel a_wn f0_neldif f2_neldif a_wcel p_imp $.
$}

$(Double class difference.  Exercise 11 of [TakeutiZaring] p. 22.
       (Contributed by NM, 17-May-1998.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_difdif $f class A $.
	f1_difdif $f class B $.
	i0_difdif $f set x $.
	p_difdif $p |- ( A \ ( B \ A ) ) = A $= i0_difdif a_sup_set_class f0_difdif a_wcel i0_difdif a_sup_set_class f1_difdif a_wcel p_pm4.45im i0_difdif a_sup_set_class f1_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel p_iman i0_difdif a_sup_set_class f1_difdif f0_difdif p_eldif i0_difdif a_sup_set_class f1_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel a_wi i0_difdif a_sup_set_class f1_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel a_wn a_wa i0_difdif a_sup_set_class f1_difdif f0_difdif a_cdif a_wcel p_xchbinxr i0_difdif a_sup_set_class f1_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel a_wi i0_difdif a_sup_set_class f1_difdif f0_difdif a_cdif a_wcel a_wn i0_difdif a_sup_set_class f0_difdif a_wcel p_anbi2i i0_difdif a_sup_set_class f0_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel i0_difdif a_sup_set_class f1_difdif a_wcel i0_difdif a_sup_set_class f0_difdif a_wcel a_wi a_wa i0_difdif a_sup_set_class f0_difdif a_wcel i0_difdif a_sup_set_class f1_difdif f0_difdif a_cdif a_wcel a_wn a_wa p_bitr2i i0_difdif f0_difdif f1_difdif f0_difdif a_cdif f0_difdif p_difeqri $.
$}

$(Subclass relationship for class difference.  Exercise 14 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_difss $f class A $.
	f1_difss $f class B $.
	i0_difss $f set x $.
	p_difss $p |- ( A \ B ) C_ A $= i0_difss a_sup_set_class f0_difss f1_difss p_eldifi i0_difss f0_difss f1_difss a_cdif f0_difss p_ssriv $.
$}

$(A difference of two classes is contained in the minuend.  Deduction form
     of ~ difss .  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B  $.
	f0_difssd $f wff ph $.
	f1_difssd $f class A $.
	f2_difssd $f class B $.
	p_difssd $p |- ( ph -> ( A \ B ) C_ A ) $= f1_difssd f2_difssd p_difss f1_difssd f2_difssd a_cdif f1_difssd a_wss f0_difssd p_a1i $.
$}

$(If a class is contained in a difference, it is contained in the minuend.
     (Contributed by David Moews, 1-May-2017.) $)

${
	$v A B C  $.
	f0_difss2 $f class A $.
	f1_difss2 $f class B $.
	f2_difss2 $f class C $.
	p_difss2 $p |- ( A C_ ( B \ C ) -> A C_ B ) $= f0_difss2 f1_difss2 f2_difss2 a_cdif a_wss p_id f1_difss2 f2_difss2 p_difss f0_difss2 f1_difss2 f2_difss2 a_cdif a_wss f0_difss2 f1_difss2 f2_difss2 a_cdif f1_difss2 p_syl6ss $.
$}

$(If a class is contained in a difference, it is contained in the
       minuend.  Deduction form of ~ difss2 .  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_difss2d $f wff ph $.
	f1_difss2d $f class A $.
	f2_difss2d $f class B $.
	f3_difss2d $f class C $.
	e0_difss2d $e |- ( ph -> A C_ ( B \ C ) ) $.
	p_difss2d $p |- ( ph -> A C_ B ) $= e0_difss2d f1_difss2d f2_difss2d f3_difss2d p_difss2 f0_difss2d f1_difss2d f2_difss2d f3_difss2d a_cdif a_wss f1_difss2d f2_difss2d a_wss p_syl $.
$}

$(Preservation of a subclass relationship by class difference.  (Contributed
     by NM, 15-Feb-2007.) $)

${
	$v A B C  $.
	f0_ssdifss $f class A $.
	f1_ssdifss $f class B $.
	f2_ssdifss $f class C $.
	p_ssdifss $p |- ( A C_ B -> ( A \ C ) C_ B ) $= f0_ssdifss f2_ssdifss p_difss f0_ssdifss f2_ssdifss a_cdif f0_ssdifss f1_ssdifss p_sstr f0_ssdifss f2_ssdifss a_cdif f0_ssdifss a_wss f0_ssdifss f1_ssdifss a_wss f0_ssdifss f2_ssdifss a_cdif f1_ssdifss a_wss p_mpan $.
$}

$(Double complement under universal class.  Exercise 4.10(s) of
       [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)

${
	$v A  $.
	$d x A  $.
	f0_ddif $f class A $.
	i0_ddif $f set x $.
	p_ddif $p |- ( _V \ ( _V \ A ) ) = A $= i0_ddif p_vex i0_ddif a_sup_set_class a_cvv f0_ddif p_eldif i0_ddif a_sup_set_class a_cvv f0_ddif a_cdif a_wcel i0_ddif a_sup_set_class a_cvv a_wcel i0_ddif a_sup_set_class f0_ddif a_wcel a_wn p_mpbiran i0_ddif a_sup_set_class a_cvv f0_ddif a_cdif a_wcel i0_ddif a_sup_set_class f0_ddif a_wcel p_con2bii i0_ddif p_vex i0_ddif a_sup_set_class a_cvv a_wcel i0_ddif a_sup_set_class a_cvv f0_ddif a_cdif a_wcel a_wn p_biantrur i0_ddif a_sup_set_class f0_ddif a_wcel i0_ddif a_sup_set_class a_cvv f0_ddif a_cdif a_wcel a_wn i0_ddif a_sup_set_class a_cvv a_wcel i0_ddif a_sup_set_class a_cvv f0_ddif a_cdif a_wcel a_wn a_wa p_bitr2i i0_ddif a_cvv a_cvv f0_ddif a_cdif f0_ddif p_difeqri $.
$}

$(Contraposition law for subsets.  (Contributed by NM, 22-Mar-1998.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssconb $f class A $.
	f1_ssconb $f class B $.
	f2_ssconb $f class C $.
	i0_ssconb $f set x $.
	p_ssconb $p |- ( ( A C_ C /\ B C_ C ) -> ( A C_ ( C \ B ) <-> B C_ ( C \ A ) ) ) $= f0_ssconb f2_ssconb i0_ssconb a_sup_set_class p_ssel f1_ssconb f2_ssconb i0_ssconb a_sup_set_class p_ssel i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi p_pm5.1 f0_ssconb f2_ssconb a_wss i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi a_wb f1_ssconb f2_ssconb a_wss p_syl2an i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel p_con2b i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wi a_wb f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa p_a1i f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wi p_anbi12d i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn p_jcab i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn p_jcab f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wi a_wa i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wi a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wa a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wa a_wi p_3bitr4g i0_ssconb a_sup_set_class f2_ssconb f1_ssconb p_eldif i0_ssconb a_sup_set_class f2_ssconb f1_ssconb a_cdif a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel p_imbi2i i0_ssconb a_sup_set_class f2_ssconb f0_ssconb p_eldif i0_ssconb a_sup_set_class f2_ssconb f0_ssconb a_cdif a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wa i0_ssconb a_sup_set_class f1_ssconb a_wcel p_imbi2i f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f1_ssconb a_wcel a_wn a_wa a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb a_wcel i0_ssconb a_sup_set_class f0_ssconb a_wcel a_wn a_wa a_wi i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f1_ssconb a_cdif a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f0_ssconb a_cdif a_wcel a_wi p_3bitr4g f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f1_ssconb a_cdif a_wcel a_wi i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f0_ssconb a_cdif a_wcel a_wi i0_ssconb p_albidv i0_ssconb f0_ssconb f2_ssconb f1_ssconb a_cdif p_dfss2 i0_ssconb f1_ssconb f2_ssconb f0_ssconb a_cdif p_dfss2 f0_ssconb f2_ssconb a_wss f1_ssconb f2_ssconb a_wss a_wa i0_ssconb a_sup_set_class f0_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f1_ssconb a_cdif a_wcel a_wi i0_ssconb a_wal i0_ssconb a_sup_set_class f1_ssconb a_wcel i0_ssconb a_sup_set_class f2_ssconb f0_ssconb a_cdif a_wcel a_wi i0_ssconb a_wal f0_ssconb f2_ssconb f1_ssconb a_cdif a_wss f1_ssconb f2_ssconb f0_ssconb a_cdif a_wss p_3bitr4g $.
$}

$(Contraposition law for subsets.  Exercise 15 of [TakeutiZaring] p. 22.
       (Contributed by NM, 22-Mar-1998.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_sscon $f class A $.
	f1_sscon $f class B $.
	f2_sscon $f class C $.
	i0_sscon $f set x $.
	p_sscon $p |- ( A C_ B -> ( C \ B ) C_ ( C \ A ) ) $= f0_sscon f1_sscon i0_sscon a_sup_set_class p_ssel f0_sscon f1_sscon a_wss i0_sscon a_sup_set_class f0_sscon a_wcel i0_sscon a_sup_set_class f1_sscon a_wcel p_con3d f0_sscon f1_sscon a_wss i0_sscon a_sup_set_class f1_sscon a_wcel a_wn i0_sscon a_sup_set_class f0_sscon a_wcel a_wn i0_sscon a_sup_set_class f2_sscon a_wcel p_anim2d i0_sscon a_sup_set_class f2_sscon f1_sscon p_eldif i0_sscon a_sup_set_class f2_sscon f0_sscon p_eldif f0_sscon f1_sscon a_wss i0_sscon a_sup_set_class f2_sscon a_wcel i0_sscon a_sup_set_class f1_sscon a_wcel a_wn a_wa i0_sscon a_sup_set_class f2_sscon a_wcel i0_sscon a_sup_set_class f0_sscon a_wcel a_wn a_wa i0_sscon a_sup_set_class f2_sscon f1_sscon a_cdif a_wcel i0_sscon a_sup_set_class f2_sscon f0_sscon a_cdif a_wcel p_3imtr4g f0_sscon f1_sscon a_wss i0_sscon f2_sscon f1_sscon a_cdif f2_sscon f0_sscon a_cdif p_ssrdv $.
$}

$(Difference law for subsets.  (Contributed by NM, 28-May-1998.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssdif $f class A $.
	f1_ssdif $f class B $.
	f2_ssdif $f class C $.
	i0_ssdif $f set x $.
	p_ssdif $p |- ( A C_ B -> ( A \ C ) C_ ( B \ C ) ) $= f0_ssdif f1_ssdif i0_ssdif a_sup_set_class p_ssel f0_ssdif f1_ssdif a_wss i0_ssdif a_sup_set_class f0_ssdif a_wcel i0_ssdif a_sup_set_class f1_ssdif a_wcel i0_ssdif a_sup_set_class f2_ssdif a_wcel a_wn p_anim1d i0_ssdif a_sup_set_class f0_ssdif f2_ssdif p_eldif i0_ssdif a_sup_set_class f1_ssdif f2_ssdif p_eldif f0_ssdif f1_ssdif a_wss i0_ssdif a_sup_set_class f0_ssdif a_wcel i0_ssdif a_sup_set_class f2_ssdif a_wcel a_wn a_wa i0_ssdif a_sup_set_class f1_ssdif a_wcel i0_ssdif a_sup_set_class f2_ssdif a_wcel a_wn a_wa i0_ssdif a_sup_set_class f0_ssdif f2_ssdif a_cdif a_wcel i0_ssdif a_sup_set_class f1_ssdif f2_ssdif a_cdif a_wcel p_3imtr4g f0_ssdif f1_ssdif a_wss i0_ssdif f0_ssdif f2_ssdif a_cdif f1_ssdif f2_ssdif a_cdif p_ssrdv $.
$}

$(If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is contained in
       ` ( B \ C ) ` .  Deduction form of ~ ssdif .  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssdifd $f wff ph $.
	f1_ssdifd $f class A $.
	f2_ssdifd $f class B $.
	f3_ssdifd $f class C $.
	e0_ssdifd $e |- ( ph -> A C_ B ) $.
	p_ssdifd $p |- ( ph -> ( A \ C ) C_ ( B \ C ) ) $= e0_ssdifd f1_ssdifd f2_ssdifd f3_ssdifd p_ssdif f0_ssdifd f1_ssdifd f2_ssdifd a_wss f1_ssdifd f3_ssdifd a_cdif f2_ssdifd f3_ssdifd a_cdif a_wss p_syl $.
$}

$(If ` A ` is contained in ` B ` , then ` ( C \ B ) ` is contained in
       ` ( C \ A ) ` .  Deduction form of ~ sscon .  (Contributed by David
       Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_sscond $f wff ph $.
	f1_sscond $f class A $.
	f2_sscond $f class B $.
	f3_sscond $f class C $.
	e0_sscond $e |- ( ph -> A C_ B ) $.
	p_sscond $p |- ( ph -> ( C \ B ) C_ ( C \ A ) ) $= e0_sscond f1_sscond f2_sscond f3_sscond p_sscon f0_sscond f1_sscond f2_sscond a_wss f3_sscond f2_sscond a_cdif f3_sscond f1_sscond a_cdif a_wss p_syl $.
$}

$(If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is also contained in
       ` B ` .  Deduction form of ~ ssdifss .  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssdifssd $f wff ph $.
	f1_ssdifssd $f class A $.
	f2_ssdifssd $f class B $.
	f3_ssdifssd $f class C $.
	e0_ssdifssd $e |- ( ph -> A C_ B ) $.
	p_ssdifssd $p |- ( ph -> ( A \ C ) C_ B ) $= e0_ssdifssd f1_ssdifssd f2_ssdifssd f3_ssdifssd p_ssdifss f0_ssdifssd f1_ssdifssd f2_ssdifssd a_wss f1_ssdifssd f3_ssdifssd a_cdif f2_ssdifssd a_wss p_syl $.
$}

$(If ` A ` is contained in ` B ` and ` C ` is contained in ` D ` , then
       ` ( A \ D ) ` is contained in ` ( B \ C ) ` .  Deduction form.
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B C D  $.
	f0_ssdif2d $f wff ph $.
	f1_ssdif2d $f class A $.
	f2_ssdif2d $f class B $.
	f3_ssdif2d $f class C $.
	f4_ssdif2d $f class D $.
	e0_ssdif2d $e |- ( ph -> A C_ B ) $.
	e1_ssdif2d $e |- ( ph -> C C_ D ) $.
	p_ssdif2d $p |- ( ph -> ( A \ D ) C_ ( B \ C ) ) $= e1_ssdif2d f0_ssdif2d f3_ssdif2d f4_ssdif2d f1_ssdif2d p_sscond e0_ssdif2d f0_ssdif2d f1_ssdif2d f2_ssdif2d f3_ssdif2d p_ssdifd f0_ssdif2d f1_ssdif2d f4_ssdif2d a_cdif f1_ssdif2d f3_ssdif2d a_cdif f2_ssdif2d f3_ssdif2d a_cdif p_sstrd $.
$}

$(Expansion of membership in class union.  Theorem 12 of [Suppes] p. 25.
       (Contributed by NM, 7-Aug-1994.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elun $f class A $.
	f1_elun $f class B $.
	f2_elun $f class C $.
	i0_elun $f set x $.
	p_elun $p |- ( A e. ( B u. C ) <-> ( A e. B \/ A e. C ) ) $= f0_elun f1_elun f2_elun a_cun p_elex f0_elun f1_elun p_elex f0_elun f2_elun p_elex f0_elun f1_elun a_wcel f0_elun a_cvv a_wcel f0_elun f2_elun a_wcel p_jaoi i0_elun a_sup_set_class f0_elun f1_elun p_eleq1 i0_elun a_sup_set_class f0_elun f2_elun p_eleq1 i0_elun a_sup_set_class f0_elun a_wceq i0_elun a_sup_set_class f1_elun a_wcel f0_elun f1_elun a_wcel i0_elun a_sup_set_class f2_elun a_wcel f0_elun f2_elun a_wcel p_orbi12d i0_elun f1_elun f2_elun a_df-un i0_elun a_sup_set_class f1_elun a_wcel i0_elun a_sup_set_class f2_elun a_wcel a_wo f0_elun f1_elun a_wcel f0_elun f2_elun a_wcel a_wo i0_elun f0_elun f1_elun f2_elun a_cun a_cvv p_elab2g f0_elun f1_elun f2_elun a_cun a_wcel f0_elun a_cvv a_wcel f0_elun f1_elun a_wcel f0_elun f2_elun a_wcel a_wo p_pm5.21nii $.
$}

$(Inference from membership to union.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_uneqri $f set x $.
	f1_uneqri $f class A $.
	f2_uneqri $f class B $.
	f3_uneqri $f class C $.
	e0_uneqri $e |- ( ( x e. A \/ x e. B ) <-> x e. C ) $.
	p_uneqri $p |- ( A u. B ) = C $= f0_uneqri a_sup_set_class f1_uneqri f2_uneqri p_elun e0_uneqri f0_uneqri a_sup_set_class f1_uneqri f2_uneqri a_cun a_wcel f0_uneqri a_sup_set_class f1_uneqri a_wcel f0_uneqri a_sup_set_class f2_uneqri a_wcel a_wo f0_uneqri a_sup_set_class f3_uneqri a_wcel p_bitri f0_uneqri f1_uneqri f2_uneqri a_cun f3_uneqri p_eqriv $.
$}

$(Idempotent law for union of classes.  Theorem 23 of [Suppes] p. 27.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_unidm $f class A $.
	i0_unidm $f set x $.
	p_unidm $p |- ( A u. A ) = A $= i0_unidm a_sup_set_class f0_unidm a_wcel p_oridm i0_unidm f0_unidm f0_unidm f0_unidm p_uneqri $.
$}

$(Commutative law for union of classes.  Exercise 6 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_uncom $f class A $.
	f1_uncom $f class B $.
	i0_uncom $f set x $.
	p_uncom $p |- ( A u. B ) = ( B u. A ) $= i0_uncom a_sup_set_class f0_uncom a_wcel i0_uncom a_sup_set_class f1_uncom a_wcel p_orcom i0_uncom a_sup_set_class f1_uncom f0_uncom p_elun i0_uncom a_sup_set_class f0_uncom a_wcel i0_uncom a_sup_set_class f1_uncom a_wcel a_wo i0_uncom a_sup_set_class f1_uncom a_wcel i0_uncom a_sup_set_class f0_uncom a_wcel a_wo i0_uncom a_sup_set_class f1_uncom f0_uncom a_cun a_wcel p_bitr4i i0_uncom f0_uncom f1_uncom f1_uncom f0_uncom a_cun p_uneqri $.
$}

$(If a class equals the union of two other classes, then it equals the
       union of those two classes commuted. ~ equncom was automatically derived
       from ~ equncomVD using the tools program
       translate_without_overwriting.cmd and minimizing.  (Contributed by Alan
       Sare, 18-Feb-2012.) $)

${
	$v A B C  $.
	f0_equncom $f class A $.
	f1_equncom $f class B $.
	f2_equncom $f class C $.
	p_equncom $p |- ( A = ( B u. C ) <-> A = ( C u. B ) ) $= f1_equncom f2_equncom p_uncom f1_equncom f2_equncom a_cun f2_equncom f1_equncom a_cun f0_equncom p_eqeq2i $.
$}

$(Inference form of ~ equncom . ~ equncomi was automatically derived from
       ~ equncomiVD using the tools program translate_without_overwriting.cmd
       and minimizing.  (Contributed by Alan Sare, 18-Feb-2012.) $)

${
	$v A B C  $.
	f0_equncomi $f class A $.
	f1_equncomi $f class B $.
	f2_equncomi $f class C $.
	e0_equncomi $e |- A = ( B u. C ) $.
	p_equncomi $p |- A = ( C u. B ) $= e0_equncomi f0_equncomi f1_equncomi f2_equncomi p_equncom f0_equncomi f1_equncomi f2_equncomi a_cun a_wceq f0_equncomi f2_equncomi f1_equncomi a_cun a_wceq p_mpbi $.
$}

$(Equality theorem for union of two classes.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_uneq1 $f class A $.
	f1_uneq1 $f class B $.
	f2_uneq1 $f class C $.
	i0_uneq1 $f set x $.
	p_uneq1 $p |- ( A = B -> ( A u. C ) = ( B u. C ) ) $= f0_uneq1 f1_uneq1 i0_uneq1 a_sup_set_class p_eleq2 f0_uneq1 f1_uneq1 a_wceq i0_uneq1 a_sup_set_class f0_uneq1 a_wcel i0_uneq1 a_sup_set_class f1_uneq1 a_wcel i0_uneq1 a_sup_set_class f2_uneq1 a_wcel p_orbi1d i0_uneq1 a_sup_set_class f0_uneq1 f2_uneq1 p_elun i0_uneq1 a_sup_set_class f1_uneq1 f2_uneq1 p_elun f0_uneq1 f1_uneq1 a_wceq i0_uneq1 a_sup_set_class f0_uneq1 a_wcel i0_uneq1 a_sup_set_class f2_uneq1 a_wcel a_wo i0_uneq1 a_sup_set_class f1_uneq1 a_wcel i0_uneq1 a_sup_set_class f2_uneq1 a_wcel a_wo i0_uneq1 a_sup_set_class f0_uneq1 f2_uneq1 a_cun a_wcel i0_uneq1 a_sup_set_class f1_uneq1 f2_uneq1 a_cun a_wcel p_3bitr4g f0_uneq1 f1_uneq1 a_wceq i0_uneq1 f0_uneq1 f2_uneq1 a_cun f1_uneq1 f2_uneq1 a_cun p_eqrdv $.
$}

$(Equality theorem for the union of two classes.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v A B C  $.
	f0_uneq2 $f class A $.
	f1_uneq2 $f class B $.
	f2_uneq2 $f class C $.
	p_uneq2 $p |- ( A = B -> ( C u. A ) = ( C u. B ) ) $= f0_uneq2 f1_uneq2 f2_uneq2 p_uneq1 f2_uneq2 f0_uneq2 p_uncom f2_uneq2 f1_uneq2 p_uncom f0_uneq2 f1_uneq2 a_wceq f0_uneq2 f2_uneq2 a_cun f1_uneq2 f2_uneq2 a_cun f2_uneq2 f0_uneq2 a_cun f2_uneq2 f1_uneq2 a_cun p_3eqtr4g $.
$}

$(Equality theorem for union of two classes.  (Contributed by NM,
     29-Mar-1998.) $)

${
	$v A B C D  $.
	f0_uneq12 $f class A $.
	f1_uneq12 $f class B $.
	f2_uneq12 $f class C $.
	f3_uneq12 $f class D $.
	p_uneq12 $p |- ( ( A = B /\ C = D ) -> ( A u. C ) = ( B u. D ) ) $= f0_uneq12 f1_uneq12 f2_uneq12 p_uneq1 f2_uneq12 f3_uneq12 f1_uneq12 p_uneq2 f0_uneq12 f1_uneq12 a_wceq f2_uneq12 f3_uneq12 a_wceq f0_uneq12 f2_uneq12 a_cun f1_uneq12 f2_uneq12 a_cun f1_uneq12 f3_uneq12 a_cun p_sylan9eq $.
$}

$(Inference adding union to the right in a class equality.  (Contributed
       by NM, 30-Aug-1993.) $)

${
	$v A B C  $.
	f0_uneq1i $f class A $.
	f1_uneq1i $f class B $.
	f2_uneq1i $f class C $.
	e0_uneq1i $e |- A = B $.
	p_uneq1i $p |- ( A u. C ) = ( B u. C ) $= e0_uneq1i f0_uneq1i f1_uneq1i f2_uneq1i p_uneq1 f0_uneq1i f1_uneq1i a_wceq f0_uneq1i f2_uneq1i a_cun f1_uneq1i f2_uneq1i a_cun a_wceq a_ax-mp $.
$}

$(Inference adding union to the left in a class equality.  (Contributed by
       NM, 30-Aug-1993.) $)

${
	$v A B C  $.
	f0_uneq2i $f class A $.
	f1_uneq2i $f class B $.
	f2_uneq2i $f class C $.
	e0_uneq2i $e |- A = B $.
	p_uneq2i $p |- ( C u. A ) = ( C u. B ) $= e0_uneq2i f0_uneq2i f1_uneq2i f2_uneq2i p_uneq2 f0_uneq2i f1_uneq2i a_wceq f2_uneq2i f0_uneq2i a_cun f2_uneq2i f1_uneq2i a_cun a_wceq a_ax-mp $.
$}

$(Equality inference for union of two classes.  (Contributed by NM,
         12-Aug-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)

${
	$v A B C D  $.
	f0_uneq12i $f class A $.
	f1_uneq12i $f class B $.
	f2_uneq12i $f class C $.
	f3_uneq12i $f class D $.
	e0_uneq12i $e |- A = B $.
	e1_uneq12i $e |- C = D $.
	p_uneq12i $p |- ( A u. C ) = ( B u. D ) $= e0_uneq12i e1_uneq12i f0_uneq12i f1_uneq12i f2_uneq12i f3_uneq12i p_uneq12 f0_uneq12i f1_uneq12i a_wceq f2_uneq12i f3_uneq12i a_wceq f0_uneq12i f2_uneq12i a_cun f1_uneq12i f3_uneq12i a_cun a_wceq p_mp2an $.
$}

$(Deduction adding union to the right in a class equality.  (Contributed
       by NM, 29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_uneq1d $f wff ph $.
	f1_uneq1d $f class A $.
	f2_uneq1d $f class B $.
	f3_uneq1d $f class C $.
	e0_uneq1d $e |- ( ph -> A = B ) $.
	p_uneq1d $p |- ( ph -> ( A u. C ) = ( B u. C ) ) $= e0_uneq1d f1_uneq1d f2_uneq1d f3_uneq1d p_uneq1 f0_uneq1d f1_uneq1d f2_uneq1d a_wceq f1_uneq1d f3_uneq1d a_cun f2_uneq1d f3_uneq1d a_cun a_wceq p_syl $.
$}

$(Deduction adding union to the left in a class equality.  (Contributed by
       NM, 29-Mar-1998.) $)

${
	$v ph A B C  $.
	f0_uneq2d $f wff ph $.
	f1_uneq2d $f class A $.
	f2_uneq2d $f class B $.
	f3_uneq2d $f class C $.
	e0_uneq2d $e |- ( ph -> A = B ) $.
	p_uneq2d $p |- ( ph -> ( C u. A ) = ( C u. B ) ) $= e0_uneq2d f1_uneq2d f2_uneq2d f3_uneq2d p_uneq2 f0_uneq2d f1_uneq2d f2_uneq2d a_wceq f3_uneq2d f1_uneq2d a_cun f3_uneq2d f2_uneq2d a_cun a_wceq p_syl $.
$}

$(Equality deduction for union of two classes.  (Contributed by NM,
         29-Sep-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph A B C D  $.
	f0_uneq12d $f wff ph $.
	f1_uneq12d $f class A $.
	f2_uneq12d $f class B $.
	f3_uneq12d $f class C $.
	f4_uneq12d $f class D $.
	e0_uneq12d $e |- ( ph -> A = B ) $.
	e1_uneq12d $e |- ( ph -> C = D ) $.
	p_uneq12d $p |- ( ph -> ( A u. C ) = ( B u. D ) ) $= e0_uneq12d e1_uneq12d f1_uneq12d f2_uneq12d f3_uneq12d f4_uneq12d p_uneq12 f0_uneq12d f1_uneq12d f2_uneq12d a_wceq f3_uneq12d f4_uneq12d a_wceq f1_uneq12d f3_uneq12d a_cun f2_uneq12d f4_uneq12d a_cun a_wceq p_syl2anc $.
$}

$(Bound-variable hypothesis builder for the union of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_nfun $f set x $.
	f1_nfun $f class A $.
	f2_nfun $f class B $.
	i0_nfun $f set y $.
	e0_nfun $e |- F/_ x A $.
	e1_nfun $e |- F/_ x B $.
	p_nfun $p |- F/_ x ( A u. B ) $= i0_nfun f1_nfun f2_nfun a_df-un e0_nfun f0_nfun i0_nfun f1_nfun p_nfcri e1_nfun f0_nfun i0_nfun f2_nfun p_nfcri i0_nfun a_sup_set_class f1_nfun a_wcel i0_nfun a_sup_set_class f2_nfun a_wcel f0_nfun p_nfor i0_nfun a_sup_set_class f1_nfun a_wcel i0_nfun a_sup_set_class f2_nfun a_wcel a_wo f0_nfun i0_nfun p_nfab f0_nfun f1_nfun f2_nfun a_cun i0_nfun a_sup_set_class f1_nfun a_wcel i0_nfun a_sup_set_class f2_nfun a_wcel a_wo i0_nfun a_cab p_nfcxfr $.
$}

$(Associative law for union of classes.  Exercise 8 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 3-May-1994.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d A x  $.
	$d B x  $.
	$d C x  $.
	f0_unass $f class A $.
	f1_unass $f class B $.
	f2_unass $f class C $.
	i0_unass $f set x $.
	p_unass $p |- ( ( A u. B ) u. C ) = ( A u. ( B u. C ) ) $= i0_unass a_sup_set_class f0_unass f1_unass f2_unass a_cun p_elun i0_unass a_sup_set_class f1_unass f2_unass p_elun i0_unass a_sup_set_class f1_unass f2_unass a_cun a_wcel i0_unass a_sup_set_class f1_unass a_wcel i0_unass a_sup_set_class f2_unass a_wcel a_wo i0_unass a_sup_set_class f0_unass a_wcel p_orbi2i i0_unass a_sup_set_class f0_unass f1_unass p_elun i0_unass a_sup_set_class f0_unass f1_unass a_cun a_wcel i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass a_wcel a_wo i0_unass a_sup_set_class f2_unass a_wcel p_orbi1i i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass a_wcel i0_unass a_sup_set_class f2_unass a_wcel p_orass i0_unass a_sup_set_class f0_unass f1_unass a_cun a_wcel i0_unass a_sup_set_class f2_unass a_wcel a_wo i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass a_wcel a_wo i0_unass a_sup_set_class f2_unass a_wcel a_wo i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass a_wcel i0_unass a_sup_set_class f2_unass a_wcel a_wo a_wo p_bitr2i i0_unass a_sup_set_class f0_unass f1_unass f2_unass a_cun a_cun a_wcel i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass f2_unass a_cun a_wcel a_wo i0_unass a_sup_set_class f0_unass a_wcel i0_unass a_sup_set_class f1_unass a_wcel i0_unass a_sup_set_class f2_unass a_wcel a_wo a_wo i0_unass a_sup_set_class f0_unass f1_unass a_cun a_wcel i0_unass a_sup_set_class f2_unass a_wcel a_wo p_3bitrri i0_unass f0_unass f1_unass a_cun f2_unass f0_unass f1_unass f2_unass a_cun a_cun p_uneqri $.
$}

$(A rearrangement of union.  (Contributed by NM, 12-Aug-2004.) $)

${
	$v A B C  $.
	f0_un12 $f class A $.
	f1_un12 $f class B $.
	f2_un12 $f class C $.
	p_un12 $p |- ( A u. ( B u. C ) ) = ( B u. ( A u. C ) ) $= f0_un12 f1_un12 p_uncom f0_un12 f1_un12 a_cun f1_un12 f0_un12 a_cun f2_un12 p_uneq1i f0_un12 f1_un12 f2_un12 p_unass f1_un12 f0_un12 f2_un12 p_unass f0_un12 f1_un12 a_cun f2_un12 a_cun f1_un12 f0_un12 a_cun f2_un12 a_cun f0_un12 f1_un12 f2_un12 a_cun a_cun f1_un12 f0_un12 f2_un12 a_cun a_cun p_3eqtr3i $.
$}

$(A rearrangement of union.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	f0_un23 $f class A $.
	f1_un23 $f class B $.
	f2_un23 $f class C $.
	p_un23 $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. B ) $= f0_un23 f1_un23 f2_un23 p_unass f0_un23 f1_un23 f2_un23 p_un12 f1_un23 f0_un23 f2_un23 a_cun p_uncom f0_un23 f1_un23 a_cun f2_un23 a_cun f0_un23 f1_un23 f2_un23 a_cun a_cun f1_un23 f0_un23 f2_un23 a_cun a_cun f0_un23 f2_un23 a_cun f1_un23 a_cun p_3eqtri $.
$}

$(A rearrangement of the union of 4 classes.  (Contributed by NM,
     12-Aug-2004.) $)

${
	$v A B C D  $.
	f0_un4 $f class A $.
	f1_un4 $f class B $.
	f2_un4 $f class C $.
	f3_un4 $f class D $.
	p_un4 $p |- ( ( A u. B ) u. ( C u. D ) ) = ( ( A u. C ) u. ( B u. D ) ) $= f1_un4 f2_un4 f3_un4 p_un12 f1_un4 f2_un4 f3_un4 a_cun a_cun f2_un4 f1_un4 f3_un4 a_cun a_cun f0_un4 p_uneq2i f0_un4 f1_un4 f2_un4 f3_un4 a_cun p_unass f0_un4 f2_un4 f1_un4 f3_un4 a_cun p_unass f0_un4 f1_un4 f2_un4 f3_un4 a_cun a_cun a_cun f0_un4 f2_un4 f1_un4 f3_un4 a_cun a_cun a_cun f0_un4 f1_un4 a_cun f2_un4 f3_un4 a_cun a_cun f0_un4 f2_un4 a_cun f1_un4 f3_un4 a_cun a_cun p_3eqtr4i $.
$}

$(Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B C  $.
	f0_unundi $f class A $.
	f1_unundi $f class B $.
	f2_unundi $f class C $.
	p_unundi $p |- ( A u. ( B u. C ) ) = ( ( A u. B ) u. ( A u. C ) ) $= f0_unundi p_unidm f0_unundi f0_unundi a_cun f0_unundi f1_unundi f2_unundi a_cun p_uneq1i f0_unundi f0_unundi f1_unundi f2_unundi p_un4 f0_unundi f0_unundi a_cun f1_unundi f2_unundi a_cun a_cun f0_unundi f1_unundi f2_unundi a_cun a_cun f0_unundi f1_unundi a_cun f0_unundi f2_unundi a_cun a_cun p_eqtr3i $.
$}

$(Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B C  $.
	f0_unundir $f class A $.
	f1_unundir $f class B $.
	f2_unundir $f class C $.
	p_unundir $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. ( B u. C ) ) $= f2_unundir p_unidm f2_unundir f2_unundir a_cun f2_unundir f0_unundir f1_unundir a_cun p_uneq2i f0_unundir f1_unundir f2_unundir f2_unundir p_un4 f0_unundir f1_unundir a_cun f2_unundir f2_unundir a_cun a_cun f0_unundir f1_unundir a_cun f2_unundir a_cun f0_unundir f2_unundir a_cun f1_unundir f2_unundir a_cun a_cun p_eqtr3i $.
$}

$(Subclass relationship for union of classes.  Theorem 25 of [Suppes]
       p. 27.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssun1 $f class A $.
	f1_ssun1 $f class B $.
	i0_ssun1 $f set x $.
	p_ssun1 $p |- A C_ ( A u. B ) $= i0_ssun1 a_sup_set_class f0_ssun1 a_wcel i0_ssun1 a_sup_set_class f1_ssun1 a_wcel p_orc i0_ssun1 a_sup_set_class f0_ssun1 f1_ssun1 p_elun i0_ssun1 a_sup_set_class f0_ssun1 a_wcel i0_ssun1 a_sup_set_class f0_ssun1 a_wcel i0_ssun1 a_sup_set_class f1_ssun1 a_wcel a_wo i0_ssun1 a_sup_set_class f0_ssun1 f1_ssun1 a_cun a_wcel p_sylibr i0_ssun1 f0_ssun1 f0_ssun1 f1_ssun1 a_cun p_ssriv $.
$}

$(Subclass relationship for union of classes.  (Contributed by NM,
     30-Aug-1993.) $)

${
	$v A B  $.
	f0_ssun2 $f class A $.
	f1_ssun2 $f class B $.
	p_ssun2 $p |- A C_ ( B u. A ) $= f0_ssun2 f1_ssun2 p_ssun1 f0_ssun2 f1_ssun2 p_uncom f0_ssun2 f0_ssun2 f1_ssun2 a_cun f1_ssun2 f0_ssun2 a_cun p_sseqtri $.
$}

$(Subclass law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_ssun3 $f class A $.
	f1_ssun3 $f class B $.
	f2_ssun3 $f class C $.
	p_ssun3 $p |- ( A C_ B -> A C_ ( B u. C ) ) $= f1_ssun3 f2_ssun3 p_ssun1 f0_ssun3 f1_ssun3 f1_ssun3 f2_ssun3 a_cun p_sstr2 f0_ssun3 f1_ssun3 a_wss f1_ssun3 f1_ssun3 f2_ssun3 a_cun a_wss f0_ssun3 f1_ssun3 f2_ssun3 a_cun a_wss p_mpi $.
$}

$(Subclass law for union of classes.  (Contributed by NM, 14-Aug-1994.) $)

${
	$v A B C  $.
	f0_ssun4 $f class A $.
	f1_ssun4 $f class B $.
	f2_ssun4 $f class C $.
	p_ssun4 $p |- ( A C_ B -> A C_ ( C u. B ) ) $= f1_ssun4 f2_ssun4 p_ssun2 f0_ssun4 f1_ssun4 f2_ssun4 f1_ssun4 a_cun p_sstr2 f0_ssun4 f1_ssun4 a_wss f1_ssun4 f2_ssun4 f1_ssun4 a_cun a_wss f0_ssun4 f2_ssun4 f1_ssun4 a_cun a_wss p_mpi $.
$}

$(Membership law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_elun1 $f class A $.
	f1_elun1 $f class B $.
	f2_elun1 $f class C $.
	p_elun1 $p |- ( A e. B -> A e. ( B u. C ) ) $= f1_elun1 f2_elun1 p_ssun1 f1_elun1 f1_elun1 f2_elun1 a_cun f0_elun1 p_sseli $.
$}

$(Membership law for union of classes.  (Contributed by NM, 30-Aug-1993.) $)

${
	$v A B C  $.
	f0_elun2 $f class A $.
	f1_elun2 $f class B $.
	f2_elun2 $f class C $.
	p_elun2 $p |- ( A e. B -> A e. ( C u. B ) ) $= f1_elun2 f2_elun2 p_ssun2 f1_elun2 f2_elun2 f1_elun2 a_cun f0_elun2 p_sseli $.
$}

$(Subclass law for union of classes.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_unss1 $f class A $.
	f1_unss1 $f class B $.
	f2_unss1 $f class C $.
	i0_unss1 $f set x $.
	p_unss1 $p |- ( A C_ B -> ( A u. C ) C_ ( B u. C ) ) $= f0_unss1 f1_unss1 i0_unss1 a_sup_set_class p_ssel f0_unss1 f1_unss1 a_wss i0_unss1 a_sup_set_class f0_unss1 a_wcel i0_unss1 a_sup_set_class f1_unss1 a_wcel i0_unss1 a_sup_set_class f2_unss1 a_wcel p_orim1d i0_unss1 a_sup_set_class f0_unss1 f2_unss1 p_elun i0_unss1 a_sup_set_class f1_unss1 f2_unss1 p_elun f0_unss1 f1_unss1 a_wss i0_unss1 a_sup_set_class f0_unss1 a_wcel i0_unss1 a_sup_set_class f2_unss1 a_wcel a_wo i0_unss1 a_sup_set_class f1_unss1 a_wcel i0_unss1 a_sup_set_class f2_unss1 a_wcel a_wo i0_unss1 a_sup_set_class f0_unss1 f2_unss1 a_cun a_wcel i0_unss1 a_sup_set_class f1_unss1 f2_unss1 a_cun a_wcel p_3imtr4g f0_unss1 f1_unss1 a_wss i0_unss1 f0_unss1 f2_unss1 a_cun f1_unss1 f2_unss1 a_cun p_ssrdv $.
$}

$(A relationship between subclass and union.  Theorem 26 of [Suppes]
       p. 27.  (Contributed by NM, 30-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_ssequn1 $f class A $.
	f1_ssequn1 $f class B $.
	i0_ssequn1 $f set x $.
	p_ssequn1 $p |- ( A C_ B <-> ( A u. B ) = B ) $= i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wo p_bicom i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel p_pm4.72 i0_ssequn1 a_sup_set_class f0_ssequn1 f1_ssequn1 p_elun i0_ssequn1 a_sup_set_class f0_ssequn1 f1_ssequn1 a_cun a_wcel i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wo i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel p_bibi1i i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wo a_wb i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wo i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wb i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wi i0_ssequn1 a_sup_set_class f0_ssequn1 f1_ssequn1 a_cun a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wb p_3bitr4i i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wi i0_ssequn1 a_sup_set_class f0_ssequn1 f1_ssequn1 a_cun a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wb i0_ssequn1 p_albii i0_ssequn1 f0_ssequn1 f1_ssequn1 p_dfss2 i0_ssequn1 f0_ssequn1 f1_ssequn1 a_cun f1_ssequn1 p_dfcleq i0_ssequn1 a_sup_set_class f0_ssequn1 a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wi i0_ssequn1 a_wal i0_ssequn1 a_sup_set_class f0_ssequn1 f1_ssequn1 a_cun a_wcel i0_ssequn1 a_sup_set_class f1_ssequn1 a_wcel a_wb i0_ssequn1 a_wal f0_ssequn1 f1_ssequn1 a_wss f0_ssequn1 f1_ssequn1 a_cun f1_ssequn1 a_wceq p_3bitr4i $.
$}

$(Subclass law for union of classes.  Exercise 7 of [TakeutiZaring] p. 18.
     (Contributed by NM, 14-Oct-1999.) $)

${
	$v A B C  $.
	f0_unss2 $f class A $.
	f1_unss2 $f class B $.
	f2_unss2 $f class C $.
	p_unss2 $p |- ( A C_ B -> ( C u. A ) C_ ( C u. B ) ) $= f0_unss2 f1_unss2 f2_unss2 p_unss1 f2_unss2 f0_unss2 p_uncom f2_unss2 f1_unss2 p_uncom f0_unss2 f1_unss2 a_wss f0_unss2 f2_unss2 a_cun f1_unss2 f2_unss2 a_cun f2_unss2 f0_unss2 a_cun f2_unss2 f1_unss2 a_cun p_3sstr4g $.
$}

$(Subclass law for union of classes.  (Contributed by NM, 2-Jun-2004.) $)

${
	$v A B C D  $.
	f0_unss12 $f class A $.
	f1_unss12 $f class B $.
	f2_unss12 $f class C $.
	f3_unss12 $f class D $.
	p_unss12 $p |- ( ( A C_ B /\ C C_ D ) -> ( A u. C ) C_ ( B u. D ) ) $= f0_unss12 f1_unss12 f2_unss12 p_unss1 f2_unss12 f3_unss12 f1_unss12 p_unss2 f0_unss12 f1_unss12 a_wss f2_unss12 f3_unss12 a_wss f0_unss12 f2_unss12 a_cun f1_unss12 f2_unss12 a_cun f1_unss12 f3_unss12 a_cun p_sylan9ss $.
$}

$(A relationship between subclass and union.  (Contributed by NM,
     13-Jun-1994.) $)

${
	$v A B  $.
	f0_ssequn2 $f class A $.
	f1_ssequn2 $f class B $.
	p_ssequn2 $p |- ( A C_ B <-> ( B u. A ) = B ) $= f0_ssequn2 f1_ssequn2 p_ssequn1 f0_ssequn2 f1_ssequn2 p_uncom f0_ssequn2 f1_ssequn2 a_cun f1_ssequn2 f0_ssequn2 a_cun f1_ssequn2 p_eqeq1i f0_ssequn2 f1_ssequn2 a_wss f0_ssequn2 f1_ssequn2 a_cun f1_ssequn2 a_wceq f1_ssequn2 f0_ssequn2 a_cun f1_ssequn2 a_wceq p_bitri $.
$}

$(The union of two subclasses is a subclass.  Theorem 27 of [Suppes] p. 27
       and its converse.  (Contributed by NM, 11-Jun-2004.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_unss $f class A $.
	f1_unss $f class B $.
	f2_unss $f class C $.
	i0_unss $f set x $.
	p_unss $p |- ( ( A C_ C /\ B C_ C ) <-> ( A u. B ) C_ C ) $= i0_unss f0_unss f1_unss a_cun f2_unss p_dfss2 i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss p_19.26 i0_unss a_sup_set_class f0_unss f1_unss p_elun i0_unss a_sup_set_class f0_unss f1_unss a_cun a_wcel i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f1_unss a_wcel a_wo i0_unss a_sup_set_class f2_unss a_wcel p_imbi1i i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel i0_unss a_sup_set_class f1_unss a_wcel p_jaob i0_unss a_sup_set_class f0_unss f1_unss a_cun a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f1_unss a_wcel a_wo i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi a_wa p_bitri i0_unss a_sup_set_class f0_unss f1_unss a_cun a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi a_wa i0_unss p_albii i0_unss f0_unss f2_unss p_dfss2 i0_unss f1_unss f2_unss p_dfss2 f0_unss f2_unss a_wss i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal f1_unss f2_unss a_wss i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal p_anbi12i i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi a_wa i0_unss a_wal i0_unss a_sup_set_class f0_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal i0_unss a_sup_set_class f1_unss a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal a_wa i0_unss a_sup_set_class f0_unss f1_unss a_cun a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal f0_unss f2_unss a_wss f1_unss f2_unss a_wss a_wa p_3bitr4i f0_unss f1_unss a_cun f2_unss a_wss i0_unss a_sup_set_class f0_unss f1_unss a_cun a_wcel i0_unss a_sup_set_class f2_unss a_wcel a_wi i0_unss a_wal f0_unss f2_unss a_wss f1_unss f2_unss a_wss a_wa p_bitr2i $.
$}

$(An inference showing the union of two subclasses is a subclass.
       (Contributed by Raph Levien, 10-Dec-2002.) $)

${
	$v A B C  $.
	f0_unssi $f class A $.
	f1_unssi $f class B $.
	f2_unssi $f class C $.
	e0_unssi $e |- A C_ C $.
	e1_unssi $e |- B C_ C $.
	p_unssi $p |- ( A u. B ) C_ C $= e0_unssi e1_unssi f0_unssi f2_unssi a_wss f1_unssi f2_unssi a_wss p_pm3.2i f0_unssi f1_unssi f2_unssi p_unss f0_unssi f2_unssi a_wss f1_unssi f2_unssi a_wss a_wa f0_unssi f1_unssi a_cun f2_unssi a_wss p_mpbi $.
$}

$(A deduction showing the union of two subclasses is a subclass.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_unssd $f wff ph $.
	f1_unssd $f class A $.
	f2_unssd $f class B $.
	f3_unssd $f class C $.
	e0_unssd $e |- ( ph -> A C_ C ) $.
	e1_unssd $e |- ( ph -> B C_ C ) $.
	p_unssd $p |- ( ph -> ( A u. B ) C_ C ) $= e0_unssd e1_unssd f1_unssd f2_unssd f3_unssd p_unss f1_unssd f3_unssd a_wss f2_unssd f3_unssd a_wss a_wa f1_unssd f2_unssd a_cun f3_unssd a_wss p_biimpi f0_unssd f1_unssd f3_unssd a_wss f2_unssd f3_unssd a_wss f1_unssd f2_unssd a_cun f3_unssd a_wss p_syl2anc $.
$}

$(If ` ( A u. B ) ` is contained in ` C ` , so is ` A ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_unssad $f wff ph $.
	f1_unssad $f class A $.
	f2_unssad $f class B $.
	f3_unssad $f class C $.
	e0_unssad $e |- ( ph -> ( A u. B ) C_ C ) $.
	p_unssad $p |- ( ph -> A C_ C ) $= e0_unssad f1_unssad f2_unssad f3_unssad p_unss f0_unssad f1_unssad f2_unssad a_cun f3_unssad a_wss f1_unssad f3_unssad a_wss f2_unssad f3_unssad a_wss a_wa p_sylibr f0_unssad f1_unssad f3_unssad a_wss f2_unssad f3_unssad a_wss p_simpld $.
$}

$(If ` ( A u. B ) ` is contained in ` C ` , so is ` B ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_unssbd $f wff ph $.
	f1_unssbd $f class A $.
	f2_unssbd $f class B $.
	f3_unssbd $f class C $.
	e0_unssbd $e |- ( ph -> ( A u. B ) C_ C ) $.
	p_unssbd $p |- ( ph -> B C_ C ) $= e0_unssbd f1_unssbd f2_unssbd f3_unssbd p_unss f0_unssbd f1_unssbd f2_unssbd a_cun f3_unssbd a_wss f1_unssbd f3_unssbd a_wss f2_unssbd f3_unssbd a_wss a_wa p_sylibr f0_unssbd f1_unssbd f3_unssbd a_wss f2_unssbd f3_unssbd a_wss p_simprd $.
$}

$(A condition that implies inclusion in the union of two classes.
     (Contributed by NM, 23-Nov-2003.) $)

${
	$v A B C  $.
	f0_ssun $f class A $.
	f1_ssun $f class B $.
	f2_ssun $f class C $.
	p_ssun $p |- ( ( A C_ B \/ A C_ C ) -> A C_ ( B u. C ) ) $= f0_ssun f1_ssun f2_ssun p_ssun3 f0_ssun f2_ssun f1_ssun p_ssun4 f0_ssun f1_ssun a_wss f0_ssun f1_ssun f2_ssun a_cun a_wss f0_ssun f2_ssun a_wss p_jaoi $.
$}

$(Restricted existential quantification over union.  (Contributed by Jeff
     Madsen, 5-Jan-2011.) $)

${
	$v ph x A B  $.
	f0_rexun $f wff ph $.
	f1_rexun $f set x $.
	f2_rexun $f class A $.
	f3_rexun $f class B $.
	p_rexun $p |- ( E. x e. ( A u. B ) ph <-> ( E. x e. A ph \/ E. x e. B ph ) ) $= f0_rexun f1_rexun f2_rexun f3_rexun a_cun a_df-rex f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa f1_rexun p_19.43 f1_rexun a_sup_set_class f2_rexun f3_rexun p_elun f1_rexun a_sup_set_class f2_rexun f3_rexun a_cun a_wcel f1_rexun a_sup_set_class f2_rexun a_wcel f1_rexun a_sup_set_class f3_rexun a_wcel a_wo f0_rexun p_anbi1i f1_rexun a_sup_set_class f2_rexun a_wcel f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun p_andir f1_rexun a_sup_set_class f2_rexun f3_rexun a_cun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f2_rexun a_wcel f1_rexun a_sup_set_class f3_rexun a_wcel a_wo f0_rexun a_wa f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa a_wo p_bitri f1_rexun a_sup_set_class f2_rexun f3_rexun a_cun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa a_wo f1_rexun p_exbii f0_rexun f1_rexun f2_rexun a_df-rex f0_rexun f1_rexun f3_rexun a_df-rex f0_rexun f1_rexun f2_rexun a_wrex f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_wex f0_rexun f1_rexun f3_rexun a_wrex f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa f1_rexun a_wex p_orbi12i f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa a_wo f1_rexun a_wex f1_rexun a_sup_set_class f2_rexun a_wcel f0_rexun a_wa f1_rexun a_wex f1_rexun a_sup_set_class f3_rexun a_wcel f0_rexun a_wa f1_rexun a_wex a_wo f1_rexun a_sup_set_class f2_rexun f3_rexun a_cun a_wcel f0_rexun a_wa f1_rexun a_wex f0_rexun f1_rexun f2_rexun a_wrex f0_rexun f1_rexun f3_rexun a_wrex a_wo p_3bitr4i f0_rexun f1_rexun f2_rexun f3_rexun a_cun a_wrex f1_rexun a_sup_set_class f2_rexun f3_rexun a_cun a_wcel f0_rexun a_wa f1_rexun a_wex f0_rexun f1_rexun f2_rexun a_wrex f0_rexun f1_rexun f3_rexun a_wrex a_wo p_bitri $.
$}

$(Restricted quantification over a union.  (Contributed by Scott Fenton,
     12-Apr-2011.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v ph x A B  $.
	f0_ralunb $f wff ph $.
	f1_ralunb $f set x $.
	f2_ralunb $f class A $.
	f3_ralunb $f class B $.
	p_ralunb $p |- ( A. x e. ( A u. B ) ph <-> ( A. x e. A ph /\ A. x e. B ph ) ) $= f1_ralunb a_sup_set_class f2_ralunb f3_ralunb p_elun f1_ralunb a_sup_set_class f2_ralunb f3_ralunb a_cun a_wcel f1_ralunb a_sup_set_class f2_ralunb a_wcel f1_ralunb a_sup_set_class f3_ralunb a_wcel a_wo f0_ralunb p_imbi1i f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb f1_ralunb a_sup_set_class f3_ralunb a_wcel p_jaob f1_ralunb a_sup_set_class f2_ralunb f3_ralunb a_cun a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f2_ralunb a_wcel f1_ralunb a_sup_set_class f3_ralunb a_wcel a_wo f0_ralunb a_wi f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi a_wa p_bitri f1_ralunb a_sup_set_class f2_ralunb f3_ralunb a_cun a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi a_wa f1_ralunb p_albii f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi f1_ralunb p_19.26 f1_ralunb a_sup_set_class f2_ralunb f3_ralunb a_cun a_wcel f0_ralunb a_wi f1_ralunb a_wal f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi a_wa f1_ralunb a_wal f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal a_wa p_bitri f0_ralunb f1_ralunb f2_ralunb f3_ralunb a_cun a_df-ral f0_ralunb f1_ralunb f2_ralunb a_df-ral f0_ralunb f1_ralunb f3_ralunb a_df-ral f0_ralunb f1_ralunb f2_ralunb a_wral f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal f0_ralunb f1_ralunb f3_ralunb a_wral f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal p_anbi12i f1_ralunb a_sup_set_class f2_ralunb f3_ralunb a_cun a_wcel f0_ralunb a_wi f1_ralunb a_wal f1_ralunb a_sup_set_class f2_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal f1_ralunb a_sup_set_class f3_ralunb a_wcel f0_ralunb a_wi f1_ralunb a_wal a_wa f0_ralunb f1_ralunb f2_ralunb f3_ralunb a_cun a_wral f0_ralunb f1_ralunb f2_ralunb a_wral f0_ralunb f1_ralunb f3_ralunb a_wral a_wa p_3bitr4i $.
$}

$(Restricted quantification over union.  (Contributed by Jeff Madsen,
     2-Sep-2009.) $)

${
	$v ph x A B  $.
	f0_ralun $f wff ph $.
	f1_ralun $f set x $.
	f2_ralun $f class A $.
	f3_ralun $f class B $.
	p_ralun $p |- ( ( A. x e. A ph /\ A. x e. B ph ) -> A. x e. ( A u. B ) ph ) $= f0_ralun f1_ralun f2_ralun f3_ralun p_ralunb f0_ralun f1_ralun f2_ralun f3_ralun a_cun a_wral f0_ralun f1_ralun f2_ralun a_wral f0_ralun f1_ralun f3_ralun a_wral a_wa p_biimpri $.
$}

$(Expansion of membership in an intersection of two classes.  Theorem 12
       of [Suppes] p. 25.  (Contributed by NM, 29-Apr-1994.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elin $f class A $.
	f1_elin $f class B $.
	f2_elin $f class C $.
	i0_elin $f set x $.
	p_elin $p |- ( A e. ( B i^i C ) <-> ( A e. B /\ A e. C ) ) $= f0_elin f1_elin f2_elin a_cin p_elex f0_elin f2_elin p_elex f0_elin f2_elin a_wcel f0_elin a_cvv a_wcel f0_elin f1_elin a_wcel p_adantl i0_elin a_sup_set_class f0_elin f1_elin p_eleq1 i0_elin a_sup_set_class f0_elin f2_elin p_eleq1 i0_elin a_sup_set_class f0_elin a_wceq i0_elin a_sup_set_class f1_elin a_wcel f0_elin f1_elin a_wcel i0_elin a_sup_set_class f2_elin a_wcel f0_elin f2_elin a_wcel p_anbi12d i0_elin f1_elin f2_elin a_df-in i0_elin a_sup_set_class f1_elin a_wcel i0_elin a_sup_set_class f2_elin a_wcel a_wa f0_elin f1_elin a_wcel f0_elin f2_elin a_wcel a_wa i0_elin f0_elin f1_elin f2_elin a_cin a_cvv p_elab2g f0_elin f1_elin f2_elin a_cin a_wcel f0_elin a_cvv a_wcel f0_elin f1_elin a_wcel f0_elin f2_elin a_wcel a_wa p_pm5.21nii $.
$}

$(Membership in a class defined as an intersection.  (Contributed by
       Stefan O'Rear, 29-Mar-2015.) $)

${
	$v A B C X  $.
	f0_elin2 $f class A $.
	f1_elin2 $f class B $.
	f2_elin2 $f class C $.
	f3_elin2 $f class X $.
	e0_elin2 $e |- X = ( B i^i C ) $.
	p_elin2 $p |- ( A e. X <-> ( A e. B /\ A e. C ) ) $= e0_elin2 f3_elin2 f1_elin2 f2_elin2 a_cin f0_elin2 p_eleq2i f0_elin2 f1_elin2 f2_elin2 p_elin f0_elin2 f3_elin2 a_wcel f0_elin2 f1_elin2 f2_elin2 a_cin a_wcel f0_elin2 f1_elin2 a_wcel f0_elin2 f2_elin2 a_wcel a_wa p_bitri $.
$}

$(Membership in a class defined as a ternary intersection.  (Contributed
       by Stefan O'Rear, 29-Mar-2015.) $)

${
	$v A B C D X  $.
	f0_elin3 $f class A $.
	f1_elin3 $f class B $.
	f2_elin3 $f class C $.
	f3_elin3 $f class D $.
	f4_elin3 $f class X $.
	e0_elin3 $e |- X = ( ( B i^i C ) i^i D ) $.
	p_elin3 $p |- ( A e. X <-> ( A e. B /\ A e. C /\ A e. D ) ) $= f0_elin3 f1_elin3 f2_elin3 p_elin f0_elin3 f1_elin3 f2_elin3 a_cin a_wcel f0_elin3 f1_elin3 a_wcel f0_elin3 f2_elin3 a_wcel a_wa f0_elin3 f3_elin3 a_wcel p_anbi1i e0_elin3 f0_elin3 f1_elin3 f2_elin3 a_cin f3_elin3 f4_elin3 p_elin2 f0_elin3 f1_elin3 a_wcel f0_elin3 f2_elin3 a_wcel f0_elin3 f3_elin3 a_wcel a_df-3an f0_elin3 f1_elin3 f2_elin3 a_cin a_wcel f0_elin3 f3_elin3 a_wcel a_wa f0_elin3 f1_elin3 a_wcel f0_elin3 f2_elin3 a_wcel a_wa f0_elin3 f3_elin3 a_wcel a_wa f0_elin3 f4_elin3 a_wcel f0_elin3 f1_elin3 a_wcel f0_elin3 f2_elin3 a_wcel f0_elin3 f3_elin3 a_wcel a_w3a p_3bitr4i $.
$}

$(Commutative law for intersection of classes.  Exercise 7 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_incom $f class A $.
	f1_incom $f class B $.
	i0_incom $f set x $.
	p_incom $p |- ( A i^i B ) = ( B i^i A ) $= i0_incom a_sup_set_class f0_incom a_wcel i0_incom a_sup_set_class f1_incom a_wcel p_ancom i0_incom a_sup_set_class f0_incom f1_incom p_elin i0_incom a_sup_set_class f1_incom f0_incom p_elin i0_incom a_sup_set_class f0_incom a_wcel i0_incom a_sup_set_class f1_incom a_wcel a_wa i0_incom a_sup_set_class f1_incom a_wcel i0_incom a_sup_set_class f0_incom a_wcel a_wa i0_incom a_sup_set_class f0_incom f1_incom a_cin a_wcel i0_incom a_sup_set_class f1_incom f0_incom a_cin a_wcel p_3bitr4i i0_incom f0_incom f1_incom a_cin f1_incom f0_incom a_cin p_eqriv $.
$}

$(Inference from membership to intersection.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ineqri $f set x $.
	f1_ineqri $f class A $.
	f2_ineqri $f class B $.
	f3_ineqri $f class C $.
	e0_ineqri $e |- ( ( x e. A /\ x e. B ) <-> x e. C ) $.
	p_ineqri $p |- ( A i^i B ) = C $= f0_ineqri a_sup_set_class f1_ineqri f2_ineqri p_elin e0_ineqri f0_ineqri a_sup_set_class f1_ineqri f2_ineqri a_cin a_wcel f0_ineqri a_sup_set_class f1_ineqri a_wcel f0_ineqri a_sup_set_class f2_ineqri a_wcel a_wa f0_ineqri a_sup_set_class f3_ineqri a_wcel p_bitri f0_ineqri f1_ineqri f2_ineqri a_cin f3_ineqri p_eqriv $.
$}

$(Equality theorem for intersection of two classes.  (Contributed by NM,
       14-Dec-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ineq1 $f class A $.
	f1_ineq1 $f class B $.
	f2_ineq1 $f class C $.
	i0_ineq1 $f set x $.
	p_ineq1 $p |- ( A = B -> ( A i^i C ) = ( B i^i C ) ) $= f0_ineq1 f1_ineq1 i0_ineq1 a_sup_set_class p_eleq2 f0_ineq1 f1_ineq1 a_wceq i0_ineq1 a_sup_set_class f0_ineq1 a_wcel i0_ineq1 a_sup_set_class f1_ineq1 a_wcel i0_ineq1 a_sup_set_class f2_ineq1 a_wcel p_anbi1d i0_ineq1 a_sup_set_class f0_ineq1 f2_ineq1 p_elin i0_ineq1 a_sup_set_class f1_ineq1 f2_ineq1 p_elin f0_ineq1 f1_ineq1 a_wceq i0_ineq1 a_sup_set_class f0_ineq1 a_wcel i0_ineq1 a_sup_set_class f2_ineq1 a_wcel a_wa i0_ineq1 a_sup_set_class f1_ineq1 a_wcel i0_ineq1 a_sup_set_class f2_ineq1 a_wcel a_wa i0_ineq1 a_sup_set_class f0_ineq1 f2_ineq1 a_cin a_wcel i0_ineq1 a_sup_set_class f1_ineq1 f2_ineq1 a_cin a_wcel p_3bitr4g f0_ineq1 f1_ineq1 a_wceq i0_ineq1 f0_ineq1 f2_ineq1 a_cin f1_ineq1 f2_ineq1 a_cin p_eqrdv $.
$}

$(Equality theorem for intersection of two classes.  (Contributed by NM,
     26-Dec-1993.) $)

${
	$v A B C  $.
	f0_ineq2 $f class A $.
	f1_ineq2 $f class B $.
	f2_ineq2 $f class C $.
	p_ineq2 $p |- ( A = B -> ( C i^i A ) = ( C i^i B ) ) $= f0_ineq2 f1_ineq2 f2_ineq2 p_ineq1 f2_ineq2 f0_ineq2 p_incom f2_ineq2 f1_ineq2 p_incom f0_ineq2 f1_ineq2 a_wceq f0_ineq2 f2_ineq2 a_cin f1_ineq2 f2_ineq2 a_cin f2_ineq2 f0_ineq2 a_cin f2_ineq2 f1_ineq2 a_cin p_3eqtr4g $.
$}

$(Equality theorem for intersection of two classes.  (Contributed by NM,
     8-May-1994.) $)

${
	$v A B C D  $.
	f0_ineq12 $f class A $.
	f1_ineq12 $f class B $.
	f2_ineq12 $f class C $.
	f3_ineq12 $f class D $.
	p_ineq12 $p |- ( ( A = B /\ C = D ) -> ( A i^i C ) = ( B i^i D ) ) $= f0_ineq12 f1_ineq12 f2_ineq12 p_ineq1 f2_ineq12 f3_ineq12 f1_ineq12 p_ineq2 f0_ineq12 f1_ineq12 a_wceq f2_ineq12 f3_ineq12 a_wceq f0_ineq12 f2_ineq12 a_cin f1_ineq12 f2_ineq12 a_cin f1_ineq12 f3_ineq12 a_cin p_sylan9eq $.
$}

$(Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)

${
	$v A B C  $.
	f0_ineq1i $f class A $.
	f1_ineq1i $f class B $.
	f2_ineq1i $f class C $.
	e0_ineq1i $e |- A = B $.
	p_ineq1i $p |- ( A i^i C ) = ( B i^i C ) $= e0_ineq1i f0_ineq1i f1_ineq1i f2_ineq1i p_ineq1 f0_ineq1i f1_ineq1i a_wceq f0_ineq1i f2_ineq1i a_cin f1_ineq1i f2_ineq1i a_cin a_wceq a_ax-mp $.
$}

$(Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)

${
	$v A B C  $.
	f0_ineq2i $f class A $.
	f1_ineq2i $f class B $.
	f2_ineq2i $f class C $.
	e0_ineq2i $e |- A = B $.
	p_ineq2i $p |- ( C i^i A ) = ( C i^i B ) $= e0_ineq2i f0_ineq2i f1_ineq2i f2_ineq2i p_ineq2 f0_ineq2i f1_ineq2i a_wceq f2_ineq2i f0_ineq2i a_cin f2_ineq2i f1_ineq2i a_cin a_wceq a_ax-mp $.
$}

$(Equality inference for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)

${
	$v A B C D  $.
	f0_ineq12i $f class A $.
	f1_ineq12i $f class B $.
	f2_ineq12i $f class C $.
	f3_ineq12i $f class D $.
	e0_ineq12i $e |- A = B $.
	e1_ineq12i $e |- C = D $.
	p_ineq12i $p |- ( A i^i C ) = ( B i^i D ) $= e0_ineq12i e1_ineq12i f0_ineq12i f1_ineq12i f2_ineq12i f3_ineq12i p_ineq12 f0_ineq12i f1_ineq12i a_wceq f2_ineq12i f3_ineq12i a_wceq f0_ineq12i f2_ineq12i a_cin f1_ineq12i f3_ineq12i a_cin a_wceq p_mp2an $.
$}

$(Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)

${
	$v ph A B C  $.
	f0_ineq1d $f wff ph $.
	f1_ineq1d $f class A $.
	f2_ineq1d $f class B $.
	f3_ineq1d $f class C $.
	e0_ineq1d $e |- ( ph -> A = B ) $.
	p_ineq1d $p |- ( ph -> ( A i^i C ) = ( B i^i C ) ) $= e0_ineq1d f1_ineq1d f2_ineq1d f3_ineq1d p_ineq1 f0_ineq1d f1_ineq1d f2_ineq1d a_wceq f1_ineq1d f3_ineq1d a_cin f2_ineq1d f3_ineq1d a_cin a_wceq p_syl $.
$}

$(Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)

${
	$v ph A B C  $.
	f0_ineq2d $f wff ph $.
	f1_ineq2d $f class A $.
	f2_ineq2d $f class B $.
	f3_ineq2d $f class C $.
	e0_ineq2d $e |- ( ph -> A = B ) $.
	p_ineq2d $p |- ( ph -> ( C i^i A ) = ( C i^i B ) ) $= e0_ineq2d f1_ineq2d f2_ineq2d f3_ineq2d p_ineq2 f0_ineq2d f1_ineq2d f2_ineq2d a_wceq f3_ineq2d f1_ineq2d a_cin f3_ineq2d f2_ineq2d a_cin a_wceq p_syl $.
$}

$(Equality deduction for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph A B C D  $.
	f0_ineq12d $f wff ph $.
	f1_ineq12d $f class A $.
	f2_ineq12d $f class B $.
	f3_ineq12d $f class C $.
	f4_ineq12d $f class D $.
	e0_ineq12d $e |- ( ph -> A = B ) $.
	e1_ineq12d $e |- ( ph -> C = D ) $.
	p_ineq12d $p |- ( ph -> ( A i^i C ) = ( B i^i D ) ) $= e0_ineq12d e1_ineq12d f1_ineq12d f2_ineq12d f3_ineq12d f4_ineq12d p_ineq12 f0_ineq12d f1_ineq12d f2_ineq12d a_wceq f3_ineq12d f4_ineq12d a_wceq f1_ineq12d f3_ineq12d a_cin f2_ineq12d f4_ineq12d a_cin a_wceq p_syl2anc $.
$}

$(Equality deduction for intersection of two classes.  (Contributed by
         NM, 7-Feb-2007.) $)

${
	$v ph ps A B C D  $.
	f0_ineqan12d $f wff ph $.
	f1_ineqan12d $f wff ps $.
	f2_ineqan12d $f class A $.
	f3_ineqan12d $f class B $.
	f4_ineqan12d $f class C $.
	f5_ineqan12d $f class D $.
	e0_ineqan12d $e |- ( ph -> A = B ) $.
	e1_ineqan12d $e |- ( ps -> C = D ) $.
	p_ineqan12d $p |- ( ( ph /\ ps ) -> ( A i^i C ) = ( B i^i D ) ) $= e0_ineqan12d e1_ineqan12d f2_ineqan12d f3_ineqan12d f4_ineqan12d f5_ineqan12d p_ineq12 f0_ineqan12d f2_ineqan12d f3_ineqan12d a_wceq f4_ineqan12d f5_ineqan12d a_wceq f2_ineqan12d f4_ineqan12d a_cin f3_ineqan12d f5_ineqan12d a_cin a_wceq f1_ineqan12d p_syl2an $.
$}

$(A frequently-used variant of subclass definition ~ df-ss .  (Contributed
     by NM, 10-Jan-2015.) $)

${
	$v A B  $.
	f0_dfss1 $f class A $.
	f1_dfss1 $f class B $.
	p_dfss1 $p |- ( A C_ B <-> ( B i^i A ) = A ) $= f0_dfss1 f1_dfss1 a_df-ss f0_dfss1 f1_dfss1 p_incom f0_dfss1 f1_dfss1 a_cin f1_dfss1 f0_dfss1 a_cin f0_dfss1 p_eqeq1i f0_dfss1 f1_dfss1 a_wss f0_dfss1 f1_dfss1 a_cin f0_dfss1 a_wceq f1_dfss1 f0_dfss1 a_cin f0_dfss1 a_wceq p_bitri $.
$}

$(Another definition of subclasshood.  Similar to ~ df-ss , ~ dfss , and
     ~ dfss1 .  (Contributed by David Moews, 1-May-2017.) $)

${
	$v A B  $.
	f0_dfss5 $f class A $.
	f1_dfss5 $f class B $.
	p_dfss5 $p |- ( A C_ B <-> A = ( B i^i A ) ) $= f0_dfss5 f1_dfss5 p_dfss1 f1_dfss5 f0_dfss5 a_cin f0_dfss5 p_eqcom f0_dfss5 f1_dfss5 a_wss f1_dfss5 f0_dfss5 a_cin f0_dfss5 a_wceq f0_dfss5 f1_dfss5 f0_dfss5 a_cin a_wceq p_bitri $.
$}

$(Bound-variable hypothesis builder for the intersection of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v x A B  $.
	$d x y  $.
	$d y A  $.
	$d y B  $.
	f0_nfin $f set x $.
	f1_nfin $f class A $.
	f2_nfin $f class B $.
	i0_nfin $f set y $.
	e0_nfin $e |- F/_ x A $.
	e1_nfin $e |- F/_ x B $.
	p_nfin $p |- F/_ x ( A i^i B ) $= i0_nfin f1_nfin f2_nfin p_dfin5 e1_nfin f0_nfin i0_nfin f2_nfin p_nfcri e0_nfin i0_nfin a_sup_set_class f2_nfin a_wcel f0_nfin i0_nfin f1_nfin p_nfrab f0_nfin f1_nfin f2_nfin a_cin i0_nfin a_sup_set_class f2_nfin a_wcel i0_nfin f1_nfin a_crab p_nfcxfr $.
$}

$(Distribute proper substitution through an intersection relation.
       (Contributed by Alan Sare, 22-Jul-2012.) $)

${
	$v x A B C D  $.
	$d A y  $.
	$d C y  $.
	$d D y  $.
	$d x y  $.
	f0_csbing $f set x $.
	f1_csbing $f class A $.
	f2_csbing $f class B $.
	f3_csbing $f class C $.
	f4_csbing $f class D $.
	i0_csbing $f set y $.
	p_csbing $p |- ( A e. B -> [_ A / x ]_ ( C i^i D ) = ( [_ A / x ]_ C i^i [_ A / x ]_ D ) ) $= f0_csbing i0_csbing a_sup_set_class f1_csbing f3_csbing f4_csbing a_cin p_csbeq1 f0_csbing i0_csbing a_sup_set_class f1_csbing f3_csbing p_csbeq1 f0_csbing i0_csbing a_sup_set_class f1_csbing f4_csbing p_csbeq1 i0_csbing a_sup_set_class f1_csbing a_wceq f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f0_csbing f1_csbing f3_csbing a_csb f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb f0_csbing f1_csbing f4_csbing a_csb p_ineq12d i0_csbing a_sup_set_class f1_csbing a_wceq f0_csbing i0_csbing a_sup_set_class f3_csbing f4_csbing a_cin a_csb f0_csbing f1_csbing f3_csbing f4_csbing a_cin a_csb f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb a_cin f0_csbing f1_csbing f3_csbing a_csb f0_csbing f1_csbing f4_csbing a_csb a_cin p_eqeq12d i0_csbing p_vex f0_csbing i0_csbing a_sup_set_class f3_csbing p_nfcsb1v f0_csbing i0_csbing a_sup_set_class f4_csbing p_nfcsb1v f0_csbing f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb p_nfin f0_csbing i0_csbing a_sup_set_class f3_csbing p_csbeq1a f0_csbing i0_csbing a_sup_set_class f4_csbing p_csbeq1a f0_csbing a_sup_set_class i0_csbing a_sup_set_class a_wceq f3_csbing f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f4_csbing f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb p_ineq12d f0_csbing i0_csbing a_sup_set_class f3_csbing f4_csbing a_cin f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb a_cin p_csbief f0_csbing i0_csbing a_sup_set_class f3_csbing f4_csbing a_cin a_csb f0_csbing i0_csbing a_sup_set_class f3_csbing a_csb f0_csbing i0_csbing a_sup_set_class f4_csbing a_csb a_cin a_wceq f0_csbing f1_csbing f3_csbing f4_csbing a_cin a_csb f0_csbing f1_csbing f3_csbing a_csb f0_csbing f1_csbing f4_csbing a_csb a_cin a_wceq i0_csbing f1_csbing f2_csbing p_vtoclg $.
$}

$(Deduction from a wff to a restricted class abstraction.  (Contributed by
       NM, 14-Jan-2014.) $)

${
	$v ph ps x A B  $.
	$d x ph  $.
	$d x A  $.
	$d x B  $.
	f0_rabbi2dva $f wff ph $.
	f1_rabbi2dva $f wff ps $.
	f2_rabbi2dva $f set x $.
	f3_rabbi2dva $f class A $.
	f4_rabbi2dva $f class B $.
	e0_rabbi2dva $e |- ( ( ph /\ x e. A ) -> ( x e. B <-> ps ) ) $.
	p_rabbi2dva $p |- ( ph -> ( A i^i B ) = { x e. A | ps } ) $= f2_rabbi2dva f3_rabbi2dva f4_rabbi2dva p_dfin5 e0_rabbi2dva f0_rabbi2dva f2_rabbi2dva a_sup_set_class f4_rabbi2dva a_wcel f1_rabbi2dva f2_rabbi2dva f3_rabbi2dva p_rabbidva f0_rabbi2dva f3_rabbi2dva f4_rabbi2dva a_cin f2_rabbi2dva a_sup_set_class f4_rabbi2dva a_wcel f2_rabbi2dva f3_rabbi2dva a_crab f1_rabbi2dva f2_rabbi2dva f3_rabbi2dva a_crab p_syl5eq $.
$}

$(Idempotent law for intersection of classes.  Theorem 15 of [Suppes]
       p. 26.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_inidm $f class A $.
	i0_inidm $f set x $.
	p_inidm $p |- ( A i^i A ) = A $= i0_inidm a_sup_set_class f0_inidm a_wcel p_anidm i0_inidm f0_inidm f0_inidm f0_inidm p_ineqri $.
$}

$(Associative law for intersection of classes.  Exercise 9 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 3-May-1994.) $)

${
	$v A B C  $.
	$d A x  $.
	$d B x  $.
	$d C x  $.
	f0_inass $f class A $.
	f1_inass $f class B $.
	f2_inass $f class C $.
	i0_inass $f set x $.
	p_inass $p |- ( ( A i^i B ) i^i C ) = ( A i^i ( B i^i C ) ) $= i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass a_wcel i0_inass a_sup_set_class f2_inass a_wcel p_anass i0_inass a_sup_set_class f1_inass f2_inass p_elin i0_inass a_sup_set_class f1_inass f2_inass a_cin a_wcel i0_inass a_sup_set_class f1_inass a_wcel i0_inass a_sup_set_class f2_inass a_wcel a_wa i0_inass a_sup_set_class f0_inass a_wcel p_anbi2i i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass a_wcel a_wa i0_inass a_sup_set_class f2_inass a_wcel a_wa i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass a_wcel i0_inass a_sup_set_class f2_inass a_wcel a_wa a_wa i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass f2_inass a_cin a_wcel a_wa p_bitr4i i0_inass a_sup_set_class f0_inass f1_inass p_elin i0_inass a_sup_set_class f0_inass f1_inass a_cin a_wcel i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass a_wcel a_wa i0_inass a_sup_set_class f2_inass a_wcel p_anbi1i i0_inass a_sup_set_class f0_inass f1_inass f2_inass a_cin p_elin i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass a_wcel a_wa i0_inass a_sup_set_class f2_inass a_wcel a_wa i0_inass a_sup_set_class f0_inass a_wcel i0_inass a_sup_set_class f1_inass f2_inass a_cin a_wcel a_wa i0_inass a_sup_set_class f0_inass f1_inass a_cin a_wcel i0_inass a_sup_set_class f2_inass a_wcel a_wa i0_inass a_sup_set_class f0_inass f1_inass f2_inass a_cin a_cin a_wcel p_3bitr4i i0_inass f0_inass f1_inass a_cin f2_inass f0_inass f1_inass f2_inass a_cin a_cin p_ineqri $.
$}

$(A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.) $)

${
	$v A B C  $.
	f0_in12 $f class A $.
	f1_in12 $f class B $.
	f2_in12 $f class C $.
	p_in12 $p |- ( A i^i ( B i^i C ) ) = ( B i^i ( A i^i C ) ) $= f0_in12 f1_in12 p_incom f0_in12 f1_in12 a_cin f1_in12 f0_in12 a_cin f2_in12 p_ineq1i f0_in12 f1_in12 f2_in12 p_inass f1_in12 f0_in12 f2_in12 p_inass f0_in12 f1_in12 a_cin f2_in12 a_cin f1_in12 f0_in12 a_cin f2_in12 a_cin f0_in12 f1_in12 f2_in12 a_cin a_cin f1_in12 f0_in12 f2_in12 a_cin a_cin p_3eqtr3i $.
$}

$(A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	f0_in32 $f class A $.
	f1_in32 $f class B $.
	f2_in32 $f class C $.
	p_in32 $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i B ) $= f0_in32 f1_in32 f2_in32 p_inass f0_in32 f1_in32 f2_in32 p_in12 f1_in32 f0_in32 f2_in32 a_cin p_incom f0_in32 f1_in32 a_cin f2_in32 a_cin f0_in32 f1_in32 f2_in32 a_cin a_cin f1_in32 f0_in32 f2_in32 a_cin a_cin f0_in32 f2_in32 a_cin f1_in32 a_cin p_3eqtri $.
$}

$(A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)

${
	$v A B C  $.
	f0_in13 $f class A $.
	f1_in13 $f class B $.
	f2_in13 $f class C $.
	p_in13 $p |- ( A i^i ( B i^i C ) ) = ( C i^i ( B i^i A ) ) $= f1_in13 f2_in13 f0_in13 p_in32 f0_in13 f1_in13 f2_in13 a_cin p_incom f2_in13 f1_in13 f0_in13 a_cin p_incom f1_in13 f2_in13 a_cin f0_in13 a_cin f1_in13 f0_in13 a_cin f2_in13 a_cin f0_in13 f1_in13 f2_in13 a_cin a_cin f2_in13 f1_in13 f0_in13 a_cin a_cin p_3eqtr4i $.
$}

$(A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)

${
	$v A B C  $.
	f0_in31 $f class A $.
	f1_in31 $f class B $.
	f2_in31 $f class C $.
	p_in31 $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i B ) i^i A ) $= f2_in31 f0_in31 f1_in31 p_in12 f0_in31 f1_in31 a_cin f2_in31 p_incom f2_in31 f1_in31 a_cin f0_in31 p_incom f2_in31 f0_in31 f1_in31 a_cin a_cin f0_in31 f2_in31 f1_in31 a_cin a_cin f0_in31 f1_in31 a_cin f2_in31 a_cin f2_in31 f1_in31 a_cin f0_in31 a_cin p_3eqtr4i $.
$}

$(Rotate the intersection of 3 classes.  (Contributed by NM,
     27-Aug-2012.) $)

${
	$v A B C  $.
	f0_inrot $f class A $.
	f1_inrot $f class B $.
	f2_inrot $f class C $.
	p_inrot $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i A ) i^i B ) $= f0_inrot f1_inrot f2_inrot p_in31 f2_inrot f1_inrot f0_inrot p_in32 f0_inrot f1_inrot a_cin f2_inrot a_cin f2_inrot f1_inrot a_cin f0_inrot a_cin f2_inrot f0_inrot a_cin f1_inrot a_cin p_eqtri $.
$}

$(Rearrangement of intersection of 4 classes.  (Contributed by NM,
     21-Apr-2001.) $)

${
	$v A B C D  $.
	f0_in4 $f class A $.
	f1_in4 $f class B $.
	f2_in4 $f class C $.
	f3_in4 $f class D $.
	p_in4 $p |- ( ( A i^i B ) i^i ( C i^i D ) ) = ( ( A i^i C ) i^i ( B i^i D ) ) $= f1_in4 f2_in4 f3_in4 p_in12 f1_in4 f2_in4 f3_in4 a_cin a_cin f2_in4 f1_in4 f3_in4 a_cin a_cin f0_in4 p_ineq2i f0_in4 f1_in4 f2_in4 f3_in4 a_cin p_inass f0_in4 f2_in4 f1_in4 f3_in4 a_cin p_inass f0_in4 f1_in4 f2_in4 f3_in4 a_cin a_cin a_cin f0_in4 f2_in4 f1_in4 f3_in4 a_cin a_cin a_cin f0_in4 f1_in4 a_cin f2_in4 f3_in4 a_cin a_cin f0_in4 f2_in4 a_cin f1_in4 f3_in4 a_cin a_cin p_3eqtr4i $.
$}

$(Intersection distributes over itself.  (Contributed by NM, 6-May-1994.) $)

${
	$v A B C  $.
	f0_inindi $f class A $.
	f1_inindi $f class B $.
	f2_inindi $f class C $.
	p_inindi $p |- ( A i^i ( B i^i C ) ) = ( ( A i^i B ) i^i ( A i^i C ) ) $= f0_inindi p_inidm f0_inindi f0_inindi a_cin f0_inindi f1_inindi f2_inindi a_cin p_ineq1i f0_inindi f0_inindi f1_inindi f2_inindi p_in4 f0_inindi f0_inindi a_cin f1_inindi f2_inindi a_cin a_cin f0_inindi f1_inindi f2_inindi a_cin a_cin f0_inindi f1_inindi a_cin f0_inindi f2_inindi a_cin a_cin p_eqtr3i $.
$}

$(Intersection distributes over itself.  (Contributed by NM,
     17-Aug-2004.) $)

${
	$v A B C  $.
	f0_inindir $f class A $.
	f1_inindir $f class B $.
	f2_inindir $f class C $.
	p_inindir $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i ( B i^i C ) ) $= f2_inindir p_inidm f2_inindir f2_inindir a_cin f2_inindir f0_inindir f1_inindir a_cin p_ineq2i f0_inindir f1_inindir f2_inindir f2_inindir p_in4 f0_inindir f1_inindir a_cin f2_inindir f2_inindir a_cin a_cin f0_inindir f1_inindir a_cin f2_inindir a_cin f0_inindir f2_inindir a_cin f1_inindir f2_inindir a_cin a_cin p_eqtr3i $.
$}

$(A relationship between subclass and intersection.  Similar to Exercise 9
     of [TakeutiZaring] p. 18.  (Contributed by NM, 17-May-1994.) $)

${
	$v A B  $.
	f0_sseqin2 $f class A $.
	f1_sseqin2 $f class B $.
	p_sseqin2 $p |- ( A C_ B <-> ( B i^i A ) = A ) $= f0_sseqin2 f1_sseqin2 p_dfss1 $.
$}

$(The intersection of two classes is a subset of one of them.  Part of
       Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
       27-Apr-1994.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_inss1 $f class A $.
	f1_inss1 $f class B $.
	i0_inss1 $f set x $.
	p_inss1 $p |- ( A i^i B ) C_ A $= i0_inss1 a_sup_set_class f0_inss1 f1_inss1 p_elin i0_inss1 a_sup_set_class f0_inss1 f1_inss1 a_cin a_wcel i0_inss1 a_sup_set_class f0_inss1 a_wcel i0_inss1 a_sup_set_class f1_inss1 a_wcel p_simplbi i0_inss1 f0_inss1 f1_inss1 a_cin f0_inss1 p_ssriv $.
$}

$(The intersection of two classes is a subset of one of them.  Part of
     Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
     27-Apr-1994.) $)

${
	$v A B  $.
	f0_inss2 $f class A $.
	f1_inss2 $f class B $.
	p_inss2 $p |- ( A i^i B ) C_ B $= f1_inss2 f0_inss2 p_incom f1_inss2 f0_inss2 p_inss1 f0_inss2 f1_inss2 a_cin f1_inss2 f0_inss2 a_cin f1_inss2 p_eqsstr3i $.
$}

$(Subclass of intersection.  Theorem 2.8(vii) of [Monk1] p. 26.
       (Contributed by NM, 15-Jun-2004.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssin $f class A $.
	f1_ssin $f class B $.
	f2_ssin $f class C $.
	i0_ssin $f set x $.
	p_ssin $p |- ( ( A C_ B /\ A C_ C ) <-> A C_ ( B i^i C ) ) $= i0_ssin a_sup_set_class f1_ssin f2_ssin p_elin i0_ssin a_sup_set_class f1_ssin f2_ssin a_cin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wa i0_ssin a_sup_set_class f0_ssin a_wcel p_imbi2i i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin f2_ssin a_cin a_wcel a_wi i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wa a_wi i0_ssin p_albii i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel p_jcab i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wa a_wi i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi a_wa i0_ssin p_albii i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi i0_ssin p_19.26 i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin f2_ssin a_cin a_wcel a_wi i0_ssin a_wal i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wa a_wi i0_ssin a_wal i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi a_wa i0_ssin a_wal i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_wal i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi i0_ssin a_wal a_wa p_3bitrri i0_ssin f0_ssin f1_ssin p_dfss2 i0_ssin f0_ssin f2_ssin p_dfss2 f0_ssin f1_ssin a_wss i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_wal f0_ssin f2_ssin a_wss i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi i0_ssin a_wal p_anbi12i i0_ssin f0_ssin f1_ssin f2_ssin a_cin p_dfss2 i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin a_wcel a_wi i0_ssin a_wal i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f2_ssin a_wcel a_wi i0_ssin a_wal a_wa i0_ssin a_sup_set_class f0_ssin a_wcel i0_ssin a_sup_set_class f1_ssin f2_ssin a_cin a_wcel a_wi i0_ssin a_wal f0_ssin f1_ssin a_wss f0_ssin f2_ssin a_wss a_wa f0_ssin f1_ssin f2_ssin a_cin a_wss p_3bitr4i $.
$}

$(An inference showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by NM, 24-Nov-2003.) $)

${
	$v A B C  $.
	f0_ssini $f class A $.
	f1_ssini $f class B $.
	f2_ssini $f class C $.
	e0_ssini $e |- A C_ B $.
	e1_ssini $e |- A C_ C $.
	p_ssini $p |- A C_ ( B i^i C ) $= e0_ssini e1_ssini f0_ssini f1_ssini a_wss f0_ssini f2_ssini a_wss p_pm3.2i f0_ssini f1_ssini f2_ssini p_ssin f0_ssini f1_ssini a_wss f0_ssini f2_ssini a_wss a_wa f0_ssini f1_ssini f2_ssini a_cin a_wss p_mpbi $.
$}

$(A deduction showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_ssind $f wff ph $.
	f1_ssind $f class A $.
	f2_ssind $f class B $.
	f3_ssind $f class C $.
	e0_ssind $e |- ( ph -> A C_ B ) $.
	e1_ssind $e |- ( ph -> A C_ C ) $.
	p_ssind $p |- ( ph -> A C_ ( B i^i C ) ) $= e0_ssind e1_ssind f1_ssind f2_ssind f3_ssind p_ssin f1_ssind f2_ssind a_wss f1_ssind f3_ssind a_wss a_wa f1_ssind f2_ssind f3_ssind a_cin a_wss p_biimpi f0_ssind f1_ssind f2_ssind a_wss f1_ssind f3_ssind a_wss f1_ssind f2_ssind f3_ssind a_cin a_wss p_syl2anc $.
$}

$(Add right intersection to subclass relation.  (Contributed by NM,
       16-Aug-1994.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssrin $f class A $.
	f1_ssrin $f class B $.
	f2_ssrin $f class C $.
	i0_ssrin $f set x $.
	p_ssrin $p |- ( A C_ B -> ( A i^i C ) C_ ( B i^i C ) ) $= f0_ssrin f1_ssrin i0_ssrin a_sup_set_class p_ssel f0_ssrin f1_ssrin a_wss i0_ssrin a_sup_set_class f0_ssrin a_wcel i0_ssrin a_sup_set_class f1_ssrin a_wcel i0_ssrin a_sup_set_class f2_ssrin a_wcel p_anim1d i0_ssrin a_sup_set_class f0_ssrin f2_ssrin p_elin i0_ssrin a_sup_set_class f1_ssrin f2_ssrin p_elin f0_ssrin f1_ssrin a_wss i0_ssrin a_sup_set_class f0_ssrin a_wcel i0_ssrin a_sup_set_class f2_ssrin a_wcel a_wa i0_ssrin a_sup_set_class f1_ssrin a_wcel i0_ssrin a_sup_set_class f2_ssrin a_wcel a_wa i0_ssrin a_sup_set_class f0_ssrin f2_ssrin a_cin a_wcel i0_ssrin a_sup_set_class f1_ssrin f2_ssrin a_cin a_wcel p_3imtr4g f0_ssrin f1_ssrin a_wss i0_ssrin f0_ssrin f2_ssrin a_cin f1_ssrin f2_ssrin a_cin p_ssrdv $.
$}

$(Add left intersection to subclass relation.  (Contributed by NM,
       19-Oct-1999.) $)

${
	$v A B C  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_sslin $f class A $.
	f1_sslin $f class B $.
	f2_sslin $f class C $.
	p_sslin $p |- ( A C_ B -> ( C i^i A ) C_ ( C i^i B ) ) $= f0_sslin f1_sslin f2_sslin p_ssrin f2_sslin f0_sslin p_incom f2_sslin f1_sslin p_incom f0_sslin f1_sslin a_wss f0_sslin f2_sslin a_cin f1_sslin f2_sslin a_cin f2_sslin f0_sslin a_cin f2_sslin f1_sslin a_cin p_3sstr4g $.
$}

$(Intersection of subclasses.  (Contributed by NM, 5-May-2000.) $)

${
	$v A B C D  $.
	f0_ss2in $f class A $.
	f1_ss2in $f class B $.
	f2_ss2in $f class C $.
	f3_ss2in $f class D $.
	p_ss2in $p |- ( ( A C_ B /\ C C_ D ) -> ( A i^i C ) C_ ( B i^i D ) ) $= f0_ss2in f1_ss2in f2_ss2in p_ssrin f2_ss2in f3_ss2in f1_ss2in p_sslin f0_ss2in f1_ss2in a_wss f2_ss2in f3_ss2in a_wss f0_ss2in f2_ss2in a_cin f1_ss2in f2_ss2in a_cin f1_ss2in f3_ss2in a_cin p_sylan9ss $.
$}

$(Intersection preserves subclass relationship.  (Contributed by NM,
     14-Sep-1999.) $)

${
	$v A B C  $.
	f0_ssinss1 $f class A $.
	f1_ssinss1 $f class B $.
	f2_ssinss1 $f class C $.
	p_ssinss1 $p |- ( A C_ C -> ( A i^i B ) C_ C ) $= f0_ssinss1 f1_ssinss1 p_inss1 f0_ssinss1 f1_ssinss1 a_cin f0_ssinss1 f2_ssinss1 p_sstr2 f0_ssinss1 f1_ssinss1 a_cin f0_ssinss1 a_wss f0_ssinss1 f2_ssinss1 a_wss f0_ssinss1 f1_ssinss1 a_cin f2_ssinss1 a_wss a_wi a_ax-mp $.
$}

$(Inclusion of an intersection of two classes.  (Contributed by NM,
     30-Oct-2014.) $)

${
	$v A B C  $.
	f0_inss $f class A $.
	f1_inss $f class B $.
	f2_inss $f class C $.
	p_inss $p |- ( ( A C_ C \/ B C_ C ) -> ( A i^i B ) C_ C ) $= f0_inss f1_inss f2_inss p_ssinss1 f0_inss f1_inss p_incom f1_inss f0_inss f2_inss p_ssinss1 f1_inss f2_inss a_wss f0_inss f1_inss a_cin f1_inss f0_inss a_cin f2_inss p_syl5eqss f0_inss f2_inss a_wss f0_inss f1_inss a_cin f2_inss a_wss f1_inss f2_inss a_wss p_jaoi $.
$}

$(Absorption law for union.  (Contributed by NM, 16-Apr-2006.) $)

${
	$v A B  $.
	f0_unabs $f class A $.
	f1_unabs $f class B $.
	p_unabs $p |- ( A u. ( A i^i B ) ) = A $= f0_unabs f1_unabs p_inss1 f0_unabs f1_unabs a_cin f0_unabs p_ssequn2 f0_unabs f1_unabs a_cin f0_unabs a_wss f0_unabs f0_unabs f1_unabs a_cin a_cun f0_unabs a_wceq p_mpbi $.
$}

$(Absorption law for intersection.  (Contributed by NM, 16-Apr-2006.) $)

${
	$v A B  $.
	f0_inabs $f class A $.
	f1_inabs $f class B $.
	p_inabs $p |- ( A i^i ( A u. B ) ) = A $= f0_inabs f1_inabs p_ssun1 f0_inabs f0_inabs f1_inabs a_cun a_df-ss f0_inabs f0_inabs f1_inabs a_cun a_wss f0_inabs f0_inabs f1_inabs a_cun a_cin f0_inabs a_wceq p_mpbi $.
$}

$(Negation of subclass expressed in terms of intersection and proper
     subclass.  (Contributed by NM, 30-Jun-2004.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_nssinpss $f class A $.
	f1_nssinpss $f class B $.
	p_nssinpss $p |- ( -. A C_ B <-> ( A i^i B ) C. A ) $= f0_nssinpss f1_nssinpss p_inss1 f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wss f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wne p_biantrur f0_nssinpss f1_nssinpss a_df-ss f0_nssinpss f1_nssinpss a_wss f0_nssinpss f1_nssinpss a_cin f0_nssinpss p_necon3bbii f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_df-pss f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wne f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wss f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wne a_wa f0_nssinpss f1_nssinpss a_wss a_wn f0_nssinpss f1_nssinpss a_cin f0_nssinpss a_wpss p_3bitr4i $.
$}

$(Negation of subclass expressed in terms of proper subclass and union.
     (Contributed by NM, 15-Sep-2004.) $)

${
	$v A B  $.
	f0_nsspssun $f class A $.
	f1_nsspssun $f class B $.
	p_nsspssun $p |- ( -. A C_ B <-> B C. ( A u. B ) ) $= f1_nsspssun f0_nsspssun p_ssun2 f1_nsspssun f0_nsspssun f1_nsspssun a_cun a_wss f0_nsspssun f1_nsspssun a_cun f1_nsspssun a_wss a_wn p_biantrur f1_nsspssun p_ssid f1_nsspssun f1_nsspssun a_wss f0_nsspssun f1_nsspssun a_wss p_biantru f0_nsspssun f1_nsspssun f1_nsspssun p_unss f0_nsspssun f1_nsspssun a_wss f0_nsspssun f1_nsspssun a_wss f1_nsspssun f1_nsspssun a_wss a_wa f0_nsspssun f1_nsspssun a_cun f1_nsspssun a_wss p_bitri f0_nsspssun f1_nsspssun a_cun f1_nsspssun a_wss f1_nsspssun f0_nsspssun f1_nsspssun a_cun a_wss f0_nsspssun f1_nsspssun a_cun f1_nsspssun a_wss a_wn a_wa f0_nsspssun f1_nsspssun a_wss p_xchnxbir f1_nsspssun f0_nsspssun f1_nsspssun a_cun p_dfpss3 f0_nsspssun f1_nsspssun a_wss a_wn f1_nsspssun f0_nsspssun f1_nsspssun a_cun a_wss f0_nsspssun f1_nsspssun a_cun f1_nsspssun a_wss a_wn a_wa f1_nsspssun f0_nsspssun f1_nsspssun a_cun a_wpss p_bitr4i $.
$}

$(Subclass defined in terms of class difference.  See comments under
       ~ dfun2 .  (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfss4 $f class A $.
	f1_dfss4 $f class B $.
	i0_dfss4 $f set x $.
	p_dfss4 $p |- ( A C_ B <-> ( B \ ( B \ A ) ) = A ) $= f0_dfss4 f1_dfss4 p_sseqin2 i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 p_eldif i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 a_cdif a_wcel i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wn a_wa p_notbii i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 a_cdif a_wcel a_wn i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wn a_wa a_wn i0_dfss4 a_sup_set_class f1_dfss4 a_wcel p_anbi2i i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 p_elin i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel p_abai i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel p_iman i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wi i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wn a_wa a_wn i0_dfss4 a_sup_set_class f1_dfss4 a_wcel p_anbi2i i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 a_cin a_wcel i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wa i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wi a_wa i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wn a_wa a_wn a_wa p_3bitri i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 a_cdif a_wcel a_wn a_wa i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f1_dfss4 a_wcel i0_dfss4 a_sup_set_class f0_dfss4 a_wcel a_wn a_wa a_wn a_wa i0_dfss4 a_sup_set_class f1_dfss4 f0_dfss4 a_cin a_wcel p_bitr4i i0_dfss4 f1_dfss4 f1_dfss4 f0_dfss4 a_cdif f1_dfss4 f0_dfss4 a_cin p_difeqri f1_dfss4 f1_dfss4 f0_dfss4 a_cdif a_cdif f1_dfss4 f0_dfss4 a_cin f0_dfss4 p_eqeq1i f0_dfss4 f1_dfss4 a_wss f1_dfss4 f0_dfss4 a_cin f0_dfss4 a_wceq f1_dfss4 f1_dfss4 f0_dfss4 a_cdif a_cdif f0_dfss4 a_wceq p_bitr4i $.
$}

$(An alternate definition of the union of two classes in terms of class
       difference, requiring no dummy variables.  Along with ~ dfin2 and
       ~ dfss4 it shows we can express union, intersection, and subset directly
       in terms of the single "primitive" operation ` \ ` (class difference).
       (Contributed by NM, 10-Jun-2004.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfun2 $f class A $.
	f1_dfun2 $f class B $.
	i0_dfun2 $f set x $.
	p_dfun2 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) \ B ) ) $= i0_dfun2 p_vex i0_dfun2 a_sup_set_class a_cvv f0_dfun2 p_eldif i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif a_wcel i0_dfun2 a_sup_set_class a_cvv a_wcel i0_dfun2 a_sup_set_class f0_dfun2 a_wcel a_wn p_mpbiran i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif a_wcel i0_dfun2 a_sup_set_class f0_dfun2 a_wcel a_wn i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wn p_anbi1i i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif f1_dfun2 p_eldif i0_dfun2 a_sup_set_class f0_dfun2 a_wcel i0_dfun2 a_sup_set_class f1_dfun2 a_wcel p_ioran i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif a_wcel i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wn a_wa i0_dfun2 a_sup_set_class f0_dfun2 a_wcel a_wn i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wn a_wa i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_wcel i0_dfun2 a_sup_set_class f0_dfun2 a_wcel i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wo a_wn p_3bitr4i i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_wcel i0_dfun2 a_sup_set_class f0_dfun2 a_wcel i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wo p_con2bii i0_dfun2 p_vex i0_dfun2 a_sup_set_class a_cvv a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif p_eldif i0_dfun2 a_sup_set_class a_cvv a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_cdif a_wcel i0_dfun2 a_sup_set_class a_cvv a_wcel i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_wcel a_wn p_mpbiran i0_dfun2 a_sup_set_class f0_dfun2 a_wcel i0_dfun2 a_sup_set_class f1_dfun2 a_wcel a_wo i0_dfun2 a_sup_set_class a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_wcel a_wn i0_dfun2 a_sup_set_class a_cvv a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_cdif a_wcel p_bitr4i i0_dfun2 f0_dfun2 f1_dfun2 a_cvv a_cvv f0_dfun2 a_cdif f1_dfun2 a_cdif a_cdif p_uneqri $.
$}

$(An alternate definition of the intersection of two classes in terms of
       class difference, requiring no dummy variables.  See comments under
       ~ dfun2 .  Another version is given by ~ dfin4 .  (Contributed by NM,
       10-Jun-2004.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfin2 $f class A $.
	f1_dfin2 $f class B $.
	i0_dfin2 $f set x $.
	p_dfin2 $p |- ( A i^i B ) = ( A \ ( _V \ B ) ) $= i0_dfin2 p_vex i0_dfin2 a_sup_set_class a_cvv f1_dfin2 p_eldif i0_dfin2 a_sup_set_class a_cvv f1_dfin2 a_cdif a_wcel i0_dfin2 a_sup_set_class a_cvv a_wcel i0_dfin2 a_sup_set_class f1_dfin2 a_wcel a_wn p_mpbiran i0_dfin2 a_sup_set_class a_cvv f1_dfin2 a_cdif a_wcel i0_dfin2 a_sup_set_class f1_dfin2 a_wcel p_con2bii i0_dfin2 a_sup_set_class f1_dfin2 a_wcel i0_dfin2 a_sup_set_class a_cvv f1_dfin2 a_cdif a_wcel a_wn i0_dfin2 a_sup_set_class f0_dfin2 a_wcel p_anbi2i i0_dfin2 a_sup_set_class f0_dfin2 a_cvv f1_dfin2 a_cdif p_eldif i0_dfin2 a_sup_set_class f0_dfin2 a_wcel i0_dfin2 a_sup_set_class f1_dfin2 a_wcel a_wa i0_dfin2 a_sup_set_class f0_dfin2 a_wcel i0_dfin2 a_sup_set_class a_cvv f1_dfin2 a_cdif a_wcel a_wn a_wa i0_dfin2 a_sup_set_class f0_dfin2 a_cvv f1_dfin2 a_cdif a_cdif a_wcel p_bitr4i i0_dfin2 f0_dfin2 f1_dfin2 f0_dfin2 a_cvv f1_dfin2 a_cdif a_cdif p_ineqri $.
$}

$(Difference with intersection.  Theorem 33 of [Suppes] p. 29.
       (Contributed by NM, 31-Mar-1998.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_difin $f class A $.
	f1_difin $f class B $.
	i0_difin $f set x $.
	p_difin $p |- ( A \ ( A i^i B ) ) = ( A \ B ) $= i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel p_pm4.61 i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel p_anclb i0_difin a_sup_set_class f0_difin f1_difin p_elin i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wa i0_difin a_sup_set_class f0_difin a_wcel p_imbi2i i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel p_iman i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wi i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wa a_wi i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel a_wi i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel a_wn a_wa a_wn p_3bitr2i i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wi i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel a_wn a_wa p_con2bii i0_difin a_sup_set_class f0_difin f1_difin p_eldif i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wi a_wn i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f1_difin a_wcel a_wn a_wa i0_difin a_sup_set_class f0_difin a_wcel i0_difin a_sup_set_class f0_difin f1_difin a_cin a_wcel a_wn a_wa i0_difin a_sup_set_class f0_difin f1_difin a_cdif a_wcel p_3bitr4i i0_difin f0_difin f0_difin f1_difin a_cin f0_difin f1_difin a_cdif p_difeqri $.
$}

$(Union defined in terms of intersection (De Morgan's law).  Definition of
     union in [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)

${
	$v A B  $.
	f0_dfun3 $f class A $.
	f1_dfun3 $f class B $.
	p_dfun3 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) i^i ( _V \ B ) ) ) $= f0_dfun3 f1_dfun3 p_dfun2 a_cvv f0_dfun3 a_cdif a_cvv f1_dfun3 a_cdif p_dfin2 f1_dfun3 p_ddif a_cvv a_cvv f1_dfun3 a_cdif a_cdif f1_dfun3 a_cvv f0_dfun3 a_cdif p_difeq2i a_cvv f0_dfun3 a_cdif a_cvv f1_dfun3 a_cdif a_cin a_cvv f0_dfun3 a_cdif a_cvv a_cvv f1_dfun3 a_cdif a_cdif a_cdif a_cvv f0_dfun3 a_cdif f1_dfun3 a_cdif p_eqtr2i a_cvv f0_dfun3 a_cdif f1_dfun3 a_cdif a_cvv f0_dfun3 a_cdif a_cvv f1_dfun3 a_cdif a_cin a_cvv p_difeq2i f0_dfun3 f1_dfun3 a_cun a_cvv a_cvv f0_dfun3 a_cdif f1_dfun3 a_cdif a_cdif a_cvv a_cvv f0_dfun3 a_cdif a_cvv f1_dfun3 a_cdif a_cin a_cdif p_eqtri $.
$}

$(Intersection defined in terms of union (De Morgan's law.  Similar to
     Exercise 4.10(n) of [Mendelson] p. 231.  (Contributed by NM,
     8-Jan-2002.) $)

${
	$v A B  $.
	f0_dfin3 $f class A $.
	f1_dfin3 $f class B $.
	p_dfin3 $p |- ( A i^i B ) = ( _V \ ( ( _V \ A ) u. ( _V \ B ) ) ) $= f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif p_ddif a_cvv f0_dfin3 a_cdif a_cvv f1_dfin3 a_cdif p_dfun2 f0_dfin3 p_ddif a_cvv a_cvv f0_dfin3 a_cdif a_cdif f0_dfin3 a_cvv f1_dfin3 a_cdif p_difeq1i a_cvv a_cvv f0_dfin3 a_cdif a_cdif a_cvv f1_dfin3 a_cdif a_cdif f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif a_cvv p_difeq2i a_cvv f0_dfin3 a_cdif a_cvv f1_dfin3 a_cdif a_cun a_cvv a_cvv a_cvv f0_dfin3 a_cdif a_cdif a_cvv f1_dfin3 a_cdif a_cdif a_cdif a_cvv f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif a_cdif p_eqtri a_cvv f0_dfin3 a_cdif a_cvv f1_dfin3 a_cdif a_cun a_cvv f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif a_cdif a_cvv p_difeq2i f0_dfin3 f1_dfin3 p_dfin2 a_cvv a_cvv f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif a_cdif a_cdif f0_dfin3 a_cvv f1_dfin3 a_cdif a_cdif a_cvv a_cvv f0_dfin3 a_cdif a_cvv f1_dfin3 a_cdif a_cun a_cdif f0_dfin3 f1_dfin3 a_cin p_3eqtr4ri $.
$}

$(Alternate definition of the intersection of two classes.  Exercise 4.10(q)
     of [Mendelson] p. 231.  (Contributed by NM, 25-Nov-2003.) $)

${
	$v A B  $.
	f0_dfin4 $f class A $.
	f1_dfin4 $f class B $.
	p_dfin4 $p |- ( A i^i B ) = ( A \ ( A \ B ) ) $= f0_dfin4 f1_dfin4 p_inss1 f0_dfin4 f1_dfin4 a_cin f0_dfin4 p_dfss4 f0_dfin4 f1_dfin4 a_cin f0_dfin4 a_wss f0_dfin4 f0_dfin4 f0_dfin4 f1_dfin4 a_cin a_cdif a_cdif f0_dfin4 f1_dfin4 a_cin a_wceq p_mpbi f0_dfin4 f1_dfin4 p_difin f0_dfin4 f0_dfin4 f1_dfin4 a_cin a_cdif f0_dfin4 f1_dfin4 a_cdif f0_dfin4 p_difeq2i f0_dfin4 f0_dfin4 f0_dfin4 f1_dfin4 a_cin a_cdif a_cdif f0_dfin4 f1_dfin4 a_cin f0_dfin4 f0_dfin4 f1_dfin4 a_cdif a_cdif p_eqtr3i $.
$}

$(Intersection with universal complement.  Remark in [Stoll] p. 20.
     (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B  $.
	f0_invdif $f class A $.
	f1_invdif $f class B $.
	p_invdif $p |- ( A i^i ( _V \ B ) ) = ( A \ B ) $= f0_invdif a_cvv f1_invdif a_cdif p_dfin2 f1_invdif p_ddif a_cvv a_cvv f1_invdif a_cdif a_cdif f1_invdif f0_invdif p_difeq2i f0_invdif a_cvv f1_invdif a_cdif a_cin f0_invdif a_cvv a_cvv f1_invdif a_cdif a_cdif a_cdif f0_invdif f1_invdif a_cdif p_eqtri $.
$}

$(Intersection with class difference.  Theorem 34 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B  $.
	f0_indif $f class A $.
	f1_indif $f class B $.
	p_indif $p |- ( A i^i ( A \ B ) ) = ( A \ B ) $= f0_indif f0_indif f1_indif a_cdif p_dfin4 f0_indif f1_indif p_dfin4 f0_indif f1_indif a_cin f0_indif f0_indif f1_indif a_cdif a_cdif f0_indif p_difeq2i f0_indif f1_indif p_difin f0_indif f0_indif f1_indif a_cdif a_cin f0_indif f0_indif f0_indif f1_indif a_cdif a_cdif a_cdif f0_indif f0_indif f1_indif a_cin a_cdif f0_indif f1_indif a_cdif p_3eqtr2i $.
$}

$(Bring an intersection in and out of a class difference.  (Contributed by
     Jeff Hankins, 15-Jul-2009.) $)

${
	$v A B C  $.
	f0_indif2 $f class A $.
	f1_indif2 $f class B $.
	f2_indif2 $f class C $.
	p_indif2 $p |- ( A i^i ( B \ C ) ) = ( ( A i^i B ) \ C ) $= f0_indif2 f1_indif2 a_cvv f2_indif2 a_cdif p_inass f0_indif2 f1_indif2 a_cin f2_indif2 p_invdif f1_indif2 f2_indif2 p_invdif f1_indif2 a_cvv f2_indif2 a_cdif a_cin f1_indif2 f2_indif2 a_cdif f0_indif2 p_ineq2i f0_indif2 f1_indif2 a_cin a_cvv f2_indif2 a_cdif a_cin f0_indif2 f1_indif2 a_cvv f2_indif2 a_cdif a_cin a_cin f0_indif2 f1_indif2 a_cin f2_indif2 a_cdif f0_indif2 f1_indif2 f2_indif2 a_cdif a_cin p_3eqtr3ri $.
$}

$(Bring an intersection in and out of a class difference.  (Contributed by
     Mario Carneiro, 15-May-2015.) $)

${
	$v A B C  $.
	f0_indif1 $f class A $.
	f1_indif1 $f class B $.
	f2_indif1 $f class C $.
	p_indif1 $p |- ( ( A \ C ) i^i B ) = ( ( A i^i B ) \ C ) $= f1_indif1 f0_indif1 f2_indif1 p_indif2 f1_indif1 f0_indif1 f2_indif1 a_cdif p_incom f1_indif1 f0_indif1 p_incom f1_indif1 f0_indif1 a_cin f0_indif1 f1_indif1 a_cin f2_indif1 p_difeq1i f1_indif1 f0_indif1 f2_indif1 a_cdif a_cin f1_indif1 f0_indif1 a_cin f2_indif1 a_cdif f0_indif1 f2_indif1 a_cdif f1_indif1 a_cin f0_indif1 f1_indif1 a_cin f2_indif1 a_cdif p_3eqtr3i $.
$}

$(Commutation law for intersection and difference.  (Contributed by Scott
     Fenton, 18-Feb-2013.) $)

${
	$v A B C  $.
	f0_indifcom $f class A $.
	f1_indifcom $f class B $.
	f2_indifcom $f class C $.
	p_indifcom $p |- ( A i^i ( B \ C ) ) = ( B i^i ( A \ C ) ) $= f0_indifcom f1_indifcom p_incom f0_indifcom f1_indifcom a_cin f1_indifcom f0_indifcom a_cin f2_indifcom p_difeq1i f0_indifcom f1_indifcom f2_indifcom p_indif2 f1_indifcom f0_indifcom f2_indifcom p_indif2 f0_indifcom f1_indifcom a_cin f2_indifcom a_cdif f1_indifcom f0_indifcom a_cin f2_indifcom a_cdif f0_indifcom f1_indifcom f2_indifcom a_cdif a_cin f1_indifcom f0_indifcom f2_indifcom a_cdif a_cin p_3eqtr4i $.
$}

$(Distributive law for intersection over union.  Exercise 10 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_indi $f class A $.
	f1_indi $f class B $.
	f2_indi $f class C $.
	i0_indi $f set x $.
	p_indi $p |- ( A i^i ( B u. C ) ) = ( ( A i^i B ) u. ( A i^i C ) ) $= i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel p_andi i0_indi a_sup_set_class f0_indi f1_indi p_elin i0_indi a_sup_set_class f0_indi f2_indi p_elin i0_indi a_sup_set_class f0_indi f1_indi a_cin a_wcel i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi a_wcel a_wa i0_indi a_sup_set_class f0_indi f2_indi a_cin a_wcel i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel a_wa p_orbi12i i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel a_wo a_wa i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi a_wcel a_wa i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel a_wa a_wo i0_indi a_sup_set_class f0_indi f1_indi a_cin a_wcel i0_indi a_sup_set_class f0_indi f2_indi a_cin a_wcel a_wo p_bitr4i i0_indi a_sup_set_class f1_indi f2_indi p_elun i0_indi a_sup_set_class f1_indi f2_indi a_cun a_wcel i0_indi a_sup_set_class f1_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel a_wo i0_indi a_sup_set_class f0_indi a_wcel p_anbi2i i0_indi a_sup_set_class f0_indi f1_indi a_cin f0_indi f2_indi a_cin p_elun i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi a_wcel i0_indi a_sup_set_class f2_indi a_wcel a_wo a_wa i0_indi a_sup_set_class f0_indi f1_indi a_cin a_wcel i0_indi a_sup_set_class f0_indi f2_indi a_cin a_wcel a_wo i0_indi a_sup_set_class f0_indi a_wcel i0_indi a_sup_set_class f1_indi f2_indi a_cun a_wcel a_wa i0_indi a_sup_set_class f0_indi f1_indi a_cin f0_indi f2_indi a_cin a_cun a_wcel p_3bitr4i i0_indi f0_indi f1_indi f2_indi a_cun f0_indi f1_indi a_cin f0_indi f2_indi a_cin a_cun p_ineqri $.
$}

$(Distributive law for union over intersection.  Exercise 11 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_undi $f class A $.
	f1_undi $f class B $.
	f2_undi $f class C $.
	i0_undi $f set x $.
	p_undi $p |- ( A u. ( B i^i C ) ) = ( ( A u. B ) i^i ( A u. C ) ) $= i0_undi a_sup_set_class f1_undi f2_undi p_elin i0_undi a_sup_set_class f1_undi f2_undi a_cin a_wcel i0_undi a_sup_set_class f1_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel a_wa i0_undi a_sup_set_class f0_undi a_wcel p_orbi2i i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel p_ordi i0_undi a_sup_set_class f0_undi f1_undi a_cun f0_undi f2_undi a_cun p_elin i0_undi a_sup_set_class f0_undi f1_undi p_elun i0_undi a_sup_set_class f0_undi f2_undi p_elun i0_undi a_sup_set_class f0_undi f1_undi a_cun a_wcel i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi a_wcel a_wo i0_undi a_sup_set_class f0_undi f2_undi a_cun a_wcel i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel a_wo p_anbi12i i0_undi a_sup_set_class f0_undi f1_undi a_cun f0_undi f2_undi a_cun a_cin a_wcel i0_undi a_sup_set_class f0_undi f1_undi a_cun a_wcel i0_undi a_sup_set_class f0_undi f2_undi a_cun a_wcel a_wa i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi a_wcel a_wo i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel a_wo a_wa p_bitr2i i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi f2_undi a_cin a_wcel a_wo i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel a_wa a_wo i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f1_undi a_wcel a_wo i0_undi a_sup_set_class f0_undi a_wcel i0_undi a_sup_set_class f2_undi a_wcel a_wo a_wa i0_undi a_sup_set_class f0_undi f1_undi a_cun f0_undi f2_undi a_cun a_cin a_wcel p_3bitri i0_undi f0_undi f1_undi f2_undi a_cin f0_undi f1_undi a_cun f0_undi f2_undi a_cun a_cin p_uneqri $.
$}

$(Distributive law for intersection over union.  Theorem 28 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)

${
	$v A B C  $.
	f0_indir $f class A $.
	f1_indir $f class B $.
	f2_indir $f class C $.
	p_indir $p |- ( ( A u. B ) i^i C ) = ( ( A i^i C ) u. ( B i^i C ) ) $= f2_indir f0_indir f1_indir p_indi f0_indir f1_indir a_cun f2_indir p_incom f0_indir f2_indir p_incom f1_indir f2_indir p_incom f0_indir f2_indir a_cin f2_indir f0_indir a_cin f1_indir f2_indir a_cin f2_indir f1_indir a_cin p_uneq12i f2_indir f0_indir f1_indir a_cun a_cin f2_indir f0_indir a_cin f2_indir f1_indir a_cin a_cun f0_indir f1_indir a_cun f2_indir a_cin f0_indir f2_indir a_cin f1_indir f2_indir a_cin a_cun p_3eqtr4i $.
$}

$(Distributive law for union over intersection.  Theorem 29 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)

${
	$v A B C  $.
	f0_undir $f class A $.
	f1_undir $f class B $.
	f2_undir $f class C $.
	p_undir $p |- ( ( A i^i B ) u. C ) = ( ( A u. C ) i^i ( B u. C ) ) $= f2_undir f0_undir f1_undir p_undi f0_undir f1_undir a_cin f2_undir p_uncom f0_undir f2_undir p_uncom f1_undir f2_undir p_uncom f0_undir f2_undir a_cun f2_undir f0_undir a_cun f1_undir f2_undir a_cun f2_undir f1_undir a_cun p_ineq12i f2_undir f0_undir f1_undir a_cin a_cun f2_undir f0_undir a_cun f2_undir f1_undir a_cun a_cin f0_undir f1_undir a_cin f2_undir a_cun f0_undir f2_undir a_cun f1_undir f2_undir a_cun a_cin p_3eqtr4i $.
$}

$(Infer equality from equalities of union and intersection.  Exercise 20
       of [Enderton] p. 32 and its converse.  (Contributed by NM,
       10-Aug-2004.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_unineq $f class A $.
	f1_unineq $f class B $.
	f2_unineq $f class C $.
	i0_unineq $f set x $.
	p_unineq $p |- ( ( ( A u. C ) = ( B u. C ) /\ ( A i^i C ) = ( B i^i C ) ) <-> A = B ) $= f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin i0_unineq a_sup_set_class p_eleq2 i0_unineq a_sup_set_class f0_unineq f2_unineq p_elin i0_unineq a_sup_set_class f1_unineq f2_unineq p_elin f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq i0_unineq a_sup_set_class f0_unineq f2_unineq a_cin a_wcel i0_unineq a_sup_set_class f1_unineq f2_unineq a_cin a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa i0_unineq a_sup_set_class f1_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa p_3bitr3g i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel p_iba i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel p_iba i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa i0_unineq a_sup_set_class f1_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa p_bibi12d f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wb i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa i0_unineq a_sup_set_class f1_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel a_wa a_wb p_syl5ibr i0_unineq a_sup_set_class f2_unineq a_wcel f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wb f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq p_adantld f0_unineq f2_unineq p_uncom f1_unineq f2_unineq p_uncom f0_unineq f2_unineq a_cun f2_unineq f0_unineq a_cun f1_unineq f2_unineq a_cun f2_unineq f1_unineq a_cun p_eqeq12i f2_unineq f0_unineq a_cun f2_unineq f1_unineq a_cun i0_unineq a_sup_set_class p_eleq2 f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq f2_unineq f0_unineq a_cun f2_unineq f1_unineq a_cun a_wceq i0_unineq a_sup_set_class f2_unineq f0_unineq a_cun a_wcel i0_unineq a_sup_set_class f2_unineq f1_unineq a_cun a_wcel a_wb p_sylbi i0_unineq a_sup_set_class f2_unineq f0_unineq p_elun i0_unineq a_sup_set_class f2_unineq f1_unineq p_elun f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq i0_unineq a_sup_set_class f2_unineq f0_unineq a_cun a_wcel i0_unineq a_sup_set_class f2_unineq f1_unineq a_cun a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel a_wo i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wo p_3bitr3g i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel p_biorf i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel p_biorf i0_unineq a_sup_set_class f2_unineq a_wcel a_wn i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel a_wo i0_unineq a_sup_set_class f1_unineq a_wcel i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wo p_bibi12d f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wb i0_unineq a_sup_set_class f2_unineq a_wcel a_wn i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f0_unineq a_wcel a_wo i0_unineq a_sup_set_class f2_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wo a_wb p_syl5ibr i0_unineq a_sup_set_class f2_unineq a_wcel a_wn f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wb f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq p_adantrd i0_unineq a_sup_set_class f2_unineq a_wcel f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq a_wa i0_unineq a_sup_set_class f0_unineq a_wcel i0_unineq a_sup_set_class f1_unineq a_wcel a_wb a_wi p_pm2.61i f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq a_wa i0_unineq f0_unineq f1_unineq p_eqrdv f0_unineq f1_unineq f2_unineq p_uneq1 f0_unineq f1_unineq f2_unineq p_ineq1 f0_unineq f1_unineq a_wceq f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq p_jca f0_unineq f2_unineq a_cun f1_unineq f2_unineq a_cun a_wceq f0_unineq f2_unineq a_cin f1_unineq f2_unineq a_cin a_wceq a_wa f0_unineq f1_unineq a_wceq p_impbii $.
$}

$(Equality of union and intersection implies equality of their arguments.
     (Contributed by NM, 16-Apr-2006.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)

${
	$v A B  $.
	f0_uneqin $f class A $.
	f1_uneqin $f class B $.
	p_uneqin $p |- ( ( A u. B ) = ( A i^i B ) <-> A = B ) $= f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin p_eqimss f0_uneqin f1_uneqin f0_uneqin f1_uneqin a_cin p_unss f0_uneqin f0_uneqin f1_uneqin p_ssin f0_uneqin f0_uneqin f1_uneqin p_sstr f0_uneqin f0_uneqin f1_uneqin a_cin a_wss f0_uneqin f0_uneqin a_wss f0_uneqin f1_uneqin a_wss a_wa f0_uneqin f1_uneqin a_wss p_sylbir f1_uneqin f0_uneqin f1_uneqin p_ssin f1_uneqin f0_uneqin a_wss f1_uneqin f1_uneqin a_wss p_simpl f1_uneqin f0_uneqin f1_uneqin a_cin a_wss f1_uneqin f0_uneqin a_wss f1_uneqin f1_uneqin a_wss a_wa f1_uneqin f0_uneqin a_wss p_sylbir f0_uneqin f0_uneqin f1_uneqin a_cin a_wss f0_uneqin f1_uneqin a_wss f1_uneqin f0_uneqin f1_uneqin a_cin a_wss f1_uneqin f0_uneqin a_wss p_anim12i f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin a_wss f0_uneqin f0_uneqin f1_uneqin a_cin a_wss f1_uneqin f0_uneqin f1_uneqin a_cin a_wss a_wa f0_uneqin f1_uneqin a_wss f1_uneqin f0_uneqin a_wss a_wa p_sylbir f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin a_wceq f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin a_wss f0_uneqin f1_uneqin a_wss f1_uneqin f0_uneqin a_wss a_wa p_syl f0_uneqin f1_uneqin p_eqss f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin a_wceq f0_uneqin f1_uneqin a_wss f1_uneqin f0_uneqin a_wss a_wa f0_uneqin f1_uneqin a_wceq p_sylibr f0_uneqin p_unidm f0_uneqin p_inidm f0_uneqin f0_uneqin a_cun f0_uneqin f0_uneqin f0_uneqin a_cin p_eqtr4i f0_uneqin f1_uneqin f0_uneqin p_uneq2 f0_uneqin f1_uneqin f0_uneqin p_ineq2 f0_uneqin f1_uneqin a_wceq f0_uneqin f0_uneqin a_cun f0_uneqin f0_uneqin a_cin f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin p_3eqtr3a f0_uneqin f1_uneqin a_cun f0_uneqin f1_uneqin a_cin a_wceq f0_uneqin f1_uneqin a_wceq p_impbii $.
$}

$(Distributive law for class difference.  Theorem 39 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B C  $.
	f0_difundi $f class A $.
	f1_difundi $f class B $.
	f2_difundi $f class C $.
	p_difundi $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) i^i ( A \ C ) ) $= f1_difundi f2_difundi p_dfun3 f1_difundi f2_difundi a_cun a_cvv a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif a_cin a_cdif f0_difundi p_difeq2i f0_difundi a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif p_inindi f0_difundi a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif a_cin p_dfin2 f0_difundi f1_difundi p_invdif f0_difundi f2_difundi p_invdif f0_difundi a_cvv f1_difundi a_cdif a_cin f0_difundi f1_difundi a_cdif f0_difundi a_cvv f2_difundi a_cdif a_cin f0_difundi f2_difundi a_cdif p_ineq12i f0_difundi a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif a_cin a_cin f0_difundi a_cvv f1_difundi a_cdif a_cin f0_difundi a_cvv f2_difundi a_cdif a_cin a_cin f0_difundi a_cvv a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif a_cin a_cdif a_cdif f0_difundi f1_difundi a_cdif f0_difundi f2_difundi a_cdif a_cin p_3eqtr3i f0_difundi f1_difundi f2_difundi a_cun a_cdif f0_difundi a_cvv a_cvv f1_difundi a_cdif a_cvv f2_difundi a_cdif a_cin a_cdif a_cdif f0_difundi f1_difundi a_cdif f0_difundi f2_difundi a_cdif a_cin p_eqtri $.
$}

$(Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)

${
	$v A B C  $.
	f0_difundir $f class A $.
	f1_difundir $f class B $.
	f2_difundir $f class C $.
	p_difundir $p |- ( ( A u. B ) \ C ) = ( ( A \ C ) u. ( B \ C ) ) $= f0_difundir f1_difundir a_cvv f2_difundir a_cdif p_indir f0_difundir f1_difundir a_cun f2_difundir p_invdif f0_difundir f2_difundir p_invdif f1_difundir f2_difundir p_invdif f0_difundir a_cvv f2_difundir a_cdif a_cin f0_difundir f2_difundir a_cdif f1_difundir a_cvv f2_difundir a_cdif a_cin f1_difundir f2_difundir a_cdif p_uneq12i f0_difundir f1_difundir a_cun a_cvv f2_difundir a_cdif a_cin f0_difundir a_cvv f2_difundir a_cdif a_cin f1_difundir a_cvv f2_difundir a_cdif a_cin a_cun f0_difundir f1_difundir a_cun f2_difundir a_cdif f0_difundir f2_difundir a_cdif f1_difundir f2_difundir a_cdif a_cun p_3eqtr3i $.
$}

$(Distributive law for class difference.  Theorem 40 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)

${
	$v A B C  $.
	f0_difindi $f class A $.
	f1_difindi $f class B $.
	f2_difindi $f class C $.
	p_difindi $p |- ( A \ ( B i^i C ) ) = ( ( A \ B ) u. ( A \ C ) ) $= f1_difindi f2_difindi p_dfin3 f1_difindi f2_difindi a_cin a_cvv a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif a_cun a_cdif f0_difindi p_difeq2i f0_difindi a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif p_indi f0_difindi a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif a_cun p_dfin2 f0_difindi f1_difindi p_invdif f0_difindi f2_difindi p_invdif f0_difindi a_cvv f1_difindi a_cdif a_cin f0_difindi f1_difindi a_cdif f0_difindi a_cvv f2_difindi a_cdif a_cin f0_difindi f2_difindi a_cdif p_uneq12i f0_difindi a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif a_cun a_cin f0_difindi a_cvv f1_difindi a_cdif a_cin f0_difindi a_cvv f2_difindi a_cdif a_cin a_cun f0_difindi a_cvv a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif a_cun a_cdif a_cdif f0_difindi f1_difindi a_cdif f0_difindi f2_difindi a_cdif a_cun p_3eqtr3i f0_difindi f1_difindi f2_difindi a_cin a_cdif f0_difindi a_cvv a_cvv f1_difindi a_cdif a_cvv f2_difindi a_cdif a_cun a_cdif a_cdif f0_difindi f1_difindi a_cdif f0_difindi f2_difindi a_cdif a_cun p_eqtri $.
$}

$(Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)

${
	$v A B C  $.
	f0_difindir $f class A $.
	f1_difindir $f class B $.
	f2_difindir $f class C $.
	p_difindir $p |- ( ( A i^i B ) \ C ) = ( ( A \ C ) i^i ( B \ C ) ) $= f0_difindir f1_difindir a_cvv f2_difindir a_cdif p_inindir f0_difindir f1_difindir a_cin f2_difindir p_invdif f0_difindir f2_difindir p_invdif f1_difindir f2_difindir p_invdif f0_difindir a_cvv f2_difindir a_cdif a_cin f0_difindir f2_difindir a_cdif f1_difindir a_cvv f2_difindir a_cdif a_cin f1_difindir f2_difindir a_cdif p_ineq12i f0_difindir f1_difindir a_cin a_cvv f2_difindir a_cdif a_cin f0_difindir a_cvv f2_difindir a_cdif a_cin f1_difindir a_cvv f2_difindir a_cdif a_cin a_cin f0_difindir f1_difindir a_cin f2_difindir a_cdif f0_difindir f2_difindir a_cdif f1_difindir f2_difindir a_cdif a_cin p_3eqtr3i $.
$}

$(Distribute intersection over difference.  (Contributed by Scott Fenton,
       14-Apr-2011.) $)

${
	$v A B C  $.
	$d A x  $.
	$d B x  $.
	$d C x  $.
	f0_indifdir $f class A $.
	f1_indifdir $f class B $.
	f2_indifdir $f class C $.
	i0_indifdir $f set x $.
	p_indifdir $p |- ( ( A \ B ) i^i C ) = ( ( A i^i C ) \ ( B i^i C ) ) $= i0_indifdir a_sup_set_class f2_indifdir a_wcel p_pm3.24 i0_indifdir a_sup_set_class f2_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel p_intnan i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn p_anass i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wa a_wa p_mtbir i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa p_biorfi i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn i0_indifdir a_sup_set_class f2_indifdir a_wcel p_an32 i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn p_andi i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wa a_wo i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wo a_wa p_3bitr4i i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel p_ianor i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa a_wn i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wo i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa p_anbi2i i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wn a_wo a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa a_wn a_wa p_bitr4i i0_indifdir a_sup_set_class f0_indifdir f1_indifdir a_cdif f2_indifdir p_elin i0_indifdir a_sup_set_class f0_indifdir f1_indifdir p_eldif i0_indifdir a_sup_set_class f0_indifdir f1_indifdir a_cdif a_wcel i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel p_anbi1i i0_indifdir a_sup_set_class f0_indifdir f1_indifdir a_cdif f2_indifdir a_cin a_wcel i0_indifdir a_sup_set_class f0_indifdir f1_indifdir a_cdif a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa p_bitri i0_indifdir a_sup_set_class f0_indifdir f2_indifdir a_cin f1_indifdir f2_indifdir a_cin p_eldif i0_indifdir a_sup_set_class f0_indifdir f2_indifdir p_elin i0_indifdir a_sup_set_class f1_indifdir f2_indifdir p_elin i0_indifdir a_sup_set_class f1_indifdir f2_indifdir a_cin a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa p_notbii i0_indifdir a_sup_set_class f0_indifdir f2_indifdir a_cin a_wcel i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir f2_indifdir a_cin a_wcel a_wn i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa a_wn p_anbi12i i0_indifdir a_sup_set_class f0_indifdir f2_indifdir a_cin f1_indifdir f2_indifdir a_cin a_cdif a_wcel i0_indifdir a_sup_set_class f0_indifdir f2_indifdir a_cin a_wcel i0_indifdir a_sup_set_class f1_indifdir f2_indifdir a_cin a_wcel a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa a_wn a_wa p_bitri i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f1_indifdir a_wcel a_wn a_wa i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f0_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa i0_indifdir a_sup_set_class f1_indifdir a_wcel i0_indifdir a_sup_set_class f2_indifdir a_wcel a_wa a_wn a_wa i0_indifdir a_sup_set_class f0_indifdir f1_indifdir a_cdif f2_indifdir a_cin a_wcel i0_indifdir a_sup_set_class f0_indifdir f2_indifdir a_cin f1_indifdir f2_indifdir a_cin a_cdif a_wcel p_3bitr4i i0_indifdir f0_indifdir f1_indifdir a_cdif f2_indifdir a_cin f0_indifdir f2_indifdir a_cin f1_indifdir f2_indifdir a_cin a_cdif p_eqriv $.
$}

$(De Morgan's law for union.  Theorem 5.2(13) of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)

${
	$v A B  $.
	f0_undm $f class A $.
	f1_undm $f class B $.
	p_undm $p |- ( _V \ ( A u. B ) ) = ( ( _V \ A ) i^i ( _V \ B ) ) $= a_cvv f0_undm f1_undm p_difundi $.
$}

$(De Morgan's law for intersection.  Theorem 5.2(13') of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)

${
	$v A B  $.
	f0_indm $f class A $.
	f1_indm $f class B $.
	p_indm $p |- ( _V \ ( A i^i B ) ) = ( ( _V \ A ) u. ( _V \ B ) ) $= a_cvv f0_indm f1_indm p_difindi $.
$}

$(A relationship involving double difference and union.  (Contributed by NM,
     29-Aug-2004.) $)

${
	$v A B C  $.
	f0_difun1 $f class A $.
	f1_difun1 $f class B $.
	f2_difun1 $f class C $.
	p_difun1 $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) \ C ) $= f0_difun1 a_cvv f1_difun1 a_cdif a_cvv f2_difun1 a_cdif p_inass f0_difun1 a_cvv f1_difun1 a_cdif a_cin f2_difun1 p_invdif f0_difun1 a_cvv f1_difun1 a_cdif a_cin a_cvv f2_difun1 a_cdif a_cin f0_difun1 a_cvv f1_difun1 a_cdif a_cvv f2_difun1 a_cdif a_cin a_cin f0_difun1 a_cvv f1_difun1 a_cdif a_cin f2_difun1 a_cdif p_eqtr3i f1_difun1 f2_difun1 p_undm a_cvv f1_difun1 f2_difun1 a_cun a_cdif a_cvv f1_difun1 a_cdif a_cvv f2_difun1 a_cdif a_cin f0_difun1 p_ineq2i f0_difun1 f1_difun1 f2_difun1 a_cun p_invdif f0_difun1 a_cvv f1_difun1 f2_difun1 a_cun a_cdif a_cin f0_difun1 a_cvv f1_difun1 a_cdif a_cvv f2_difun1 a_cdif a_cin a_cin f0_difun1 f1_difun1 f2_difun1 a_cun a_cdif p_eqtr3i f0_difun1 a_cvv f1_difun1 a_cdif a_cvv f2_difun1 a_cdif a_cin a_cin f0_difun1 a_cvv f1_difun1 a_cdif a_cin f2_difun1 a_cdif f0_difun1 f1_difun1 f2_difun1 a_cun a_cdif p_eqtr3i f0_difun1 f1_difun1 p_invdif f0_difun1 a_cvv f1_difun1 a_cdif a_cin f0_difun1 f1_difun1 a_cdif f2_difun1 p_difeq1i f0_difun1 a_cvv f1_difun1 a_cdif a_cin f2_difun1 a_cdif f0_difun1 f1_difun1 f2_difun1 a_cun a_cdif f0_difun1 f1_difun1 a_cdif f2_difun1 a_cdif p_eqtr3i $.
$}

$(An equality involving class union and class difference.  The first
       equality of Exercise 13 of [TakeutiZaring] p. 22.  (Contributed by Alan
       Sare, 17-Apr-2012.) $)

${
	$v A B C  $.
	$d A x  $.
	$d B x  $.
	$d C x  $.
	f0_undif3 $f class A $.
	f1_undif3 $f class B $.
	f2_undif3 $f class C $.
	i0_undif3 $f set x $.
	p_undif3 $p |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) ) $= i0_undif3 a_sup_set_class f0_undif3 f1_undif3 p_elun i0_undif3 a_sup_set_class f2_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel p_pm4.53 i0_undif3 a_sup_set_class f2_undif3 f0_undif3 p_eldif i0_undif3 a_sup_set_class f2_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wn a_wa i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 f0_undif3 a_cdif a_wcel p_xchnxbir i0_undif3 a_sup_set_class f0_undif3 f1_undif3 a_cun a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 f0_undif3 a_cdif a_wcel a_wn i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo p_anbi12i i0_undif3 a_sup_set_class f0_undif3 f1_undif3 a_cun f2_undif3 f0_undif3 a_cdif p_eldif i0_undif3 a_sup_set_class f0_undif3 f1_undif3 f2_undif3 a_cdif p_elun i0_undif3 a_sup_set_class f1_undif3 f2_undif3 p_eldif i0_undif3 a_sup_set_class f1_undif3 f2_undif3 a_cdif a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa i0_undif3 a_sup_set_class f0_undif3 a_wcel p_orbi2i i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel p_orc i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn p_olc i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo p_jca i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel p_olc i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel p_orc i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo p_anim12i i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo a_wa i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa p_jaoi i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn p_simpl i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa p_orcd i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa i0_undif3 a_sup_set_class f0_undif3 a_wcel p_olc i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa p_orc i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa a_wo i0_undif3 a_sup_set_class f0_undif3 a_wcel p_adantr i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa p_orc i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa a_wo i0_undif3 a_sup_set_class f1_undif3 a_wcel p_adantl i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa a_wo p_ccase i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa a_wo i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo a_wa p_impbii i0_undif3 a_sup_set_class f0_undif3 f1_undif3 f2_undif3 a_cdif a_cun a_wcel i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 f2_undif3 a_cdif a_wcel a_wo i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn a_wa a_wo i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo a_wa p_3bitri i0_undif3 a_sup_set_class f0_undif3 f1_undif3 a_cun a_wcel i0_undif3 a_sup_set_class f2_undif3 f0_undif3 a_cdif a_wcel a_wn a_wa i0_undif3 a_sup_set_class f0_undif3 a_wcel i0_undif3 a_sup_set_class f1_undif3 a_wcel a_wo i0_undif3 a_sup_set_class f2_undif3 a_wcel a_wn i0_undif3 a_sup_set_class f0_undif3 a_wcel a_wo a_wa i0_undif3 a_sup_set_class f0_undif3 f1_undif3 a_cun f2_undif3 f0_undif3 a_cdif a_cdif a_wcel i0_undif3 a_sup_set_class f0_undif3 f1_undif3 f2_undif3 a_cdif a_cun a_wcel p_3bitr4ri i0_undif3 f0_undif3 f1_undif3 f2_undif3 a_cdif a_cun f0_undif3 f1_undif3 a_cun f2_undif3 f0_undif3 a_cdif a_cdif p_eqriv $.
$}

$(Represent a set difference as an intersection with a larger difference.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)

${
	$v A B C  $.
	$d A x  $.
	$d B x  $.
	$d C x  $.
	f0_difin2 $f class A $.
	f1_difin2 $f class B $.
	f2_difin2 $f class C $.
	i0_difin2 $f set x $.
	p_difin2 $p |- ( A C_ C -> ( A \ B ) = ( ( C \ B ) i^i A ) ) $= f0_difin2 f2_difin2 i0_difin2 a_sup_set_class p_ssel f0_difin2 f2_difin2 a_wss i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel p_pm4.71d f0_difin2 f2_difin2 a_wss i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn p_anbi1d i0_difin2 a_sup_set_class f0_difin2 f1_difin2 p_eldif i0_difin2 a_sup_set_class f2_difin2 f1_difin2 a_cdif f0_difin2 p_elin i0_difin2 a_sup_set_class f2_difin2 f1_difin2 p_eldif i0_difin2 a_sup_set_class f2_difin2 f1_difin2 a_cdif a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel p_anbi1i i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel p_ancom i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn p_anass i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa p_bitr4i i0_difin2 a_sup_set_class f2_difin2 f1_difin2 a_cdif f0_difin2 a_cin a_wcel i0_difin2 a_sup_set_class f2_difin2 f1_difin2 a_cdif a_wcel i0_difin2 a_sup_set_class f0_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f2_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa p_3bitri f0_difin2 f2_difin2 a_wss i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 a_wcel i0_difin2 a_sup_set_class f2_difin2 a_wcel a_wa i0_difin2 a_sup_set_class f1_difin2 a_wcel a_wn a_wa i0_difin2 a_sup_set_class f0_difin2 f1_difin2 a_cdif a_wcel i0_difin2 a_sup_set_class f2_difin2 f1_difin2 a_cdif f0_difin2 a_cin a_wcel p_3bitr4g f0_difin2 f2_difin2 a_wss i0_difin2 f0_difin2 f1_difin2 a_cdif f2_difin2 f1_difin2 a_cdif f0_difin2 a_cin p_eqrdv $.
$}

$(Swap second and third argument of double difference.  (Contributed by NM,
     18-Aug-2004.) $)

${
	$v A B C  $.
	f0_dif32 $f class A $.
	f1_dif32 $f class B $.
	f2_dif32 $f class C $.
	p_dif32 $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ B ) $= f1_dif32 f2_dif32 p_uncom f1_dif32 f2_dif32 a_cun f2_dif32 f1_dif32 a_cun f0_dif32 p_difeq2i f0_dif32 f1_dif32 f2_dif32 p_difun1 f0_dif32 f2_dif32 f1_dif32 p_difun1 f0_dif32 f1_dif32 f2_dif32 a_cun a_cdif f0_dif32 f2_dif32 f1_dif32 a_cun a_cdif f0_dif32 f1_dif32 a_cdif f2_dif32 a_cdif f0_dif32 f2_dif32 a_cdif f1_dif32 a_cdif p_3eqtr3i $.
$}

$(Absorption-like law for class difference: you can remove a class only
     once.  (Contributed by FL, 2-Aug-2009.) $)

${
	$v A B  $.
	f0_difabs $f class A $.
	f1_difabs $f class B $.
	p_difabs $p |- ( ( A \ B ) \ B ) = ( A \ B ) $= f0_difabs f1_difabs f1_difabs p_difun1 f1_difabs p_unidm f1_difabs f1_difabs a_cun f1_difabs f0_difabs p_difeq2i f0_difabs f1_difabs f1_difabs a_cun a_cdif f0_difabs f1_difabs a_cdif f1_difabs a_cdif f0_difabs f1_difabs a_cdif p_eqtr3i $.
$}

$(Two ways to express symmetric difference.  This theorem shows the
     equivalence of the definition of symmetric difference in [Stoll] p. 13 and
     the restated definition in Example 4.1 of [Stoll] p. 262.  (Contributed by
     NM, 17-Aug-2004.) $)

${
	$v A B  $.
	f0_symdif1 $f class A $.
	f1_symdif1 $f class B $.
	p_symdif1 $p |- ( ( A \ B ) u. ( B \ A ) ) = ( ( A u. B ) \ ( A i^i B ) ) $= f0_symdif1 f1_symdif1 f0_symdif1 f1_symdif1 a_cin p_difundir f0_symdif1 f1_symdif1 p_difin f0_symdif1 f1_symdif1 p_incom f0_symdif1 f1_symdif1 a_cin f1_symdif1 f0_symdif1 a_cin f1_symdif1 p_difeq2i f1_symdif1 f0_symdif1 p_difin f1_symdif1 f0_symdif1 f1_symdif1 a_cin a_cdif f1_symdif1 f1_symdif1 f0_symdif1 a_cin a_cdif f1_symdif1 f0_symdif1 a_cdif p_eqtri f0_symdif1 f0_symdif1 f1_symdif1 a_cin a_cdif f0_symdif1 f1_symdif1 a_cdif f1_symdif1 f0_symdif1 f1_symdif1 a_cin a_cdif f1_symdif1 f0_symdif1 a_cdif p_uneq12i f0_symdif1 f1_symdif1 a_cun f0_symdif1 f1_symdif1 a_cin a_cdif f0_symdif1 f0_symdif1 f1_symdif1 a_cin a_cdif f1_symdif1 f0_symdif1 f1_symdif1 a_cin a_cdif a_cun f0_symdif1 f1_symdif1 a_cdif f1_symdif1 f0_symdif1 a_cdif a_cun p_eqtr2i $.
$}

$(Two ways to express symmetric difference.  (Contributed by NM,
       17-Aug-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_symdif2 $f set x $.
	f1_symdif2 $f class A $.
	f2_symdif2 $f class B $.
	p_symdif2 $p |- ( ( A \ B ) u. ( B \ A ) ) = { x | -. ( x e. A <-> x e. B ) } $= f0_symdif2 a_sup_set_class f1_symdif2 f2_symdif2 p_eldif f0_symdif2 a_sup_set_class f2_symdif2 f1_symdif2 p_eldif f0_symdif2 a_sup_set_class f1_symdif2 f2_symdif2 a_cdif a_wcel f0_symdif2 a_sup_set_class f1_symdif2 a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel a_wn a_wa f0_symdif2 a_sup_set_class f2_symdif2 f1_symdif2 a_cdif a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel f0_symdif2 a_sup_set_class f1_symdif2 a_wcel a_wn a_wa p_orbi12i f0_symdif2 a_sup_set_class f1_symdif2 f2_symdif2 a_cdif f2_symdif2 f1_symdif2 a_cdif p_elun f0_symdif2 a_sup_set_class f1_symdif2 a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel p_xor f0_symdif2 a_sup_set_class f1_symdif2 f2_symdif2 a_cdif a_wcel f0_symdif2 a_sup_set_class f2_symdif2 f1_symdif2 a_cdif a_wcel a_wo f0_symdif2 a_sup_set_class f1_symdif2 a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel a_wn a_wa f0_symdif2 a_sup_set_class f2_symdif2 a_wcel f0_symdif2 a_sup_set_class f1_symdif2 a_wcel a_wn a_wa a_wo f0_symdif2 a_sup_set_class f1_symdif2 f2_symdif2 a_cdif f2_symdif2 f1_symdif2 a_cdif a_cun a_wcel f0_symdif2 a_sup_set_class f1_symdif2 a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel a_wb a_wn p_3bitr4i f0_symdif2 a_sup_set_class f1_symdif2 a_wcel f0_symdif2 a_sup_set_class f2_symdif2 a_wcel a_wb a_wn f0_symdif2 f1_symdif2 f2_symdif2 a_cdif f2_symdif2 f1_symdif2 a_cdif a_cun p_abbi2i $.
$}

$(Union of two class abstractions.  (Contributed by NM, 29-Sep-2002.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d ph y  $.
	$d ps y  $.
	f0_unab $f wff ph $.
	f1_unab $f wff ps $.
	f2_unab $f set x $.
	i0_unab $f set y $.
	p_unab $p |- ( { x | ph } u. { x | ps } ) = { x | ( ph \/ ps ) } $= f0_unab f1_unab f2_unab i0_unab p_sbor f0_unab f1_unab a_wo i0_unab f2_unab a_df-clab f0_unab i0_unab f2_unab a_df-clab f1_unab i0_unab f2_unab a_df-clab i0_unab a_sup_set_class f0_unab f2_unab a_cab a_wcel f0_unab f2_unab i0_unab a_wsb i0_unab a_sup_set_class f1_unab f2_unab a_cab a_wcel f1_unab f2_unab i0_unab a_wsb p_orbi12i f0_unab f1_unab a_wo f2_unab i0_unab a_wsb f0_unab f2_unab i0_unab a_wsb f1_unab f2_unab i0_unab a_wsb a_wo i0_unab a_sup_set_class f0_unab f1_unab a_wo f2_unab a_cab a_wcel i0_unab a_sup_set_class f0_unab f2_unab a_cab a_wcel i0_unab a_sup_set_class f1_unab f2_unab a_cab a_wcel a_wo p_3bitr4ri i0_unab f0_unab f2_unab a_cab f1_unab f2_unab a_cab f0_unab f1_unab a_wo f2_unab a_cab p_uneqri $.
$}

$(Intersection of two class abstractions.  (Contributed by NM,
       29-Sep-2002.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d ph y  $.
	$d ps y  $.
	f0_inab $f wff ph $.
	f1_inab $f wff ps $.
	f2_inab $f set x $.
	i0_inab $f set y $.
	p_inab $p |- ( { x | ph } i^i { x | ps } ) = { x | ( ph /\ ps ) } $= f0_inab f1_inab f2_inab i0_inab p_sban f0_inab f1_inab a_wa i0_inab f2_inab a_df-clab f0_inab i0_inab f2_inab a_df-clab f1_inab i0_inab f2_inab a_df-clab i0_inab a_sup_set_class f0_inab f2_inab a_cab a_wcel f0_inab f2_inab i0_inab a_wsb i0_inab a_sup_set_class f1_inab f2_inab a_cab a_wcel f1_inab f2_inab i0_inab a_wsb p_anbi12i f0_inab f1_inab a_wa f2_inab i0_inab a_wsb f0_inab f2_inab i0_inab a_wsb f1_inab f2_inab i0_inab a_wsb a_wa i0_inab a_sup_set_class f0_inab f1_inab a_wa f2_inab a_cab a_wcel i0_inab a_sup_set_class f0_inab f2_inab a_cab a_wcel i0_inab a_sup_set_class f1_inab f2_inab a_cab a_wcel a_wa p_3bitr4ri i0_inab f0_inab f2_inab a_cab f1_inab f2_inab a_cab f0_inab f1_inab a_wa f2_inab a_cab p_ineqri $.
$}

$(Difference of two class abstractions.  (Contributed by NM,
       23-Oct-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph ps x  $.
	$d x y  $.
	$d ph y  $.
	$d ps y  $.
	f0_difab $f wff ph $.
	f1_difab $f wff ps $.
	f2_difab $f set x $.
	i0_difab $f set y $.
	p_difab $p |- ( { x | ph } \ { x | ps } ) = { x | ( ph /\ -. ps ) } $= f0_difab f1_difab a_wn a_wa i0_difab f2_difab a_df-clab f0_difab f1_difab a_wn f2_difab i0_difab p_sban f0_difab i0_difab f2_difab a_df-clab i0_difab a_sup_set_class f0_difab f2_difab a_cab a_wcel f0_difab f2_difab i0_difab a_wsb p_bicomi f1_difab f2_difab i0_difab p_sbn f1_difab i0_difab f2_difab a_df-clab f1_difab a_wn f2_difab i0_difab a_wsb f1_difab f2_difab i0_difab a_wsb i0_difab a_sup_set_class f1_difab f2_difab a_cab a_wcel p_xchbinxr f0_difab f2_difab i0_difab a_wsb i0_difab a_sup_set_class f0_difab f2_difab a_cab a_wcel f1_difab a_wn f2_difab i0_difab a_wsb i0_difab a_sup_set_class f1_difab f2_difab a_cab a_wcel a_wn p_anbi12i i0_difab a_sup_set_class f0_difab f1_difab a_wn a_wa f2_difab a_cab a_wcel f0_difab f1_difab a_wn a_wa f2_difab i0_difab a_wsb f0_difab f2_difab i0_difab a_wsb f1_difab a_wn f2_difab i0_difab a_wsb a_wa i0_difab a_sup_set_class f0_difab f2_difab a_cab a_wcel i0_difab a_sup_set_class f1_difab f2_difab a_cab a_wcel a_wn a_wa p_3bitrri i0_difab f0_difab f2_difab a_cab f1_difab f2_difab a_cab f0_difab f1_difab a_wn a_wa f2_difab a_cab p_difeqri $.
$}

$(A class builder defined by a negation.  (Contributed by FL,
     18-Sep-2010.) $)

${
	$v ph x  $.
	f0_notab $f wff ph $.
	f1_notab $f set x $.
	p_notab $p |- { x | -. ph } = ( _V \ { x | ph } ) $= f0_notab a_wn f1_notab a_cvv a_df-rab f0_notab a_wn f1_notab p_rabab f0_notab a_wn f1_notab a_cvv a_crab f1_notab a_sup_set_class a_cvv a_wcel f0_notab a_wn a_wa f1_notab a_cab f0_notab a_wn f1_notab a_cab p_eqtr3i f1_notab a_sup_set_class a_cvv a_wcel f0_notab f1_notab p_difab f1_notab a_cvv p_abid2 f1_notab a_sup_set_class a_cvv a_wcel f1_notab a_cab a_cvv f0_notab f1_notab a_cab p_difeq1i f1_notab a_sup_set_class a_cvv a_wcel f1_notab a_cab f0_notab f1_notab a_cab a_cdif f1_notab a_sup_set_class a_cvv a_wcel f0_notab a_wn a_wa f1_notab a_cab a_cvv f0_notab f1_notab a_cab a_cdif p_eqtr3i f1_notab a_sup_set_class a_cvv a_wcel f0_notab a_wn a_wa f1_notab a_cab f0_notab a_wn f1_notab a_cab a_cvv f0_notab f1_notab a_cab a_cdif p_eqtr3i $.
$}

$(Union of two restricted class abstractions.  (Contributed by NM,
     25-Mar-2004.) $)

${
	$v ph ps x A  $.
	f0_unrab $f wff ph $.
	f1_unrab $f wff ps $.
	f2_unrab $f set x $.
	f3_unrab $f class A $.
	p_unrab $p |- ( { x e. A | ph } u. { x e. A | ps } ) = { x e. A | ( ph \/ ps ) } $= f0_unrab f2_unrab f3_unrab a_df-rab f1_unrab f2_unrab f3_unrab a_df-rab f0_unrab f2_unrab f3_unrab a_crab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_cab f1_unrab f2_unrab f3_unrab a_crab f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa f2_unrab a_cab p_uneq12i f0_unrab f1_unrab a_wo f2_unrab f3_unrab a_df-rab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa f2_unrab p_unab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab f1_unrab p_andi f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab f1_unrab a_wo a_wa f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa a_wo f2_unrab p_abbii f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_cab f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa f2_unrab a_cab a_cun f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa a_wo f2_unrab a_cab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab f1_unrab a_wo a_wa f2_unrab a_cab p_eqtr4i f0_unrab f1_unrab a_wo f2_unrab f3_unrab a_crab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab f1_unrab a_wo a_wa f2_unrab a_cab f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_cab f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa f2_unrab a_cab a_cun p_eqtr4i f0_unrab f2_unrab f3_unrab a_crab f1_unrab f2_unrab f3_unrab a_crab a_cun f2_unrab a_sup_set_class f3_unrab a_wcel f0_unrab a_wa f2_unrab a_cab f2_unrab a_sup_set_class f3_unrab a_wcel f1_unrab a_wa f2_unrab a_cab a_cun f0_unrab f1_unrab a_wo f2_unrab f3_unrab a_crab p_eqtr4i $.
$}

$(Intersection of two restricted class abstractions.  (Contributed by NM,
     1-Sep-2006.) $)

${
	$v ph ps x A  $.
	f0_inrab $f wff ph $.
	f1_inrab $f wff ps $.
	f2_inrab $f set x $.
	f3_inrab $f class A $.
	p_inrab $p |- ( { x e. A | ph } i^i { x e. A | ps } ) = { x e. A | ( ph /\ ps ) } $= f0_inrab f2_inrab f3_inrab a_df-rab f1_inrab f2_inrab f3_inrab a_df-rab f0_inrab f2_inrab f3_inrab a_crab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_cab f1_inrab f2_inrab f3_inrab a_crab f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa f2_inrab a_cab p_ineq12i f0_inrab f1_inrab a_wa f2_inrab f3_inrab a_df-rab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa f2_inrab p_inab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab f1_inrab p_anandi f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab f1_inrab a_wa a_wa f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa a_wa f2_inrab p_abbii f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_cab f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa f2_inrab a_cab a_cin f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa a_wa f2_inrab a_cab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab f1_inrab a_wa a_wa f2_inrab a_cab p_eqtr4i f0_inrab f1_inrab a_wa f2_inrab f3_inrab a_crab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab f1_inrab a_wa a_wa f2_inrab a_cab f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_cab f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa f2_inrab a_cab a_cin p_eqtr4i f0_inrab f2_inrab f3_inrab a_crab f1_inrab f2_inrab f3_inrab a_crab a_cin f2_inrab a_sup_set_class f3_inrab a_wcel f0_inrab a_wa f2_inrab a_cab f2_inrab a_sup_set_class f3_inrab a_wcel f1_inrab a_wa f2_inrab a_cab a_cin f0_inrab f1_inrab a_wa f2_inrab f3_inrab a_crab p_eqtr4i $.
$}

$(Intersection with a restricted class abstraction.  (Contributed by NM,
       19-Nov-2007.) $)

${
	$v ph x A B  $.
	$d x B  $.
	f0_inrab2 $f wff ph $.
	f1_inrab2 $f set x $.
	f2_inrab2 $f class A $.
	f3_inrab2 $f class B $.
	p_inrab2 $p |- ( { x e. A | ph } i^i B ) = { x e. ( A i^i B ) | ph } $= f0_inrab2 f1_inrab2 f2_inrab2 a_df-rab f1_inrab2 f3_inrab2 p_abid2 f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 a_cab f3_inrab2 p_eqcomi f0_inrab2 f1_inrab2 f2_inrab2 a_crab f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_cab f3_inrab2 f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 a_cab p_ineq12i f0_inrab2 f1_inrab2 f2_inrab2 f3_inrab2 a_cin a_df-rab f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 p_inab f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 p_elin f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 a_cin a_wcel f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f1_inrab2 a_sup_set_class f3_inrab2 a_wcel a_wa f0_inrab2 p_anbi1i f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f0_inrab2 p_an32 f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 a_cin a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f1_inrab2 a_sup_set_class f3_inrab2 a_wcel a_wa f0_inrab2 a_wa f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f3_inrab2 a_wcel a_wa p_bitri f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 a_cin a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f3_inrab2 a_wcel a_wa f1_inrab2 p_abbii f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_cab f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 a_cab a_cin f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_sup_set_class f3_inrab2 a_wcel a_wa f1_inrab2 a_cab f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 a_cin a_wcel f0_inrab2 a_wa f1_inrab2 a_cab p_eqtr4i f0_inrab2 f1_inrab2 f2_inrab2 f3_inrab2 a_cin a_crab f1_inrab2 a_sup_set_class f2_inrab2 f3_inrab2 a_cin a_wcel f0_inrab2 a_wa f1_inrab2 a_cab f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_cab f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 a_cab a_cin p_eqtr4i f0_inrab2 f1_inrab2 f2_inrab2 a_crab f3_inrab2 a_cin f1_inrab2 a_sup_set_class f2_inrab2 a_wcel f0_inrab2 a_wa f1_inrab2 a_cab f1_inrab2 a_sup_set_class f3_inrab2 a_wcel f1_inrab2 a_cab a_cin f0_inrab2 f1_inrab2 f2_inrab2 f3_inrab2 a_cin a_crab p_eqtr4i $.
$}

$(Difference of two restricted class abstractions.  (Contributed by NM,
     23-Oct-2004.) $)

${
	$v ph ps x A  $.
	f0_difrab $f wff ph $.
	f1_difrab $f wff ps $.
	f2_difrab $f set x $.
	f3_difrab $f class A $.
	p_difrab $p |- ( { x e. A | ph } \ { x e. A | ps } ) = { x e. A | ( ph /\ -. ps ) } $= f0_difrab f2_difrab f3_difrab a_df-rab f1_difrab f2_difrab f3_difrab a_df-rab f0_difrab f2_difrab f3_difrab a_crab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_cab f1_difrab f2_difrab f3_difrab a_crab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f2_difrab a_cab p_difeq12i f0_difrab f1_difrab a_wn a_wa f2_difrab f3_difrab a_df-rab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f2_difrab p_difab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab f1_difrab a_wn p_anass f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab p_simpr f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f1_difrab p_con3i f1_difrab a_wn f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa p_anim2i f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab p_pm3.2 f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wi f0_difrab p_adantr f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f1_difrab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa p_con3d f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn f1_difrab a_wn p_imdistani f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f1_difrab a_wn a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn a_wa p_impbii f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab f1_difrab a_wn a_wa a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f1_difrab a_wn a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn a_wa p_bitr3i f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab f1_difrab a_wn a_wa a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn a_wa f2_difrab p_abbii f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_cab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f2_difrab a_cab a_cdif f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa a_wn a_wa f2_difrab a_cab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab f1_difrab a_wn a_wa a_wa f2_difrab a_cab p_eqtr4i f0_difrab f1_difrab a_wn a_wa f2_difrab f3_difrab a_crab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab f1_difrab a_wn a_wa a_wa f2_difrab a_cab f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_cab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f2_difrab a_cab a_cdif p_eqtr4i f0_difrab f2_difrab f3_difrab a_crab f1_difrab f2_difrab f3_difrab a_crab a_cdif f2_difrab a_sup_set_class f3_difrab a_wcel f0_difrab a_wa f2_difrab a_cab f2_difrab a_sup_set_class f3_difrab a_wcel f1_difrab a_wa f2_difrab a_cab a_cdif f0_difrab f1_difrab a_wn a_wa f2_difrab f3_difrab a_crab p_eqtr4i $.
$}

$(Alternate definition of restricted class abstraction.  (Contributed by
       NM, 20-Sep-2003.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	f0_dfrab2 $f wff ph $.
	f1_dfrab2 $f set x $.
	f2_dfrab2 $f class A $.
	p_dfrab2 $p |- { x e. A | ph } = ( { x | ph } i^i A ) $= f0_dfrab2 f1_dfrab2 f2_dfrab2 a_df-rab f1_dfrab2 a_sup_set_class f2_dfrab2 a_wcel f0_dfrab2 f1_dfrab2 p_inab f1_dfrab2 f2_dfrab2 p_abid2 f1_dfrab2 a_sup_set_class f2_dfrab2 a_wcel f1_dfrab2 a_cab f2_dfrab2 f0_dfrab2 f1_dfrab2 a_cab p_ineq1i f1_dfrab2 a_sup_set_class f2_dfrab2 a_wcel f1_dfrab2 a_cab f0_dfrab2 f1_dfrab2 a_cab a_cin f1_dfrab2 a_sup_set_class f2_dfrab2 a_wcel f0_dfrab2 a_wa f1_dfrab2 a_cab f2_dfrab2 f0_dfrab2 f1_dfrab2 a_cab a_cin p_eqtr3i f2_dfrab2 f0_dfrab2 f1_dfrab2 a_cab p_incom f0_dfrab2 f1_dfrab2 f2_dfrab2 a_crab f1_dfrab2 a_sup_set_class f2_dfrab2 a_wcel f0_dfrab2 a_wa f1_dfrab2 a_cab f2_dfrab2 f0_dfrab2 f1_dfrab2 a_cab a_cin f0_dfrab2 f1_dfrab2 a_cab f2_dfrab2 a_cin p_3eqtri $.
$}

$(Alternate definition of restricted class abstraction.  (Contributed by
       Mario Carneiro, 8-Sep-2013.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	f0_dfrab3 $f wff ph $.
	f1_dfrab3 $f set x $.
	f2_dfrab3 $f class A $.
	p_dfrab3 $p |- { x e. A | ph } = ( A i^i { x | ph } ) $= f0_dfrab3 f1_dfrab3 f2_dfrab3 a_df-rab f1_dfrab3 a_sup_set_class f2_dfrab3 a_wcel f0_dfrab3 f1_dfrab3 p_inab f1_dfrab3 f2_dfrab3 p_abid2 f1_dfrab3 a_sup_set_class f2_dfrab3 a_wcel f1_dfrab3 a_cab f2_dfrab3 f0_dfrab3 f1_dfrab3 a_cab p_ineq1i f0_dfrab3 f1_dfrab3 f2_dfrab3 a_crab f1_dfrab3 a_sup_set_class f2_dfrab3 a_wcel f0_dfrab3 a_wa f1_dfrab3 a_cab f1_dfrab3 a_sup_set_class f2_dfrab3 a_wcel f1_dfrab3 a_cab f0_dfrab3 f1_dfrab3 a_cab a_cin f2_dfrab3 f0_dfrab3 f1_dfrab3 a_cab a_cin p_3eqtr2i $.
$}

$(Complementation of restricted class abstractions.  (Contributed by Mario
       Carneiro, 3-Sep-2015.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	f0_notrab $f wff ph $.
	f1_notrab $f set x $.
	f2_notrab $f class A $.
	p_notrab $p |- ( A \ { x e. A | ph } ) = { x e. A | -. ph } $= f1_notrab a_sup_set_class f2_notrab a_wcel f0_notrab f1_notrab p_difab f2_notrab f0_notrab f1_notrab a_cab p_difin f0_notrab f1_notrab f2_notrab p_dfrab3 f0_notrab f1_notrab f2_notrab a_crab f2_notrab f0_notrab f1_notrab a_cab a_cin f2_notrab p_difeq2i f1_notrab f2_notrab p_abid2 f1_notrab a_sup_set_class f2_notrab a_wcel f1_notrab a_cab f2_notrab f0_notrab f1_notrab a_cab p_difeq1i f2_notrab f2_notrab f0_notrab f1_notrab a_cab a_cin a_cdif f2_notrab f0_notrab f1_notrab a_cab a_cdif f2_notrab f0_notrab f1_notrab f2_notrab a_crab a_cdif f1_notrab a_sup_set_class f2_notrab a_wcel f1_notrab a_cab f0_notrab f1_notrab a_cab a_cdif p_3eqtr4i f0_notrab a_wn f1_notrab f2_notrab a_df-rab f1_notrab a_sup_set_class f2_notrab a_wcel f1_notrab a_cab f0_notrab f1_notrab a_cab a_cdif f1_notrab a_sup_set_class f2_notrab a_wcel f0_notrab a_wn a_wa f1_notrab a_cab f2_notrab f0_notrab f1_notrab f2_notrab a_crab a_cdif f0_notrab a_wn f1_notrab f2_notrab a_crab p_3eqtr4i $.
$}

$(Restricted class abstraction with a common superset.  (Contributed by
       Stefan O'Rear, 12-Sep-2015.)  (Proof shortened by Mario Carneiro,
       8-Nov-2015.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfrab3ss $f wff ph $.
	f1_dfrab3ss $f set x $.
	f2_dfrab3ss $f class A $.
	f3_dfrab3ss $f class B $.
	p_dfrab3ss $p |- ( A C_ B -> { x e. A | ph } = ( A i^i { x e. B | ph } ) ) $= f2_dfrab3ss f3_dfrab3ss a_df-ss f2_dfrab3ss f3_dfrab3ss a_cin f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab p_ineq1 f2_dfrab3ss f3_dfrab3ss a_cin f2_dfrab3ss a_wceq f2_dfrab3ss f3_dfrab3ss a_cin f0_dfrab3ss f1_dfrab3ss a_cab a_cin f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab a_cin p_eqcomd f2_dfrab3ss f3_dfrab3ss a_wss f2_dfrab3ss f3_dfrab3ss a_cin f2_dfrab3ss a_wceq f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab a_cin f2_dfrab3ss f3_dfrab3ss a_cin f0_dfrab3ss f1_dfrab3ss a_cab a_cin a_wceq p_sylbi f0_dfrab3ss f1_dfrab3ss f2_dfrab3ss p_dfrab3 f0_dfrab3ss f1_dfrab3ss f3_dfrab3ss p_dfrab3 f0_dfrab3ss f1_dfrab3ss f3_dfrab3ss a_crab f3_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab a_cin f2_dfrab3ss p_ineq2i f2_dfrab3ss f3_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab p_inass f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss f3_dfrab3ss a_crab a_cin f2_dfrab3ss f3_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab a_cin a_cin f2_dfrab3ss f3_dfrab3ss a_cin f0_dfrab3ss f1_dfrab3ss a_cab a_cin p_eqtr4i f2_dfrab3ss f3_dfrab3ss a_wss f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss a_cab a_cin f2_dfrab3ss f3_dfrab3ss a_cin f0_dfrab3ss f1_dfrab3ss a_cab a_cin f0_dfrab3ss f1_dfrab3ss f2_dfrab3ss a_crab f2_dfrab3ss f0_dfrab3ss f1_dfrab3ss f3_dfrab3ss a_crab a_cin p_3eqtr4g $.
$}

$(Abstraction restricted to a union.  (Contributed by Stefan O'Rear,
     5-Feb-2015.) $)

${
	$v ph x A B  $.
	f0_rabun2 $f wff ph $.
	f1_rabun2 $f set x $.
	f2_rabun2 $f class A $.
	f3_rabun2 $f class B $.
	p_rabun2 $p |- { x e. ( A u. B ) | ph } = ( { x e. A | ph } u. { x e. B | ph } ) $= f0_rabun2 f1_rabun2 f2_rabun2 f3_rabun2 a_cun a_df-rab f0_rabun2 f1_rabun2 f2_rabun2 a_df-rab f0_rabun2 f1_rabun2 f3_rabun2 a_df-rab f0_rabun2 f1_rabun2 f2_rabun2 a_crab f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab f0_rabun2 f1_rabun2 f3_rabun2 a_crab f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab p_uneq12i f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 p_elun f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f1_rabun2 a_sup_set_class f3_rabun2 a_wcel a_wo f0_rabun2 p_anbi1i f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 p_andir f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f1_rabun2 a_sup_set_class f3_rabun2 a_wcel a_wo f0_rabun2 a_wa f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa a_wo p_bitri f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa a_wo f1_rabun2 p_abbii f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 p_unab f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f0_rabun2 a_wa f1_rabun2 a_cab f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa a_wo f1_rabun2 a_cab f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab a_cun p_eqtr4i f0_rabun2 f1_rabun2 f2_rabun2 a_crab f0_rabun2 f1_rabun2 f3_rabun2 a_crab a_cun f1_rabun2 a_sup_set_class f2_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab f1_rabun2 a_sup_set_class f3_rabun2 a_wcel f0_rabun2 a_wa f1_rabun2 a_cab a_cun f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f0_rabun2 a_wa f1_rabun2 a_cab p_eqtr4i f0_rabun2 f1_rabun2 f2_rabun2 f3_rabun2 a_cun a_crab f1_rabun2 a_sup_set_class f2_rabun2 f3_rabun2 a_cun a_wcel f0_rabun2 a_wa f1_rabun2 a_cab f0_rabun2 f1_rabun2 f2_rabun2 a_crab f0_rabun2 f1_rabun2 f3_rabun2 a_crab a_cun p_eqtr4i $.
$}

$(Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       20-Oct-2005.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reuss2 $f wff ph $.
	f1_reuss2 $f wff ps $.
	f2_reuss2 $f set x $.
	f3_reuss2 $f class A $.
	f4_reuss2 $f class B $.
	p_reuss2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> E! x e. A ph ) $= f0_reuss2 f2_reuss2 f3_reuss2 a_df-rex f1_reuss2 f2_reuss2 f4_reuss2 a_df-reu f0_reuss2 f2_reuss2 f3_reuss2 a_wrex f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f1_reuss2 f2_reuss2 f4_reuss2 a_wreu f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu p_anbi12i f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_df-ral f3_reuss2 f4_reuss2 f2_reuss2 a_sup_set_class p_ssel f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f0_reuss2 f1_reuss2 p_prth f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f2_reuss2 a_sup_set_class f4_reuss2 a_wcel a_wi f0_reuss2 f1_reuss2 a_wi f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi p_sylan f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa p_exp4b f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi p_com23 f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f1_reuss2 a_wi f0_reuss2 f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi p_a2d f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f1_reuss2 a_wi a_wi f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa p_imp4a f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f1_reuss2 a_wi a_wi f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi f2_reuss2 p_alimdv f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f1_reuss2 a_wi a_wi f2_reuss2 a_wal f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi f2_reuss2 a_wal p_imp f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral f3_reuss2 f4_reuss2 a_wss f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 f1_reuss2 a_wi a_wi f2_reuss2 a_wal f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi f2_reuss2 a_wal p_sylan2b f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 p_euimmo f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral a_wa f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa a_wi f2_reuss2 a_wal f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wmo a_wi p_syl f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 p_eu5 f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_weu f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wmo p_simplbi2 f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral a_wa f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wmo f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_weu p_syl9 f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral a_wa f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_weu p_imp32 f0_reuss2 f2_reuss2 f3_reuss2 a_df-reu f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral a_wa f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu a_wa a_wa f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_weu f0_reuss2 f2_reuss2 f3_reuss2 a_wreu p_sylibr f0_reuss2 f2_reuss2 f3_reuss2 a_wrex f1_reuss2 f2_reuss2 f4_reuss2 a_wreu a_wa f3_reuss2 f4_reuss2 a_wss f0_reuss2 f1_reuss2 a_wi f2_reuss2 f3_reuss2 a_wral a_wa f2_reuss2 a_sup_set_class f3_reuss2 a_wcel f0_reuss2 a_wa f2_reuss2 a_wex f2_reuss2 a_sup_set_class f4_reuss2 a_wcel f1_reuss2 a_wa f2_reuss2 a_weu a_wa f0_reuss2 f2_reuss2 f3_reuss2 a_wreu p_sylan2b $.
$}

$(Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       21-Aug-1999.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reuss $f wff ph $.
	f1_reuss $f set x $.
	f2_reuss $f class A $.
	f3_reuss $f class B $.
	p_reuss $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> E! x e. A ph ) $= f1_reuss a_sup_set_class f2_reuss a_wcel f0_reuss p_idd f0_reuss f0_reuss a_wi f1_reuss f2_reuss p_rgen f0_reuss f0_reuss f1_reuss f2_reuss f3_reuss p_reuss2 f2_reuss f3_reuss a_wss f0_reuss f0_reuss a_wi f1_reuss f2_reuss a_wral f0_reuss f1_reuss f2_reuss a_wrex f0_reuss f1_reuss f3_reuss a_wreu a_wa f0_reuss f1_reuss f2_reuss a_wreu p_mpanl2 f2_reuss f3_reuss a_wss f0_reuss f1_reuss f2_reuss a_wrex f0_reuss f1_reuss f3_reuss a_wreu f0_reuss f1_reuss f2_reuss a_wreu p_3impb $.
$}

$(Transfer uniqueness to a smaller class.  (Contributed by NM,
       21-Oct-2005.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reuun1 $f wff ph $.
	f1_reuun1 $f wff ps $.
	f2_reuun1 $f set x $.
	f3_reuun1 $f class A $.
	f4_reuun1 $f class B $.
	p_reuun1 $p |- ( ( E. x e. A ph /\ E! x e. ( A u. B ) ( ph \/ ps ) ) -> E! x e. A ph ) $= f3_reuun1 f4_reuun1 p_ssun1 f0_reuun1 f1_reuun1 p_orc f0_reuun1 f0_reuun1 f1_reuun1 a_wo a_wi f2_reuun1 f3_reuun1 p_rgenw f0_reuun1 f0_reuun1 f1_reuun1 a_wo f2_reuun1 f3_reuun1 f3_reuun1 f4_reuun1 a_cun p_reuss2 f3_reuun1 f3_reuun1 f4_reuun1 a_cun a_wss f0_reuun1 f0_reuun1 f1_reuun1 a_wo a_wi f2_reuun1 f3_reuun1 a_wral f0_reuun1 f2_reuun1 f3_reuun1 a_wrex f0_reuun1 f1_reuun1 a_wo f2_reuun1 f3_reuun1 f4_reuun1 a_cun a_wreu a_wa f0_reuun1 f2_reuun1 f3_reuun1 a_wreu p_mpanl12 $.
$}

$(Transfer uniqueness to a smaller or larger class.  (Contributed by NM,
       21-Oct-2005.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reuun2 $f wff ph $.
	f1_reuun2 $f set x $.
	f2_reuun2 $f class A $.
	f3_reuun2 $f class B $.
	p_reuun2 $p |- ( -. E. x e. B ph -> ( E! x e. ( A u. B ) ph <-> E! x e. A ph ) ) $= f0_reuun2 f1_reuun2 f3_reuun2 a_df-rex f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 p_euor2 f0_reuun2 f1_reuun2 f3_reuun2 a_wrex f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_wex f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo f1_reuun2 a_weu f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_weu a_wb p_sylnbi f0_reuun2 f1_reuun2 f2_reuun2 f3_reuun2 a_cun a_df-reu f1_reuun2 a_sup_set_class f2_reuun2 f3_reuun2 p_elun f1_reuun2 a_sup_set_class f2_reuun2 f3_reuun2 a_cun a_wcel f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f1_reuun2 a_sup_set_class f3_reuun2 a_wcel a_wo f0_reuun2 p_anbi1i f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 p_andir f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa p_orcom f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f1_reuun2 a_sup_set_class f3_reuun2 a_wcel a_wo f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa a_wo f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo p_bitri f1_reuun2 a_sup_set_class f2_reuun2 f3_reuun2 a_cun a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f1_reuun2 a_sup_set_class f3_reuun2 a_wcel a_wo f0_reuun2 a_wa f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo p_bitri f1_reuun2 a_sup_set_class f2_reuun2 f3_reuun2 a_cun a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo f1_reuun2 p_eubii f0_reuun2 f1_reuun2 f2_reuun2 f3_reuun2 a_cun a_wreu f1_reuun2 a_sup_set_class f2_reuun2 f3_reuun2 a_cun a_wcel f0_reuun2 a_wa f1_reuun2 a_weu f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo f1_reuun2 a_weu p_bitri f0_reuun2 f1_reuun2 f2_reuun2 a_df-reu f0_reuun2 f1_reuun2 f3_reuun2 a_wrex a_wn f1_reuun2 a_sup_set_class f3_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa a_wo f1_reuun2 a_weu f1_reuun2 a_sup_set_class f2_reuun2 a_wcel f0_reuun2 a_wa f1_reuun2 a_weu f0_reuun2 f1_reuun2 f2_reuun2 f3_reuun2 a_cun a_wreu f0_reuun2 f1_reuun2 f2_reuun2 a_wreu p_3bitr4g $.
$}

$(Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       NM, 21-Aug-1999.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_reupick $f wff ph $.
	f1_reupick $f set x $.
	f2_reupick $f class A $.
	f3_reupick $f class B $.
	p_reupick $p |- ( ( ( A C_ B /\ ( E. x e. A ph /\ E! x e. B ph ) ) /\ ph ) -> ( x e. A <-> x e. B ) ) $= f2_reupick f3_reupick f1_reupick a_sup_set_class p_ssel f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f1_reupick a_sup_set_class f3_reupick a_wcel a_wi f0_reupick f1_reupick f2_reupick a_wrex f0_reupick f1_reupick f3_reupick a_wreu a_wa f0_reupick p_ad2antrr f0_reupick f1_reupick f2_reupick a_df-rex f0_reupick f1_reupick f3_reupick a_df-reu f0_reupick f1_reupick f2_reupick a_wrex f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_wex f0_reupick f1_reupick f3_reupick a_wreu f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu p_anbi12i f2_reupick f3_reupick f1_reupick a_sup_set_class p_ssel f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f1_reupick a_sup_set_class f3_reupick a_wcel p_ancrd f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f1_reupick a_sup_set_class f3_reupick a_wcel f1_reupick a_sup_set_class f2_reupick a_wcel a_wa f0_reupick p_anim1d f1_reupick a_sup_set_class f3_reupick a_wcel f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick p_an32 f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f3_reupick a_wcel f1_reupick a_sup_set_class f2_reupick a_wcel a_wa f0_reupick a_wa f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wa p_syl6ib f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wa f1_reupick p_eximdv f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel f1_reupick p_eupick f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_ex f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_syl9 f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_com23 f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_imp32 f0_reupick f1_reupick f2_reupick a_wrex f0_reupick f1_reupick f3_reupick a_wreu a_wa f2_reupick f3_reupick a_wss f1_reupick a_sup_set_class f2_reupick a_wcel f0_reupick a_wa f1_reupick a_wex f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_weu a_wa f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_sylan2b f2_reupick f3_reupick a_wss f0_reupick f1_reupick f2_reupick a_wrex f0_reupick f1_reupick f3_reupick a_wreu a_wa a_wa f1_reupick a_sup_set_class f3_reupick a_wcel f0_reupick f1_reupick a_sup_set_class f2_reupick a_wcel p_exp3acom23 f2_reupick f3_reupick a_wss f0_reupick f1_reupick f2_reupick a_wrex f0_reupick f1_reupick f3_reupick a_wreu a_wa a_wa f0_reupick f1_reupick a_sup_set_class f3_reupick a_wcel f1_reupick a_sup_set_class f2_reupick a_wcel a_wi p_imp f2_reupick f3_reupick a_wss f0_reupick f1_reupick f2_reupick a_wrex f0_reupick f1_reupick f3_reupick a_wreu a_wa a_wa f0_reupick a_wa f1_reupick a_sup_set_class f2_reupick a_wcel f1_reupick a_sup_set_class f3_reupick a_wcel p_impbid $.
$}

$(Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 19-Nov-2016.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x  $.
	f0_reupick3 $f wff ph $.
	f1_reupick3 $f wff ps $.
	f2_reupick3 $f set x $.
	f3_reupick3 $f class A $.
	p_reupick3 $p |- ( ( E! x e. A ph /\ E. x e. A ( ph /\ ps ) /\ x e. A ) -> ( ph -> ps ) ) $= f0_reupick3 f2_reupick3 f3_reupick3 a_df-reu f0_reupick3 f1_reupick3 a_wa f2_reupick3 f3_reupick3 a_df-rex f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 f1_reupick3 p_anass f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f1_reupick3 a_wa f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 f1_reupick3 a_wa a_wa f2_reupick3 p_exbii f0_reupick3 f1_reupick3 a_wa f2_reupick3 f3_reupick3 a_wrex f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 f1_reupick3 a_wa a_wa f2_reupick3 a_wex f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f1_reupick3 a_wa f2_reupick3 a_wex p_bitr4i f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f1_reupick3 f2_reupick3 p_eupick f0_reupick3 f2_reupick3 f3_reupick3 a_wreu f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f2_reupick3 a_weu f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f1_reupick3 a_wa f2_reupick3 a_wex f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 a_wa f1_reupick3 a_wi f0_reupick3 f1_reupick3 a_wa f2_reupick3 f3_reupick3 a_wrex p_syl2anb f0_reupick3 f2_reupick3 f3_reupick3 a_wreu f0_reupick3 f1_reupick3 a_wa f2_reupick3 f3_reupick3 a_wrex a_wa f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 f1_reupick3 p_exp3a f0_reupick3 f2_reupick3 f3_reupick3 a_wreu f0_reupick3 f1_reupick3 a_wa f2_reupick3 f3_reupick3 a_wrex f2_reupick3 a_sup_set_class f3_reupick3 a_wcel f0_reupick3 f1_reupick3 a_wi p_3impia $.
$}

$(Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 15-Dec-2013.)  (Proof shortened by Mario Carneiro,
       19-Nov-2016.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x  $.
	f0_reupick2 $f wff ph $.
	f1_reupick2 $f wff ps $.
	f2_reupick2 $f set x $.
	f3_reupick2 $f class A $.
	p_reupick2 $p |- ( ( ( A. x e. A ( ps -> ph ) /\ E. x e. A ps /\ E! x e. A ph ) /\ x e. A ) -> ( ph <-> ps ) ) $= f1_reupick2 f0_reupick2 p_ancr f1_reupick2 f0_reupick2 a_wi f1_reupick2 f0_reupick2 f1_reupick2 a_wa a_wi f2_reupick2 f3_reupick2 p_ralimi f1_reupick2 f0_reupick2 f1_reupick2 a_wa f2_reupick2 f3_reupick2 p_rexim f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f0_reupick2 f1_reupick2 a_wa a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f1_reupick2 a_wa f2_reupick2 f3_reupick2 a_wrex a_wi p_syl f0_reupick2 f1_reupick2 f2_reupick2 f3_reupick2 p_reupick3 f0_reupick2 f2_reupick2 f3_reupick2 a_wreu f0_reupick2 f1_reupick2 a_wa f2_reupick2 f3_reupick2 a_wrex f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f0_reupick2 f1_reupick2 a_wi p_3exp f0_reupick2 f2_reupick2 f3_reupick2 a_wreu f0_reupick2 f1_reupick2 a_wa f2_reupick2 f3_reupick2 a_wrex f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f0_reupick2 f1_reupick2 a_wi a_wi p_com12 f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f1_reupick2 a_wa f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f2_reupick2 f3_reupick2 a_wreu f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f0_reupick2 f1_reupick2 a_wi a_wi a_wi p_syl6 f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f2_reupick2 f3_reupick2 a_wreu f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f0_reupick2 f1_reupick2 a_wi p_3imp1 f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 p_rsp f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f1_reupick2 f0_reupick2 a_wi a_wi f0_reupick2 f2_reupick2 f3_reupick2 a_wreu p_3ad2ant1 f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f2_reupick2 f3_reupick2 a_wreu a_w3a f2_reupick2 a_sup_set_class f3_reupick2 a_wcel f1_reupick2 f0_reupick2 a_wi p_imp f1_reupick2 f0_reupick2 a_wi f2_reupick2 f3_reupick2 a_wral f1_reupick2 f2_reupick2 f3_reupick2 a_wrex f0_reupick2 f2_reupick2 f3_reupick2 a_wreu a_w3a f2_reupick2 a_sup_set_class f3_reupick2 a_wcel a_wa f0_reupick2 f1_reupick2 p_impbid $.
$}


