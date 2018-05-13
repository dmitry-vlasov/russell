$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Iota_properties.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Cantor's Theorem

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(No set ` A ` is equinumerous to its power set (Cantor's theorem), i.e.
       no function can map ` A ` it onto its power set.  Compare Theorem 6B(b)
       of [Enderton] p. 132.  For the equinumerosity version, see ~ canth2 .
       Note that ` A ` must be a set: this theorem does not hold when ` A ` is
       too large to be a set; see ~ ncanth for a counterexample.  (Use ~ nex if
       you want the form ` -. E. f f : A -onto-> ~P A ` .)  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by Mario Carneiro, 7-Jun-2016.) $)

${
	$v A F  $.
	$d x y A  $.
	$d x y F  $.
	f0_canth $f class A $.
	f1_canth $f class F $.
	i0_canth $f set x $.
	i1_canth $f set y $.
	e0_canth $e |- A e. _V $.
	p_canth $p |- -. F : A -onto-> ~P A $= i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth p_ssrab2 e0_canth i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f0_canth p_elpw2 i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f0_canth a_cpw a_wcel i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f0_canth a_wss p_mpbir f0_canth f0_canth a_cpw f1_canth p_forn f0_canth f0_canth a_cpw f1_canth a_wfo i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f0_canth a_cpw f1_canth a_crn p_syl5eleqr i0_canth a_sup_set_class i1_canth a_sup_set_class a_wceq p_id i0_canth a_sup_set_class i1_canth a_sup_set_class f1_canth p_fveq2 i0_canth a_sup_set_class i1_canth a_sup_set_class a_wceq i0_canth a_sup_set_class i1_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv i1_canth a_sup_set_class f1_canth a_cfv p_eleq12d i0_canth a_sup_set_class i1_canth a_sup_set_class a_wceq i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel p_notbid i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth i1_canth a_sup_set_class f0_canth p_elrab i1_canth a_sup_set_class i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wcel i1_canth a_sup_set_class f0_canth a_wcel i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn p_baibr i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel i1_canth a_sup_set_class i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wcel p_nbbn i1_canth a_sup_set_class f0_canth a_wcel i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i1_canth a_sup_set_class i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wcel a_wb i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel i1_canth a_sup_set_class i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wcel a_wb a_wn p_sylib i1_canth a_sup_set_class f1_canth a_cfv i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab i1_canth a_sup_set_class p_eleq2 i1_canth a_sup_set_class f0_canth a_wcel i1_canth a_sup_set_class i1_canth a_sup_set_class f1_canth a_cfv a_wcel i1_canth a_sup_set_class i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wcel a_wb i1_canth a_sup_set_class f1_canth a_cfv i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wceq p_nsyl i1_canth a_sup_set_class f1_canth a_cfv i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wceq i1_canth f0_canth p_nrex f0_canth f0_canth a_cpw f1_canth p_fofn i1_canth f0_canth i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f1_canth p_fvelrnb f0_canth f0_canth a_cpw f1_canth a_wfo f1_canth f0_canth a_wfn i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f1_canth a_crn a_wcel i1_canth a_sup_set_class f1_canth a_cfv i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wceq i1_canth f0_canth a_wrex a_wb p_syl f0_canth f0_canth a_cpw f1_canth a_wfo i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f1_canth a_crn a_wcel i1_canth a_sup_set_class f1_canth a_cfv i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab a_wceq i1_canth f0_canth a_wrex p_mtbiri f0_canth f0_canth a_cpw f1_canth a_wfo i0_canth a_sup_set_class i0_canth a_sup_set_class f1_canth a_cfv a_wcel a_wn i0_canth f0_canth a_crab f1_canth a_crn a_wcel p_pm2.65i $.
$}

$(Cantor's theorem fails for the universal class (which is not a set but a
     proper class by ~ vprc ).  Specifically, the identity function maps the
     universe onto its power class.  Compare ~ canth that works for sets.  See
     also the remark in ~ ru about NF, in which Cantor's theorem fails for sets
     that are "too large."  This theorem gives some intuition behind that
     failure: in NF the universal class is a set, and it equals its own power
     set.  (Contributed by NM, 29-Jun-2004.) $)

${
	$v  $.
	p_ncanth $p |- _I : _V -onto-> ~P _V $= p_f1ovi p_pwv a_cvv a_cpw a_cvv a_cvv a_cid p_f1oeq3 a_cvv a_cpw a_cvv a_wceq a_cvv a_cvv a_cpw a_cid a_wf1o a_cvv a_cvv a_cid a_wf1o a_wb a_ax-mp a_cvv a_cvv a_cpw a_cid a_wf1o a_cvv a_cvv a_cid a_wf1o p_mpbir a_cvv a_cvv a_cpw a_cid p_f1ofo a_cvv a_cvv a_cpw a_cid a_wf1o a_cvv a_cvv a_cpw a_cid a_wfo a_ax-mp $.
$}


