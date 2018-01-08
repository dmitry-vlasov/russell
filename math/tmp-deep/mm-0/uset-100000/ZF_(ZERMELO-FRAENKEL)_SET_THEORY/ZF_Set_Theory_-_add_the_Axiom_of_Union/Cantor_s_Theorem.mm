$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Iota_properties.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Cantor's Theorem

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( No set ` A ` is equinumerous to its power set (Cantor's theorem), i.e.
       no function can map ` A ` it onto its power set.  Compare Theorem 6B(b)
       of [Enderton] p. 132.  For the equinumerosity version, see ~ canth2 .
       Note that ` A ` must be a set: this theorem does not hold when ` A ` is
       too large to be a set; see ~ ncanth for a counterexample.  (Use ~ nex if
       you want the form ` -. E. f f : A -onto-> ~P A ` .)  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by Mario Carneiro, 7-Jun-2016.) $)
${
	$d x y A $.
	$d x y F $.
	icanth_0 $f set x $.
	icanth_1 $f set y $.
	fcanth_0 $f class A $.
	fcanth_1 $f class F $.
	ecanth_0 $e |- A e. _V $.
	canth $p |- -. F : A -onto-> ~P A $= fcanth_0 fcanth_0 cpw fcanth_1 wfo icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_1 crn wcel fcanth_0 fcanth_0 cpw fcanth_1 wfo icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_0 cpw fcanth_1 crn icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_0 cpw wcel icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_0 wss icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 ssrab2 icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_0 ecanth_0 elpw2 mpbir fcanth_0 fcanth_0 cpw fcanth_1 forn syl5eleqr fcanth_0 fcanth_0 cpw fcanth_1 wfo icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_1 crn wcel icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wceq icanth_1 fcanth_0 wrex icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wceq icanth_1 fcanth_0 icanth_1 cv fcanth_0 wcel icanth_1 cv icanth_1 cv fcanth_1 cfv wcel icanth_1 cv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wcel wb icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wceq icanth_1 cv fcanth_0 wcel icanth_1 cv icanth_1 cv fcanth_1 cfv wcel wn icanth_1 cv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wcel wb icanth_1 cv icanth_1 cv fcanth_1 cfv wcel icanth_1 cv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wcel wb wn icanth_1 cv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wcel icanth_1 cv fcanth_0 wcel icanth_1 cv icanth_1 cv fcanth_1 cfv wcel wn icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_1 cv icanth_1 cv fcanth_1 cfv wcel wn icanth_0 icanth_1 cv fcanth_0 icanth_0 cv icanth_1 cv wceq icanth_0 cv icanth_0 cv fcanth_1 cfv wcel icanth_1 cv icanth_1 cv fcanth_1 cfv wcel icanth_0 cv icanth_1 cv wceq icanth_0 cv icanth_1 cv icanth_0 cv fcanth_1 cfv icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_1 cv wceq id icanth_0 cv icanth_1 cv fcanth_1 fveq2 eleq12d notbid elrab baibr icanth_1 cv icanth_1 cv fcanth_1 cfv wcel icanth_1 cv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wcel nbbn sylib icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab icanth_1 cv eleq2 nsyl nrex fcanth_0 fcanth_0 cpw fcanth_1 wfo fcanth_1 fcanth_0 wfn icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_1 crn wcel icanth_1 cv fcanth_1 cfv icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab wceq icanth_1 fcanth_0 wrex wb fcanth_0 fcanth_0 cpw fcanth_1 fofn icanth_1 fcanth_0 icanth_0 cv icanth_0 cv fcanth_1 cfv wcel wn icanth_0 fcanth_0 crab fcanth_1 fvelrnb syl mtbiri pm2.65i $.
$}
$( Cantor's theorem fails for the universal class (which is not a set but a
     proper class by ~ vprc ).  Specifically, the identity function maps the
     universe onto its power class.  Compare ~ canth that works for sets.  See
     also the remark in ~ ru about NF, in which Cantor's theorem fails for sets
     that are "too large."  This theorem gives some intuition behind that
     failure: in NF the universal class is a set, and it equals its own power
     set.  (Contributed by NM, 29-Jun-2004.) $)
${
	ncanth $p |- _I : _V -onto-> ~P _V $= cvv cvv cpw cid wf1o cvv cvv cpw cid wfo cvv cvv cpw cid wf1o cvv cvv cid wf1o f1ovi cvv cpw cvv wceq cvv cvv cpw cid wf1o cvv cvv cid wf1o wb pwv cvv cpw cvv cvv cid f1oeq3 ax-mp mpbir cvv cvv cpw cid f1ofo ax-mp $.
$}

