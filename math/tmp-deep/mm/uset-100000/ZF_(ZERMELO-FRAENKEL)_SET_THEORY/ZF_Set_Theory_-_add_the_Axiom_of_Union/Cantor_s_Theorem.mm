
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Iota_properties.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Cantor's Theorem

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d x y F $.
    canth.1 $e |- A e. _V $.
    $( No set ` A ` is equinumerous to its power set (Cantor's theorem), i.e.
       no function can map ` A ` it onto its power set.  Compare Theorem 6B(b)
       of [Enderton] p. 132.  For the equinumerosity version, see ~ canth2 .
       Note that ` A ` must be a set: this theorem does not hold when ` A ` is
       too large to be a set; see ~ ncanth for a counterexample.  (Use ~ nex if
       you want the form ` -. E. f f : A -onto-> ~P A ` .)  (Contributed by NM,
       7-Aug-1994.)  (Proof shortened by Mario Carneiro, 7-Jun-2016.) $)
    canth $p |- -. F : A -onto-> ~P A $=
      cA cA cpw cF wfo vx cv vx cv cF cfv wcel wn vx cA crab cF crn wcel cA cA
      cpw cF wfo vx cv vx cv cF cfv wcel wn vx cA crab cA cpw cF crn vx cv vx
      cv cF cfv wcel wn vx cA crab cA cpw wcel vx cv vx cv cF cfv wcel wn vx cA
      crab cA wss vx cv vx cv cF cfv wcel wn vx cA ssrab2 vx cv vx cv cF cfv
      wcel wn vx cA crab cA canth.1 elpw2 mpbir cA cA cpw cF forn syl5eleqr cA
      cA cpw cF wfo vx cv vx cv cF cfv wcel wn vx cA crab cF crn wcel vy cv cF
      cfv vx cv vx cv cF cfv wcel wn vx cA crab wceq vy cA wrex vy cv cF cfv vx
      cv vx cv cF cfv wcel wn vx cA crab wceq vy cA vy cv cA wcel vy cv vy cv
      cF cfv wcel vy cv vx cv vx cv cF cfv wcel wn vx cA crab wcel wb vy cv cF
      cfv vx cv vx cv cF cfv wcel wn vx cA crab wceq vy cv cA wcel vy cv vy cv
      cF cfv wcel wn vy cv vx cv vx cv cF cfv wcel wn vx cA crab wcel wb vy cv
      vy cv cF cfv wcel vy cv vx cv vx cv cF cfv wcel wn vx cA crab wcel wb wn
      vy cv vx cv vx cv cF cfv wcel wn vx cA crab wcel vy cv cA wcel vy cv vy
      cv cF cfv wcel wn vx cv vx cv cF cfv wcel wn vy cv vy cv cF cfv wcel wn
      vx vy cv cA vx cv vy cv wceq vx cv vx cv cF cfv wcel vy cv vy cv cF cfv
      wcel vx cv vy cv wceq vx cv vy cv vx cv cF cfv vy cv cF cfv vx cv vy cv
      wceq id vx cv vy cv cF fveq2 eleq12d notbid elrab baibr vy cv vy cv cF
      cfv wcel vy cv vx cv vx cv cF cfv wcel wn vx cA crab wcel nbbn sylib vy
      cv cF cfv vx cv vx cv cF cfv wcel wn vx cA crab vy cv eleq2 nsyl nrex cA
      cA cpw cF wfo cF cA wfn vx cv vx cv cF cfv wcel wn vx cA crab cF crn wcel
      vy cv cF cfv vx cv vx cv cF cfv wcel wn vx cA crab wceq vy cA wrex wb cA
      cA cpw cF fofn vy cA vx cv vx cv cF cfv wcel wn vx cA crab cF fvelrnb syl
      mtbiri pm2.65i $.
  $}

  $( Cantor's theorem fails for the universal class (which is not a set but a
     proper class by ~ vprc ).  Specifically, the identity function maps the
     universe onto its power class.  Compare ~ canth that works for sets.  See
     also the remark in ~ ru about NF, in which Cantor's theorem fails for sets
     that are "too large."  This theorem gives some intuition behind that
     failure: in NF the universal class is a set, and it equals its own power
     set.  (Contributed by NM, 29-Jun-2004.) $)
  ncanth $p |- _I : _V -onto-> ~P _V $=
    cvv cvv cpw cid wf1o cvv cvv cpw cid wfo cvv cvv cpw cid wf1o cvv cvv cid
    wf1o f1ovi cvv cpw cvv wceq cvv cvv cpw cid wf1o cvv cvv cid wf1o wb pwv
    cvv cpw cvv cvv cid f1oeq3 ax-mp mpbir cvv cvv cpw cid f1ofo ax-mp $.


