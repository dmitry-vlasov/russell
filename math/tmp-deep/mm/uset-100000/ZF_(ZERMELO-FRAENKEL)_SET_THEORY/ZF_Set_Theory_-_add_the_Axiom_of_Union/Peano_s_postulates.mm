
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/The_natural_numbers_(i_e__finite_ordinals).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Peano's postulates

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Zero is a natural number.  One of Peano's 5 postulates for arithmetic.
     Proposition 7.30(1) of [TakeutiZaring] p. 42.  Note:  Unlike most
     textbooks, our proofs of ~ peano1 through ~ peano5 do not use the Axiom of
     Infinity.  Unlike Takeuti and Zaring, they also do not use the Axiom of
     Regularity.  (Contributed by NM, 15-May-1994.) $)
  peano1 $p |- (/) e. om $=
    com wlim c0 com wcel limom com 0ellim ax-mp $.

  $( The successor of any natural number is a natural number.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(2) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)
  peano2 $p |- ( A e. om -> suc A e. om ) $=
    cA com wcel cA csuc com wcel cA peano2b biimpi $.

  $( The successor of any natural number is not zero.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(3) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)
  peano3 $p |- ( A e. om -> suc A =/= (/) ) $=
    cA csuc c0 wne cA com wcel cA nsuceq0 a1i $.

  $( Two natural numbers are equal iff their successors are equal, i.e. the
     successor function is one-to-one.  One of Peano's 5 postulates for
     arithmetic.  Proposition 7.30(4) of [TakeutiZaring] p. 43.  (Contributed
     by NM, 3-Sep-2003.) $)
  peano4 $p |- ( ( A e. om /\ B e. om ) -> ( suc A = suc B <-> A = B ) ) $=
    cA com wcel cA con0 wcel cB con0 wcel cA csuc cB csuc wceq cA cB wceq wb cB
    com wcel cA nnon cB nnon cA cB suc11 syl2an $.

  ${
    $d x y A $.
    $( The induction postulate: any class containing zero and closed under the
       successor operation contains all natural numbers.  One of Peano's 5
       postulates for arithmetic.  Proposition 7.30(5) of [TakeutiZaring]
       p. 43, except our proof does not require the Axiom of Infinity.  The
       more traditional statement of mathematical induction as a theorem
       schema, with a basis and an induction hypothesis, is derived from this
       theorem as theorem ~ findes .  (Contributed by NM, 18-Feb-2004.) $)
    peano5 $p |- ( ( (/) e. A /\
                 A. x e. om ( x e. A -> suc x e. A ) ) -> om C_ A ) $=
      c0 cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral wa com cA cdif
      c0 wceq com cA wss c0 cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com
      wral wa com cA cdif vy cv cin c0 wceq vy com cA cdif wrex wn com cA cdif
      c0 wceq c0 cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral wa com
      cA cdif vy cv cin c0 wceq vy com cA cdif c0 cA wcel vx cv cA wcel vx cv
      csuc cA wcel wi vx com wral wa vy cv com cA cdif wcel wa com cA cdif vy
      cv cin c0 wceq vy cv cA wcel vy cv com cA cdif wcel vy cv cA wcel wn c0
      cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral wa vy cv com cA
      eldifn adantl c0 cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral
      wa vy cv com cA cdif wcel wa com cA cdif vy cv cin c0 wceq wa vy cv vx cv
      csuc wceq vx com wrex vy cv cA wcel c0 cA wcel vx cv cA wcel vx cv csuc
      cA wcel wi vx com wral wa vy cv com cA cdif wcel wa vy cv vx cv csuc wceq
      vx com wrex com cA cdif vy cv cin c0 wceq c0 cA wcel vy cv com cA cdif
      wcel vy cv vx cv csuc wceq vx com wrex vx cv cA wcel vx cv csuc cA wcel
      wi vx com wral c0 cA wcel vy cv com cA cdif wcel wa vy cv com wcel vy cv
      c0 wne vy cv vx cv csuc wceq vx com wrex vy cv com cA cdif wcel vy cv com
      wcel c0 cA wcel vy cv com cA eldifi adantl c0 cA wcel c0 com cA cdif wcel
      wn vy cv com cA cdif wcel vy cv c0 wne c0 cA com elndif vy cv com cA cdif
      wcel c0 com cA cdif wcel vy cv c0 vy cv c0 wceq vy cv com cA cdif wcel c0
      com cA cdif wcel vy cv c0 com cA cdif eleq1 biimpcd necon3bd mpan9 vx vy
      cv nnsuc syl2anc adantlr adantr c0 cA wcel vx cv cA wcel vx cv csuc cA
      wcel wi vx com wral vy cv com cA cdif wcel com cA cdif vy cv cin c0 wceq
      vy cv vx cv csuc wceq vx com wrex vy cv cA wcel wi vx cv cA wcel vx cv
      csuc cA wcel wi vx com wral vy cv com cA cdif wcel com cA cdif vy cv cin
      c0 wceq vy cv vx cv csuc wceq vx com wrex vy cv cA wcel wi wi wi wi c0 cA
      wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral vy cv com cA cdif
      wcel com cA cdif vy cv cin c0 wceq vy cv vx cv csuc wceq vx com wrex vy
      cv cA wcel wi vx cv cA wcel vx cv csuc cA wcel wi vx com wral vy cv com
      cA cdif wcel com cA cdif vy cv cin c0 wceq wa wa vy cv vx cv csuc wceq vy
      cv cA wcel vx com vx cv cA wcel vx cv csuc cA wcel wi vx com wral vy cv
      com cA cdif wcel com cA cdif vy cv cin c0 wceq wa vx vx cv cA wcel vx cv
      csuc cA wcel wi vx com nfra1 vy cv com cA cdif wcel com cA cdif vy cv cin
      c0 wceq wa vx nfv nfan vy cv cA wcel vx nfv vx cv cA wcel vx cv csuc cA
      wcel wi vx com wral vx cv com wcel vx cv cA wcel vx cv csuc cA wcel wi vy
      cv com cA cdif wcel com cA cdif vy cv cin c0 wceq wa vy cv vx cv csuc
      wceq vy cv cA wcel wi vx cv cA wcel vx cv csuc cA wcel wi vx com rsp vy
      cv vx cv csuc wceq vx cv cA wcel vx cv csuc cA wcel wi vy cv com cA cdif
      wcel com cA cdif vy cv cin c0 wceq wa vy cv cA wcel vy cv vx cv csuc wceq
      vy cv com cA cdif wcel com cA cdif vy cv cin c0 wceq wa vx cv cA wcel vx
      cv csuc cA wcel vy cv cA wcel vy cv vx cv csuc wceq vy cv com cA cdif
      wcel com cA cdif vy cv cin c0 wceq vx cv cA wcel vy cv com cA cdif wcel
      vy cv com wcel vy cv vx cv csuc wceq com cA cdif vy cv cin c0 wceq vx cv
      cA wcel wi vy cv com cA eldifi vy cv vx cv csuc wceq vy cv com wcel vx cv
      vy cv wcel com cA cdif vy cv cin c0 wceq vx cv cA wcel wi vy cv vx cv
      csuc wceq vx cv vy cv wcel vx cv vx cv csuc wcel vx cv vx vex sucid vy cv
      vx cv csuc vx cv eleq2 mpbiri vy cv vx cv csuc wceq vy cv com wcel vx cv
      com wcel vx cv vy cv wcel com cA cdif vy cv cin c0 wceq vx cv cA wcel wi
      wi vy cv vx cv csuc wceq vy cv com wcel vx cv csuc com wcel vx cv com
      wcel vy cv vx cv csuc com eleq1 vx cv peano2b syl6bbr vx cv com wcel vx
      cv vy cv wcel com cA cdif vy cv cin c0 wceq vx cv cA wcel vx cv vy cv
      wcel com cA cdif vy cv cin c0 wceq wa vx cv com wcel vx cv com cA cdif
      wcel wn vx cv cA wcel vx cv vy cv com cA cdif minel vx cv com cA neldif
      sylan2 exp32 syl6bi mpid syl5 imp3a vx cv csuc cA wcel vy cv vx cv csuc
      wceq vy cv cA wcel vx cv csuc cA vy cv eleq1a com12 imim12d com13 sylan9
      rexlimd exp32 a1i imp41 mpd mtand nrexdv com cA cdif vy cv cin c0 wceq vy
      com cA cdif wrex com cA cdif c0 com word com cA cdif com wss com cA cdif
      c0 wne com cA cdif vy cv cin c0 wceq vy com cA cdif wrex ordom com cA
      difss vy com com cA cdif tz7.5 mp3an12 necon1bi syl com cA ssdif0 sylibr
      $.
  $}

  ${
    $d x A $.
    $( A natural number is either 0 or a successor.  (Contributed by NM,
       27-May-1998.) $)
    nn0suc $p |- ( A e. om -> ( A = (/) \/ E. x e. om A = suc x ) ) $=
      cA com wcel cA c0 wceq cA vx cv csuc wceq vx com wrex cA com wcel cA c0
      wceq wn cA vx cv csuc wceq vx com wrex cA c0 wceq wn cA com wcel cA c0
      wne cA vx cv csuc wceq vx com wrex cA c0 df-ne vx cA nnsuc sylan2br ex
      orrd $.
  $}


