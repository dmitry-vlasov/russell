
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Ordered-pair_class_abstractions_(cont_).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Power class of union and intersection

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y $.  $d B x y $.
    $( The power class of the intersection of two classes is the intersection
       of their power classes.  Exercise 4.12(j) of [Mendelson] p. 235.
       (Contributed by NM, 23-Nov-2003.) $)
    pwin $p |- ~P ( A i^i B ) = ( ~P A i^i ~P B ) $=
      cA cpw cB cpw cin cA cB cin cpw vx cA cpw cB cpw cA cB cin cpw vx cv cA
      wss vx cv cB wss wa vx cv cA cB cin wss vx cv cA cpw wcel vx cv cB cpw
      wcel wa vx cv cA cB cin cpw wcel vx cv cA cB ssin vx cv cA cpw wcel vx cv
      cA wss vx cv cB cpw wcel vx cv cB wss vx cv cA vx vex elpw vx cv cB vx
      vex elpw anbi12i vx cv cA cB cin vx vex elpw 3bitr4i ineqri eqcomi $.

    $( The power class of the union of two classes includes the union of their
       power classes.  Exercise 4.12(k) of [Mendelson] p. 235.  (Contributed by
       NM, 23-Nov-2003.) $)
    pwunss $p |- ( ~P A u. ~P B ) C_ ~P ( A u. B ) $=
      vx cA cpw cB cpw cun cA cB cun cpw vx cv cA wss vx cv cB wss wo vx cv cA
      cB cun wss vx cv cA cpw cB cpw cun wcel vx cv cA cB cun cpw wcel vx cv cA
      cB ssun vx cv cA cpw cB cpw cun wcel vx cv cA cpw wcel vx cv cB cpw wcel
      wo vx cv cA wss vx cv cB wss wo vx cv cA cpw cB cpw elun vx cv cA cpw
      wcel vx cv cA wss vx cv cB cpw wcel vx cv cB wss vx cv cA vx vex elpw vx
      cv cB vx vex elpw orbi12i bitri vx cv cA cB cun vx vex elpw 3imtr4i ssriv
      $.

    $( The power class of the union of two classes is a subset of the union of
       their power classes, iff one class is a subclass of the other.  Exercise
       4.12(l) of [Mendelson] p. 235.  (Contributed by NM, 23-Nov-2003.) $)
    pwssun $p |- ( ( A C_ B \/ B C_ A ) <->
               ~P ( A u. B ) C_ ( ~P A u. ~P B ) ) $=
      cA cB wss cB cA wss wo cA cB cun cpw cA cpw cB cpw cun wss cA cB wss cB
      cA wss wo cA cB cun cpw cA cpw wss cA cB cun cpw cB cpw wss wo cA cB cun
      cpw cA cpw cB cpw cun wss cB cA wss cA cB wss cA cB cun cpw cA cpw wss cA
      cB cun cpw cB cpw wss wo cB cA wss cA cB cun cpw cA cpw wss cA cB wss cA
      cB cun cpw cB cpw wss cB cA wss cA cB cun cA wceq cA cB cun cpw cA cpw
      wss cB cA ssequn2 cA cB cun cA wceq cA cB cun cpw cA cpw wceq cA cB cun
      cpw cA cpw wss cA cB cun cA pweq cA cB cun cpw cA cpw eqimss syl sylbi cA
      cB wss cA cB cun cB wceq cA cB cun cpw cB cpw wss cA cB ssequn1 cA cB cun
      cB wceq cA cB cun cpw cB cpw wceq cA cB cun cpw cB cpw wss cA cB cun cB
      pweq cA cB cun cpw cB cpw eqimss syl sylbi orim12i orcoms cA cB cun cpw
      cA cpw cB cpw ssun syl cA cB cun cpw cA cpw cB cpw cun wss cA cB wss cB
      cA wss cA cB cun cpw cA cpw cB cpw cun wss cA cB wss wn cB cA wss cA cB
      cun cpw cA cpw cB cpw cun wss cA cB wss wn wa vy cB cA cA cB cun cpw cA
      cpw cB cpw cun wss cA cB wss wn vy cv cB wcel vy cv cA wcel wi cA cB cun
      cpw cA cpw cB cpw cun wss vy cv cB wcel cA cB wss wn vy cv cA wcel cA cB
      cun cpw cA cpw cB cpw cun wss vy cv cB wcel vy cv cA wcel wn cA cB wss wi
      cA cB wss wn vy cv cA wcel wi cA cB cun cpw cA cpw cB cpw cun wss vy cv
      cB wcel vy cv cA wcel wn cA cB wss cA cB cun cpw cA cpw cB cpw cun wss vy
      cv cB wcel wa vy cv cA wcel wn wa vx cA cB cA cB cun cpw cA cpw cB cpw
      cun wss vy cv cB wcel wa vx cv cA wcel vy cv cA wcel wn vx cv cB wcel cA
      cB cun cpw cA cpw cB cpw cun wss vy cv cB wcel wa vx cv cA wcel wa vy cv
      cA wcel vx cv cB wcel cA cB cun cpw cA cpw cB cpw cun wss vy cv cB wcel
      wa vx cv cA wcel wa vx cv vy cv cpr cA cpw wcel vx cv vy cv cpr cB cpw
      wcel wo vy cv cA wcel vx cv cB wcel wo cA cB cun cpw cA cpw cB cpw cun
      wss vy cv cB wcel wa vx cv cA wcel wa vx cv vy cv cpr cA cpw cB cpw cun
      wcel vx cv vy cv cpr cA cpw wcel vx cv vy cv cpr cB cpw wcel wo cA cB cun
      cpw cA cpw cB cpw cun wss vy cv cB wcel vx cv cA wcel vx cv vy cv cpr cA
      cpw cB cpw cun wcel cA cB cun cpw cA cpw cB cpw cun wss vx cv cA wcel vy
      cv cB wcel vx cv vy cv cpr cA cpw cB cpw cun wcel vx cv cA wcel vy cv cB
      wcel wa vx cv vy cv cpr cA cB cun cpw wcel cA cB cun cpw cA cpw cB cpw
      cun wss vx cv vy cv cpr cA cpw cB cpw cun wcel vx cv cA wcel vy cv cB
      wcel wa vx cv csn vy cv csn cun cA cB cun wss vx cv vy cv cpr cA cB cun
      cpw wcel vx cv cA wcel vx cv csn cA wss vy cv csn cB wss vx cv csn vy cv
      csn cun cA cB cun wss vy cv cB wcel vx cv cA vx vex snss vy cv cB vy vex
      snss vx cv csn cA vy cv csn cB unss12 syl2anb vx cv vy cv cpr cA cB cun
      cpw wcel vx cv vy cv cpr cA cB cun wss vx cv csn vy cv csn cun cA cB cun
      wss vx cv vy cv cpr cA cB cun vx vy zfpair2 elpw vx cv vy cv cpr vx cv
      csn vy cv csn cun cA cB cun vx cv vy cv df-pr sseq1i bitr2i sylib cA cB
      cun cpw cA cpw cB cpw cun vx cv vy cv cpr ssel syl5 exp3acom23 imp31 vx
      cv vy cv cpr cA cpw cB cpw elun sylib vx cv vy cv cpr cA cpw wcel vy cv
      cA wcel vx cv vy cv cpr cB cpw wcel vx cv cB wcel vx cv vy cv cpr cA cpw
      wcel vx cv cA wcel vy cv cA wcel vx cv vy cv cpr cA cpw wcel vx cv vy cv
      cpr cA wss vx cv cA wcel vy cv cA wcel wa vx cv vy cv cpr cA vx vy
      zfpair2 elpw vx cv vy cv cA vx vex vy vex prss bitr4i simprbi vx cv vy cv
      cpr cB cpw wcel vx cv cB wcel vy cv cB wcel vx cv vy cv cpr cB cpw wcel
      vx cv vy cv cpr cB wss vx cv cB wcel vy cv cB wcel wa vx cv vy cv cpr cB
      vx vy zfpair2 elpw vx cv vy cv cB vx vex vy vex prss bitr4i simplbi
      orim12i syl ord impancom ssrdv exp31 vy cv cA wcel cA cB wss con1b syl6ib
      com23 imp ssrdv ex orrd impbii $.

    $( Break up the power class of a union into a union of smaller classes.
       (Contributed by NM, 25-Mar-2007.)  (Proof shortened by Thierry Arnoux,
       20-Dec-2016.) $)
    pwundif $p |- ~P ( A u. B ) =
                  ( ( ~P ( A u. B ) \ ~P A ) u. ~P A ) $=
      cA cB cun cpw cA cpw cdif cA cpw cun cA cB cun cpw cA cpw cun cA cB cun
      cpw cA cB cun cpw cA cpw undif1 cA cpw cA cB cun cpw wss cA cB cun cpw cA
      cpw cun cA cB cun cpw wceq cA cpw cA cB cun cpw wss cB cpw cA cB cun cpw
      wss cA cpw cA cB cun cpw wss cB cpw cA cB cun cpw wss wa cA cpw cB cpw
      cun cA cB cun cpw wss cA cB pwunss cA cpw cB cpw cA cB cun cpw unss mpbir
      simpli cA cpw cA cB cun cpw ssequn2 mpbi eqtr2i $.


    $( Break up the power class of a union into a union of smaller classes.
       Obsolete as of 20-Dec-2016.  (Contributed by NM, 25-Mar-2007.)
       (New usage is discouraged.) $)
    pwundifOLD $p |- ~P ( A u. B ) =
                  ( ( ~P ( A u. B ) \ ~P A ) u. ~P A ) $=
      vx cA cB cun cpw cA cB cun cpw cA cpw cdif cA cpw cun vx cv cA cB cun cpw
      wcel vx cv cA cB cun wss vx cv cA cB cun cpw cA cpw cdif cA cpw cun wcel
      vx cv cA cB cun vx vex elpw vx cv cA cB cun wss vx cv cA wss wn wa vx cv
      cA wss wo vx cv cA cB cun wss vx cv cA wss wo vx cv cA cB cun cpw cA cpw
      cdif cA cpw cun wcel vx cv cA cB cun wss vx cv cA cB cun wss vx cv cA wss
      wn wa vx cv cA wss wo vx cv cA cB cun wss vx cv cA wss wo vx cv cA wss wn
      vx cv cA wss wo vx cv cA wss pm2.1 vx cv cA cB cun wss vx cv cA wss wn vx
      cv cA wss ordir mpbiran2 vx cv cA cB cun cpw cA cpw cdif cA cpw cun wcel
      vx cv cA cB cun cpw cA cpw cdif wcel vx cv cA cpw wcel wo vx cv cA cB cun
      wss vx cv cA wss wn wa vx cv cA wss wo vx cv cA cB cun cpw cA cpw cdif cA
      cpw elun vx cv cA cB cun cpw cA cpw cdif wcel vx cv cA cB cun wss vx cv
      cA wss wn wa vx cv cA cpw wcel vx cv cA wss vx cv cA cB cun cpw cA cpw
      cdif wcel vx cv cA cB cun cpw wcel vx cv cA cpw wcel wn wa vx cv cA cB
      cun wss vx cv cA wss wn wa vx cv cA cB cun cpw cA cpw eldif vx cv cA cB
      cun cpw wcel vx cv cA cB cun wss vx cv cA cpw wcel wn vx cv cA wss wn vx
      cv cA cB cun vx vex elpw vx cv cA cpw wcel vx cv cA wss vx cv cA vx vex
      elpw notbii anbi12i bitri vx cv cA vx vex elpw orbi12i bitr2i vx cv cA cB
      cun wss vx cv cA wss wo vx cv cA cB cun wss vx cv cA cB cun wss vx cv cA
      cB cun wss vx cv cA wss vx cv cA cB cun wss id vx cv cA cB ssun3 jaoi vx
      cv cA cB cun wss vx cv cA wss orc impbii 3bitr3ri bitri eqriv $.
  $}

  $( The power class of the union of two classes equals the union of their
     power classes, iff one class is a subclass of the other.  Part of Exercise
     7(b) of [Enderton] p. 28.  (Contributed by NM, 23-Nov-2003.) $)
  pwun $p |- ( ( A C_ B \/ B C_ A ) <->
             ~P ( A u. B ) = ( ~P A u. ~P B ) ) $=
    cA cB cun cpw cA cpw cB cpw cun wss cA cB cun cpw cA cpw cB cpw cun wss cA
    cpw cB cpw cun cA cB cun cpw wss wa cA cB wss cB cA wss wo cA cB cun cpw cA
    cpw cB cpw cun wceq cA cpw cB cpw cun cA cB cun cpw wss cA cB cun cpw cA
    cpw cB cpw cun wss cA cB pwunss biantru cA cB pwssun cA cB cun cpw cA cpw
    cB cpw cun eqss 3bitr4i $.


