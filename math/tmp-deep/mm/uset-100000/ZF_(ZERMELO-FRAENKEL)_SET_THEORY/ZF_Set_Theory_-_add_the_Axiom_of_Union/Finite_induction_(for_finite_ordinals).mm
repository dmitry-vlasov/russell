
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Peano_s_postulates.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Finite induction (for finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    find.1 $e |- ( A C_ om /\ (/) e. A /\ A. x e. A suc x e. A ) $.
    $( The Principle of Finite Induction (mathematical induction).  Corollary
       7.31 of [TakeutiZaring] p. 43.  The simpler hypothesis shown here was
       suggested in an email from "Colin" on 1-Oct-2001.  The hypothesis states
       that ` A ` is a set of natural numbers, zero belongs to ` A ` , and
       given any member of ` A ` the member's successor also belongs to
       ` A ` .  The conclusion is that every natural number is in ` A ` .
       (Contributed by NM, 22-Feb-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    find $p |- A = om $=
      cA com cA com wss c0 cA wcel vx cv csuc cA wcel vx cA wral find.1 simp1i
      c0 cA wcel vx cv cA wcel vx cv csuc cA wcel wi vx com wral wa com cA wss
      c0 cA wcel vx cv csuc cA wcel vx cA wral wa c0 cA wcel vx cv cA wcel vx
      cv csuc cA wcel wi vx com wral wa cA com wss c0 cA wcel vx cv csuc cA
      wcel vx cA wral w3a c0 cA wcel vx cv csuc cA wcel vx cA wral wa find.1 cA
      com wss c0 cA wcel vx cv csuc cA wcel vx cA wral 3simpc ax-mp vx cv csuc
      cA wcel vx cA wral vx cv cA wcel vx cv csuc cA wcel wi vx com wral c0 cA
      wcel vx cv csuc cA wcel vx cA wral vx cv cA wcel vx cv csuc cA wcel wi vx
      wal vx cv cA wcel vx cv csuc cA wcel wi vx com wral vx cv csuc cA wcel vx
      cA df-ral vx cv cA wcel vx cv csuc cA wcel wi vx com alral sylbi anim2i
      ax-mp vx cA peano5 ax-mp eqssi $.
  $}

  ${
    $d x y $.  $d x A $.  $d x ps $.  $d x ch $.  $d x th $.  $d x ta $.
    $d y ph $.
    $( Substitutions. $)
    finds.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    finds.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    finds.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    finds.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    finds.5 $e |- ps $.
    $( Induction hypothesis. $)
    finds.6 $e |- ( y e. om -> ( ch -> th ) ) $.
    $( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  Theorem
       Schema 22 of [Suppes] p. 136.  (Contributed by NM, 14-Apr-1995.) $)
    finds $p |- ( A e. om -> ta ) $=
      cA com wcel cA wph vx cab wcel wta com wph vx cab cA c0 wph vx cab wcel
      vy cv wph vx cab wcel vy cv csuc wph vx cab wcel wi vy com wral com wph
      vx cab wss c0 wph vx cab wcel wps finds.5 wph wps vx c0 0ex finds.1 elab
      mpbir vy cv wph vx cab wcel vy cv csuc wph vx cab wcel wi vy com vy cv
      com wcel wch wth vy cv wph vx cab wcel vy cv csuc wph vx cab wcel finds.6
      wph wch vx vy cv vy vex finds.2 elab wph wth vx vy cv csuc vy cv vy vex
      sucex finds.3 elab 3imtr4g rgen vy wph vx cab peano5 mp2an sseli wph wta
      vx cA com finds.4 elabg mpbid $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x ps $.  $d x ch $.  $d x th $.  $d x ta $.
    $d y ph $.
    $( Substitutions. $)
    findsg.1 $e |- ( x = B -> ( ph <-> ps ) ) $.
    findsg.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    findsg.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    findsg.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    findsg.5 $e |- ( B e. om -> ps ) $.
    $( Induction hypothesis. $)
    findsg.6 $e |- ( ( ( y e. om /\ B e. om ) /\ B C_ y ) -> ( ch -> th ) ) $.
    $( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  The
       basis of this version is an arbitrary natural number ` B ` instead of
       zero.  (Contributed by NM, 16-Sep-1995.) $)
    findsg $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) -> ta ) $=
      cA com wcel cB com wcel cB cA wss wta cB com wcel cB vx cv wss wph wi wi
      cB com wcel cB c0 wss wps wi wi cB com wcel cB vy cv wss wch wi wi cB com
      wcel cB vy cv csuc wss wth wi wi cB com wcel cB cA wss wta wi wi vx vy cA
      vx cv c0 wceq cB vx cv wss wph wi cB c0 wss wps wi cB com wcel cB c0 wceq
      vx cv c0 wceq cB vx cv wss wph wi cB c0 wss wps wi wb cB c0 wceq vx cv c0
      wceq wa cB vx cv wss cB c0 wss wph wps vx cv c0 wceq cB vx cv wss cB c0
      wss wb cB c0 wceq vx cv c0 cB sseq2 adantl cB c0 wceq vx cv c0 wceq wph
      wps wb cB c0 wceq vx cv c0 wceq vx cv cB wceq wph wps wb cB c0 vx cv
      eqeq2 findsg.1 syl6bir imp imbi12d vx cv c0 wceq cB vx cv wss wph wi cB
      c0 wss wph wi cB c0 wceq wn cB c0 wss wps wi vx cv c0 wceq cB vx cv wss
      cB c0 wss wph vx cv c0 cB sseq2 imbi1d cB c0 wceq wn cB c0 wss wph wps cB
      c0 wceq wn cB c0 wss wph wps wb cB c0 wss cB c0 wceq cB ss0 con3i pm2.21d
      pm5.74d sylan9bbr pm2.61ian imbi2d vx cv vy cv wceq cB vx cv wss wph wi
      cB vy cv wss wch wi cB com wcel vx cv vy cv wceq cB vx cv wss cB vy cv
      wss wph wch vx cv vy cv cB sseq2 findsg.2 imbi12d imbi2d vx cv vy cv csuc
      wceq cB vx cv wss wph wi cB vy cv csuc wss wth wi cB com wcel vx cv vy cv
      csuc wceq cB vx cv wss cB vy cv csuc wss wph wth vx cv vy cv csuc cB
      sseq2 findsg.3 imbi12d imbi2d vx cv cA wceq cB vx cv wss wph wi cB cA wss
      wta wi cB com wcel vx cv cA wceq cB vx cv wss cB cA wss wph wta vx cv cA
      cB sseq2 findsg.4 imbi12d imbi2d cB com wcel wps cB c0 wss findsg.5 a1d
      vy cv com wcel cB com wcel cB vy cv wss wch wi cB vy cv csuc wss wth wi
      vy cv com wcel cB com wcel cB vy cv wss wch wi cB vy cv csuc wss wth wi
      wi vy cv com wcel cB com wcel wa cB vy cv csuc wss cB vy cv csuc wceq wi
      cB vy cv wss wch wi cB vy cv csuc wss wth wi wi cB com wcel cB vy cv csuc
      wss cB vy cv csuc wceq wi cB vy cv wss wch wi cB vy cv csuc wss wth wi wi
      wi vy cv com wcel cB vy cv csuc wss cB vy cv csuc wceq wi cB vy cv wss
      wch wi cB vy cv csuc wss cB com wcel wth cB vy cv csuc wss cB vy cv csuc
      wceq wi cB vy cv csuc wss cB com wcel wth wi wi cB vy cv wss wch wi cB vy
      cv csuc wceq cB com wcel wth wi cB vy cv csuc wss cB com wcel wth wi vy
      cv csuc cB vy cv csuc cB wceq vx cv vy cv csuc wceq vx cv cB wceq wa vx
      wex cB com wcel wth wi vx vy cv csuc cB vy cv vy vex sucex eqvinc vx cv
      vy cv csuc wceq vx cv cB wceq wa cB com wcel wth wi vx vx cv cB wceq cB
      com wcel wph vx cv vy cv csuc wceq wth cB com wcel wph vx cv cB wceq wps
      findsg.5 findsg.1 syl5ibr vx cv vy cv csuc wceq wph wth findsg.3 biimpd
      sylan9r exlimiv sylbi eqcoms imim2i a1d com4r adantl cB vy cv csuc wss cB
      vy cv csuc wceq wi wn cB vy cv csuc wss cB vy cv csuc wne wa vy cv com
      wcel cB com wcel wa cB vy cv wss wch wi cB vy cv csuc wss wth wi wi cB vy
      cv csuc wss cB vy cv csuc wne wa cB vy cv csuc wss cB vy cv csuc wceq wn
      wa cB vy cv csuc wss cB vy cv csuc wceq wi wn cB vy cv csuc wne cB vy cv
      csuc wceq wn cB vy cv csuc wss cB vy cv csuc df-ne anbi2i cB vy cv csuc
      wss cB vy cv csuc wceq annim bitri vy cv com wcel cB com wcel wa cB vy cv
      csuc wss cB vy cv csuc wne wa cB vy cv wss cB vy cv wss wch wi cB vy cv
      csuc wss wth wi wi cB com wcel cB con0 wcel vy cv con0 wcel cB vy cv wss
      cB vy cv csuc wss cB vy cv csuc wne wa wb vy cv com wcel cB nnon vy cv
      nnon cB con0 wcel vy cv con0 wcel wa cB vy cv wss cB vy cv csuc wcel cB
      vy cv csuc wss cB vy cv csuc wne wa cB vy cv onsssuc vy cv con0 wcel cB
      con0 wcel vy cv csuc con0 wcel cB vy cv csuc wcel cB vy cv csuc wss cB vy
      cv csuc wne wa wb vy cv suceloni cB vy cv csuc onelpss sylan2 bitrd
      syl2anr vy cv com wcel cB com wcel wa cB vy cv wss wch wi cB vy cv wss cB
      vy cv csuc wss wth wi vy cv com wcel cB com wcel wa cB vy cv wss wch cB
      vy cv csuc wss wth wi vy cv com wcel cB com wcel wa cB vy cv wss wch wth
      cB vy cv csuc wss wth wi vy cv com wcel cB com wcel wa cB vy cv wss wch
      wth wi findsg.6 ex wth cB vy cv csuc wss ax-1 syl8 a2d com23 sylbird
      syl5bir pm2.61d ex a2d finds imp31 $.
  $}

  ${
    $d x y ta $.  $d x ps $.  $d x ch $.  $d x th $.  $d y ph $.
    $( Substitutions. $)
    finds2.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    finds2.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    finds2.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    $( Basis. $)
    finds2.4 $e |- ( ta -> ps ) $.
    $( Induction hypothesis. $)
    finds2.5 $e |- ( y e. om -> ( ta -> ( ch -> th ) ) ) $.
    $( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       29-Nov-2002.) $)
    finds2 $p |- ( x e. om -> ( ta -> ph ) ) $=
      vx cv com wcel vx cv wta wph wi vx cab wcel wta wph wi com wta wph wi vx
      cab vx cv c0 wta wph wi vx cab wcel vy cv wta wph wi vx cab wcel vy cv
      csuc wta wph wi vx cab wcel wi vy com wral com wta wph wi vx cab wss c0
      wta wph wi vx cab wcel wta wps wi finds2.4 wta wph wi wta wps wi vx c0
      0ex vx cv c0 wceq wph wps wta finds2.1 imbi2d elab mpbir vy cv wta wph wi
      vx cab wcel vy cv csuc wta wph wi vx cab wcel wi vy com vy cv com wcel
      wta wch wi wta wth wi vy cv wta wph wi vx cab wcel vy cv csuc wta wph wi
      vx cab wcel vy cv com wcel wta wch wth finds2.5 a2d wta wph wi wta wch wi
      vx vy cv vy vex vx cv vy cv wceq wph wch wta finds2.2 imbi2d elab wta wph
      wi wta wth wi vx vy cv csuc vy cv vy vex sucex vx cv vy cv csuc wceq wph
      wth wta finds2.3 imbi2d elab 3imtr4g rgen vy wta wph wi vx cab peano5
      mp2an sseli wta wph wi vx abid sylib $.
  $}

  ${
    $d x y $.  $d x ps $.  $d x ch $.  $d x th $.  $d y ph $.
    $( Substitutions. $)
    finds1.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    finds1.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    finds1.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    $( Basis. $)
    finds1.4 $e |- ps $.
    $( Induction hypothesis. $)
    finds1.5 $e |- ( y e. om -> ( ch -> th ) ) $.
    $( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       22-Mar-2006.) $)
    finds1 $p |- ( x e. om -> ph ) $=
      vx cv com wcel c0 c0 wceq wph c0 eqid wph wps wch wth c0 c0 wceq vx vy
      finds1.1 finds1.2 finds1.3 wps c0 c0 wceq finds1.4 a1i vy cv com wcel wch
      wth wi c0 c0 wceq finds1.5 a1d finds2 mpi $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    findes.1 $e |- [. (/) / x ]. ph $.
    findes.2 $e |- ( x e. om -> ( ph -> [. suc x / x ]. ph ) ) $.
    $( Finite induction with explicit substitution.  The first hypothesis is
       the basis and the second is the induction hypothesis.  Theorem Schema 22
       of [Suppes] p. 136.  See ~ tfindes for the transfinite version.
       (Contributed by Raph Levien, 9-Jul-2003.) $)
    findes $p |- ( x e. om -> ph ) $=
      wph vx vz wsb wph vx c0 wsbc wph vx vy wsb wph vx vy cv csuc wsbc wph vz
      vy vx cv wph vx vz c0 dfsbcq2 wph vz vy vx sbequ wph vx vz vy cv csuc
      dfsbcq2 wph vz vx sbequ12r findes.1 vx cv com wcel wph wph vx vx cv csuc
      wsbc wi wi vy cv com wcel wph vx vy wsb wph vx vy cv csuc wsbc wi wi vx
      vy vy cv com wcel wph vx vy wsb wph vx vy cv csuc wsbc wi vx vy cv com
      wcel vx nfv wph vx vy wsb wph vx vy cv csuc wsbc vx wph vx vy nfs1v wph
      vx vy cv csuc nfsbc1v nfim nfim vx vy weq vx cv com wcel vy cv com wcel
      wph wph vx vx cv csuc wsbc wi wph vx vy wsb wph vx vy cv csuc wsbc wi vx
      cv vy cv com eleq1 vx vy weq wph wph vx vy wsb wph vx vx cv csuc wsbc wph
      vx vy cv csuc wsbc wph vx vy sbequ12 vx vy weq vx cv csuc vy cv csuc wceq
      wph vx vx cv csuc wsbc wph vx vy cv csuc wsbc wb vx cv vy cv suceq wph vx
      vx cv csuc vy cv csuc dfsbcq syl imbi12d imbi12d findes.2 chvar finds $.
  $}



