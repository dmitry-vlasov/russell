
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Founded_and_well-ordering_relations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c Ord $. $( Ordinal predicate $)
  $c On $. $( The class of ordinal numbers $)
  $c Lim $. $( Limit ordinal predicate $)
  $c suc $. $( Successor function (read:  'successor of') $)

  $( Extend the definition of a wff to include the ordinal predicate. $)
  word $a wff Ord A $.

  $( Extend the definition of a class to include the class of all ordinal
     numbers.  (The 0 in the name prevents creating a file called con.html,
     which causes problems in Windows.) $)
  con0 $a class On $.

  $( Extend the definition of a wff to include the limit ordinal predicate. $)
  wlim $a wff Lim A $.

  $( Extend class notation to include the successor function. $)
  csuc $a class suc A $.

  $( Define the ordinal predicate, which is true for a class that is transitive
     and is well-ordered by the epsilon relation.  Variant of definition of
     [BellMachover] p. 468.  (Contributed by NM, 17-Sep-1993.) $)
  df-ord $a |- ( Ord A <-> ( Tr A /\ _E We A ) ) $.

  $( Define the class of all ordinal numbers.  Definition 7.11 of
     [TakeutiZaring] p. 38.  (Contributed by NM, 5-Jun-1994.) $)
  df-on $a |- On = { x | Ord x } $.

  $( Define the limit ordinal predicate, which is true for a non-empty ordinal
     that is not a successor (i.e. that is the union of itself).  Our
     definition combines the definition of Lim of [BellMachover] p. 471 and
     Exercise 1 of [TakeutiZaring] p. 42.  See ~ dflim2 , ~ dflim3 , and dflim4
     for alternate definitions.  (Contributed by NM, 22-Apr-1994.) $)
  df-lim $a |- ( Lim A <-> ( Ord A /\ A =/= (/) /\ A = U. A ) ) $.

  $( Define the successor of a class.  When applied to an ordinal number, the
     successor means the same thing as "plus 1" (see ~ oa1suc ).  Definition
     7.22 of [TakeutiZaring] p. 41, who use "+ 1" to denote this function.  Our
     definition is a generalization to classes.  Although it is not
     conventional to use it with proper classes, it has no effect on a proper
     class ( ~ sucprc ), so that the successor of any ordinal class is still an
     ordinal class ( ~ ordsuc ), simplifying certain proofs.  Some authors
     denote the successor operation with a prime (apostrophe-like) symbol, such
     as Definition 6 of [Suppes] p. 134 and the definition of successor in
     [Mendelson] p. 246 (who uses the symbol "Suc" as a predicate to mean "is a
     successor ordinal").  The definition of successor of [Enderton] p. 68
     denotes the operation with a plus-sign superscript.  (Contributed by NM,
     30-Aug-1993.) $)
  df-suc $a |- suc A = ( A u. { A } ) $.

  $( Equality theorem for the ordinal predicate.  (Contributed by NM,
     17-Sep-1993.) $)
  ordeq $p |- ( A = B -> ( Ord A <-> Ord B ) ) $=
    cA cB wceq cA wtr cA cep wwe wa cB wtr cB cep wwe wa cA word cB word cA cB
    wceq cA wtr cB wtr cA cep wwe cB cep wwe cA cB treq cA cB cep weeq2 anbi12d
    cA df-ord cB df-ord 3bitr4g $.

  ${
    $d x A $.
    $( An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)
    elong $p |- ( A e. V -> ( A e. On <-> Ord A ) ) $=
      vx cv word cA word vx cA con0 cV vx cv cA ordeq vx df-on elab2g $.
  $}

  ${
    elon.1 $e |- A e. _V $.
    $( An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)
    elon $p |- ( A e. On <-> Ord A ) $=
      cA cvv wcel cA con0 wcel cA word wb elon.1 cA cvv elong ax-mp $.
  $}

  $( An ordinal number has the ordinal property.  (Contributed by NM,
     5-Jun-1994.) $)
  eloni $p |- ( A e. On -> Ord A ) $=
    cA con0 wcel cA word cA con0 elong ibi $.

  $( An ordinal number is an ordinal set.  (Contributed by NM, 8-Feb-2004.) $)
  elon2 $p |- ( A e. On <-> ( Ord A /\ A e. _V ) ) $=
    cA con0 wcel cA word cA cvv wcel wa cA con0 wcel cA word cA cvv wcel cA
    eloni cA con0 elex jca cA cvv wcel cA con0 wcel cA word cA cvv elong
    biimparc impbii $.

  $( Equality theorem for the limit predicate.  (Contributed by NM,
     22-Apr-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  limeq $p |- ( A = B -> ( Lim A <-> Lim B ) ) $=
    cA cB wceq cA word cA c0 wne cA cA cuni wceq w3a cB word cB c0 wne cB cB
    cuni wceq w3a cA wlim cB wlim cA cB wceq cA word cB word cA c0 wne cB c0
    wne cA cA cuni wceq cB cB cuni wceq cA cB ordeq cA cB c0 neeq1 cA cB wceq
    cA cB cA cuni cB cuni cA cB wceq id cA cB unieq eqeq12d 3anbi123d cA df-lim
    cB df-lim 3bitr4g $.

  $( Epsilon well-orders every ordinal.  Proposition 7.4 of [TakeutiZaring]
     p. 36.  (Contributed by NM, 3-Apr-1994.) $)
  ordwe $p |- ( Ord A -> _E We A ) $=
    cA word cA wtr cA cep wwe cA df-ord simprbi $.

  $( An ordinal class is transitive.  (Contributed by NM, 3-Apr-1994.) $)
  ordtr $p |- ( Ord A -> Tr A ) $=
    cA word cA wtr cA cep wwe cA df-ord simplbi $.

  $( Epsilon is well-founded on an ordinal class.  (Contributed by NM,
     22-Apr-1994.) $)
  ordfr $p |- ( Ord A -> _E Fr A ) $=
    cA word cA cep wwe cA cep wfr cA ordwe cA cep wefr syl $.

  $( An element of an ordinal class is a subset of it.  (Contributed by NM,
     30-May-1994.) $)
  ordelss $p |- ( ( Ord A /\ B e. A ) -> B C_ A ) $=
    cA word cA wtr cB cA wcel cB cA wss cA ordtr cA wtr cB cA wcel cB cA wss cA
    cB trss imp sylan $.

  $( A transitive subclass of an ordinal class is ordinal.  (Contributed by NM,
     29-May-1994.) $)
  trssord $p |- ( ( Tr A /\ A C_ B /\ Ord B ) -> Ord A ) $=
    cA wtr cA cB wss cB word w3a cA wtr cA cep wwe wa cA word cA wtr cA cB wss
    cB word cA wtr cA cep wwe wa cA cB wss cB word wa cA cep wwe cA wtr cB word
    cA cB wss cB cep wwe cA cep wwe cB ordwe cA cB wss cB cep wwe cA cep wwe cA
    cB cep wess imp sylan2 anim2i 3impb cA df-ord sylibr $.

  $( Epsilon irreflexivity of ordinals: no ordinal class is a member of
     itself.  Theorem 2.2(i) of [BellMachover] p. 469, generalized to classes.
     We prove this without invoking the Axiom of Regularity.  (Contributed by
     NM, 2-Jan-1994.) $)
  ordirr $p |- ( Ord A -> -. A e. A ) $=
    cA word cA cep wfr cA cA wcel wn cA ordfr cA efrirr syl $.

  $( A member of an ordinal class is not equal to it.  (Contributed by NM,
     25-May-1998.) $)
  nordeq $p |- ( ( Ord A /\ B e. A ) -> A =/= B ) $=
    cA word cB cA wcel cA cB wne cA word cB cA wcel cA cB cA word cA cA wcel wn
    cA cB wceq cB cA wcel wn cA ordirr cA cB wceq cA cA wcel cB cA wcel cA cB
    cA eleq1 notbid syl5ibcom necon2ad imp $.

  $( An ordinal class cannot an element of one of its members.  Variant of
     first part of Theorem 2.2(vii) of [BellMachover] p. 469.  (Contributed by
     NM, 3-Apr-1994.) $)
  ordn2lp $p |- ( Ord A -> -. ( A e. B /\ B e. A ) ) $=
    cA word cA cB wcel cB cA wcel wa cA cA wcel cA ordirr cA word cA wtr cA cB
    wcel cB cA wcel wa cA cA wcel wi cA ordtr cA cA cB trel syl mtod $.

  ${
    $d x B $.
    $( A subclass (possibly proper) of an ordinal class has a minimal element.
       Proposition 7.5 of [TakeutiZaring] p. 36.  (Contributed by NM,
       18-Feb-2004.)  (Revised by David Abernethy, 16-Mar-2011.) $)
    tz7.5 $p |- ( ( Ord A /\ B C_ A /\ B =/= (/) ) ->
               E. x e. B ( B i^i x ) = (/) ) $=
      cA word cA cep wwe cB cA wss cB c0 wne cB vx cv cin c0 wceq vx cB wrex cA
      ordwe vx cA cB wefrc syl3an1 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( An element of an ordinal class is ordinal.  Proposition 7.6 of
       [TakeutiZaring] p. 36.  (Contributed by NM, 23-Apr-1994.) $)
    ordelord $p |- ( ( Ord A /\ B e. A ) -> Ord B ) $=
      cA word cB cA wcel cB word cA word vx cv cA wcel wa vx cv word wi cA word
      cB cA wcel wa cB word wi vx cB cA vx cv cB wceq cA word vx cv cA wcel wa
      cA word cB cA wcel wa vx cv word cB word vx cv cB wceq vx cv cA wcel cB
      cA wcel cA word vx cv cB cA eleq1 anbi2d vx cv cB ordeq imbi12d cA word
      vx cv cA wcel wa vx cv wtr vx cv cep wwe vx cv word cA word vx cv cA wcel
      wa vz cv vy cv wcel vy cv vx cv wcel wa vz cv vx cv wcel wi vy wal vz wal
      vx cv wtr cA word vx cv cA wcel wa vz cv vy cv wcel vy cv vx cv wcel wa
      vz cv vx cv wcel wi vz vy cA word vx cv cA wcel wa vz cv vy cv wcel vy cv
      vx cv wcel wa vz cv vx cv wcel cA word vx cv cA wcel wa vz cv vy cv wcel
      vy cv vx cv wcel wa vz cv vy cv wcel vy cv vx cv wcel wa vz cv vx cv wcel
      wi cA word vx cv cA wcel wa vz cv vy cv wcel vy cv vx cv wcel wa wa cA
      word vz cv cA wcel vy cv cA wcel vx cv cA wcel vz cv vy cv wcel vy cv vx
      cv wcel wa vz cv vx cv wcel wi cA word vx cv cA wcel vz cv vy cv wcel vy
      cv vx cv wcel wa simpll cA word vx cv cA wcel vz cv vy cv wcel vy cv vx
      cv wcel wa vz cv cA wcel vx cv cA wcel vz cv vy cv wcel vy cv vx cv wcel
      wa wa vz cv vy cv wcel vy cv vx cv wcel vx cv cA wcel w3a cA word vz cv
      cA wcel vz cv vy cv wcel vy cv vx cv wcel vx cv cA wcel w3a vx cv cA wcel
      vz cv vy cv wcel vy cv vx cv wcel w3a vx cv cA wcel vz cv vy cv wcel vy
      cv vx cv wcel wa wa vx cv cA wcel vz cv vy cv wcel vy cv vx cv wcel
      3anrot vx cv cA wcel vz cv vy cv wcel vy cv vx cv wcel 3anass bitr3i cA
      word cA wtr vz cv vy cv wcel vy cv vx cv wcel vx cv cA wcel w3a vz cv cA
      wcel wi cA ordtr cA vz cv vy cv vx cv trel3 syl syl5bir impl cA word vx
      cv cA wcel wa vy cv vx cv wcel vy cv cA wcel vz cv vy cv wcel cA word vx
      cv cA wcel vy cv vx cv wcel vy cv cA wcel cA word vy cv vx cv wcel vx cv
      cA wcel vy cv cA wcel cA word cA wtr vy cv vx cv wcel vx cv cA wcel wa vy
      cv cA wcel wi cA ordtr cA vy cv vx cv trel syl exp3acom23 imp31 adantrl
      cA word vx cv cA wcel vz cv vy cv wcel vy cv vx cv wcel wa simplr cA word
      cA cep wwe vz cv cA wcel vy cv cA wcel vx cv cA wcel w3a vz cv vy cv wcel
      vy cv vx cv wcel wa vz cv vx cv wcel wi cA ordwe vz vy vx cA wetrep sylan
      syl13anc ex pm2.43d alrimivv vz vy vx cv dftr2 sylibr cA word vx cv cA
      wcel vx cv cep wwe cA word vx cv cA wcel vx cv cA wss vx cv cep wwe cA
      word cA wtr vx cv cA wcel vx cv cA wss wi cA ordtr cA vx cv trss syl cA
      word cA cep wwe vx cv cA wss vx cv cep wwe cA ordwe vx cv cA cep wess
      syl5com syld imp vx cv df-ord sylanbrc vtoclg anabsi7 $.
  $}

  ${
    $d x y $.
    $( The class of all ordinal numbers is transitive.  (Contributed by NM,
       4-May-2009.) $)
    tron $p |- Tr On $=
      con0 wtr vx cv con0 wss vx con0 vx con0 dftr3 vx cv con0 wcel vy vx cv
      con0 vx cv con0 wcel vy cv vx cv wcel vy cv word vy cv con0 wcel vx cv
      con0 wcel vy cv vx cv wcel vy cv word vx cv con0 wcel vx cv word vy cv vx
      cv wcel vy cv word vx cv vx vex elon vx cv vy cv ordelord sylanb ex vy cv
      vy vex elon syl6ibr ssrdv mprgbir $.
  $}

  $( An element of an ordinal class is an ordinal number.  (Contributed by NM,
     26-Oct-2003.) $)
  ordelon $p |- ( ( Ord A /\ B e. A ) -> B e. On ) $=
    cA word cB cA wcel wa cB con0 wcel cB word cA cB ordelord cB cA wcel cB
    con0 wcel cB word wb cA word cB cA elong adantl mpbird $.

  $( An element of an ordinal number is an ordinal number.  Theorem 2.2(iii) of
     [BellMachover] p. 469.  (Contributed by NM, 26-Oct-2003.) $)
  onelon $p |- ( ( A e. On /\ B e. A ) -> B e. On ) $=
    cA con0 wcel cA word cB cA wcel cB con0 wcel cA eloni cA cB ordelon sylan
    $.

  ${
    $d x y A $.  $d x y B $.
    $( Proposition 7.7 of [TakeutiZaring] p. 37.  (Contributed by NM,
       5-May-1994.) $)
    tz7.7 $p |- ( ( Ord A /\ Tr B ) ->
                ( B e. A <-> ( B C_ A /\ B =/= A ) ) ) $=
      cA word cB wtr wa cB cA wcel cB cA wss cB cA wne wa cA word cB cA wcel cB
      cA wss cB cA wne wa wi cB wtr cA word cA wtr cA cep wfr cB cA wcel cB cA
      wss cB cA wne wa wi cA ordtr cA ordfr cA wtr cA cep wfr cB cA wcel cB cA
      wss cB cA wne wa cA cB tz7.2 3exp sylc adantr cA word cB wtr wa cB cA wss
      cB cA wne cB cA wcel cA word cB wtr wa cB cA wss cB cA wne cB cA wcel wi
      cA word cB wtr wa cB cA wss cB cA wss cB cA wne cB cA wcel cB cA wss cB
      cA wne wa cA cB cdif c0 wne cA word cB wtr wa cB cA wss cB cA wcel cB cA
      pssdifn0 cA word cB wtr wa cB cA wss cA cB cdif c0 wne cB cA wcel wi wi
      cA word cB wtr wa cA word cB cA wss cA cB cdif c0 wne cB cA wcel wi wi cB
      wtr cA word cB wtr wa cB cA wss cA word cA cB cdif c0 wne cB cA wcel wi
      cA word cB wtr wa cB cA wss cA word cA cB cdif c0 wne cB cA wcel cA word
      cA cB cdif c0 wne wa cA cB cdif vx cv cin c0 wceq vx cA cB cdif wrex cA
      word cB wtr wa cB cA wss wa cB cA wcel cA word cA cB cdif cA wss cA cB
      cdif c0 wne cA cB cdif vx cv cin c0 wceq vx cA cB cdif wrex cA cB difss
      vx cA cA cB cdif tz7.5 mp3an2 cA word cB wtr wa cB cA wss wa cA cB cdif
      vx cv cin c0 wceq cB cA wcel vx cA cB cdif cA word cB wtr wa cB cA wss wa
      vx cv cA cB cdif wcel cA cB cdif vx cv cin c0 wceq cB cA wcel cA word cB
      wtr wa cB cA wss wa vx cv cA cB cdif wcel cA cB cdif vx cv cin c0 wceq wa
      wa vx cv cB cA cA word cB wtr wa cB cA wss wa vx cv cA cB cdif wcel cA cB
      cdif vx cv cin c0 wceq wa wa vx cv cB cA word cB wtr wa cB cA wss wa vx
      cv cA cB cdif wcel cA cB cdif vx cv cin c0 wceq vx cv cB wss cA word vx
      cv cA cB cdif wcel cA cB cdif vx cv cin c0 wceq vx cv cB wss wi wi cB wtr
      cB cA wss cA word cA wtr vx cv cA cB cdif wcel cA cB cdif vx cv cin c0
      wceq vx cv cB wss wi wi cA ordtr vx cv cA cB cdif wcel vx cv cA wcel cA
      wtr vx cv cA wss cA cB cdif vx cv cin c0 wceq vx cv cB wss wi vx cv cA cB
      eldifi cA vx cv trss cA cB cdif vx cv cin c0 wceq vx cv cA wss vx cv cB
      wss cA cB vx cv difin0ss com12 syl56 syl ad2antrr imp32 cA word cB wtr wa
      cB cA wss wa vx cv cA cB cdif wcel cB vx cv wss cA cB cdif vx cv cin c0
      wceq cA word cB wtr wa cB cA wss wa vx cv cA cB cdif wcel wa vy cB vx cv
      cA word cB wtr wa cB cA wss vx cv cA cB cdif wcel vy cv cB wcel vy cv vx
      cv wcel wi cA word cB wtr wa cB cA wss vy cv cB wcel vx cv cA cB cdif
      wcel vy cv vx cv wcel cA word cB wtr wa cB cA wss vy cv cB wcel vx cv cA
      cB cdif wcel vy cv vx cv wcel cA word cB wtr wa cB cA wss vy cv cB wcel
      wa vx cv cA cB cdif wcel wa wa vy cv vx cv wcel vy cv vx cv wceq vx cv vy
      cv wcel cB cA wss vy cv cB wcel wa vx cv cA cB cdif wcel wa vy cv vx cv
      wceq wn cA word cB wtr wa vy cv cB wcel vx cv cA cB cdif wcel vy cv vx cv
      wceq wn cB cA wss vy cv cB wcel vx cv cA cB cdif wcel vy cv vx cv wceq wn
      vy cv cB wcel vy cv vx cv wceq vx cv cB wcel vx cv cA cB cdif wcel vy cv
      vx cv wceq vy cv cB wcel vx cv cB wcel vy cv vx cv cB eleq1 biimpcd vx cv
      cA cB eldifn nsyli imp adantll adantl cB wtr cB cA wss vy cv cB wcel wa
      vx cv cA cB cdif wcel wa vx cv vy cv wcel wn cA word cB wtr cB cA wss vy
      cv cB wcel wa vx cv cA cB cdif wcel vx cv vy cv wcel wn cB wtr vy cv cB
      wcel vx cv cA cB cdif wcel vx cv vy cv wcel wn wi cB cA wss cB wtr vy cv
      cB wcel vx cv cA cB cdif wcel vx cv vy cv wcel wn wi cB wtr vy cv cB wcel
      wa vx cv vy cv wcel vx cv cB wcel vx cv cA cB cdif wcel cB wtr vy cv cB
      wcel vx cv vy cv wcel vx cv cB wcel wi cB wtr vx cv vy cv wcel vy cv cB
      wcel vx cv cB wcel cB vx cv vy cv trel exp3acom23 imp vx cv cA cB eldifn
      nsyli ex adantld imp32 adantll cA word cB cA wss vy cv cB wcel wa vx cv
      cA cB cdif wcel wa vy cv vx cv wcel vy cv vx cv wceq vx cv vy cv wcel w3o
      cB wtr cA word cA cep wwe vy cv cA wcel vx cv cA wcel wa vy cv vx cv wcel
      vy cv vx cv wceq vx cv vy cv wcel w3o cB cA wss vy cv cB wcel wa vx cv cA
      cB cdif wcel wa cA ordwe cB cA wss vy cv cB wcel wa vy cv cA wcel vx cv
      cA cB cdif wcel vx cv cA wcel cB cA vy cv ssel2 vx cv cA cB eldifi
      anim12i vy vx cA wecmpep syl2an adantlr ecase23d exp44 com34 imp31 ssrdv
      adantrr eqssd vx cv cA cB cdif wcel vx cv cA wcel cA word cB wtr wa cB cA
      wss wa cA cB cdif vx cv cin c0 wceq vx cv cA cB eldifi ad2antrl eqeltrrd
      exp32 rexlimdv syl5 exp4b com23 adantrd pm2.43i syl7 exp4a pm2.43d imp3a
      impbid $.
  $}

  $( Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     25-Nov-1995.) $)
  ordelssne $p |- ( ( Ord A /\ Ord B ) ->
              ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $=
    cB word cA word cA cB wcel cA cB wss cA cB wne wa wb cA word cB word cA wtr
    cA cB wcel cA cB wss cA cB wne wa wb cA ordtr cB cA tz7.7 sylan2 ancoms $.

  $( Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     17-Jun-1998.) $)
  ordelpss $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> A C. B ) ) $=
    cA word cB word wa cA cB wcel cA cB wss cA cB wne wa cA cB wpss cA cB
    ordelssne cA cB df-pss syl6bbr $.

  $( For ordinal classes, subclass is equivalent to membership or equality.
     (Contributed by NM, 25-Nov-1995.)  (Proof shortened by Andrew Salmon,
     25-Jul-2011.) $)
  ordsseleq $p |- ( ( Ord A /\ Ord B ) ->
                  ( A C_ B <-> ( A e. B \/ A = B ) ) ) $=
    cA word cB word wa cA cB wcel cA cB wceq wo cA cB wpss cA cB wceq wo cA cB
    wss cA word cB word wa cA cB wcel cA cB wpss cA cB wceq cA cB ordelpss
    orbi1d cA cB sspss syl6rbbr $.

  $( The intersection of two ordinal classes is ordinal.  Proposition 7.9 of
     [TakeutiZaring] p. 37.  (Contributed by NM, 9-May-1994.) $)
  ordin $p |- ( ( Ord A /\ Ord B ) -> Ord ( A i^i B ) ) $=
    cA word cB word cA cB cin wtr cA cB cin word cA word cA wtr cB wtr cA cB
    cin wtr cB word cA ordtr cB ordtr cA cB trin syl2an cA cB cin wtr cA cB cin
    cB wss cB word cA cB cin word cA cB inss2 cA cB cin cB trssord mp3an2
    sylancom $.

  ${
    $d x y A $.  $d x y B $.
    $( The intersection of two ordinal numbers is an ordinal number.
       (Contributed by NM, 7-Apr-1995.) $)
    onin $p |- ( ( A e. On /\ B e. On ) -> ( A i^i B ) e. On ) $=
      cA con0 wcel cB con0 wcel wa cA cB cin con0 wcel cA cB cin word cA con0
      wcel cA word cB word cA cB cin word cB con0 wcel cA eloni cB eloni cA cB
      ordin syl2an cA con0 wcel cB con0 wcel wa cA con0 wcel cA cB cin cvv wcel
      cA cB cin con0 wcel cA cB cin word wb cA con0 wcel cB con0 wcel simpl cA
      cB con0 inex1g cA cB cin cvv elong 3syl mpbird $.
  $}

  $( A trichotomy law for ordinals.  Proposition 7.10 of [TakeutiZaring]
     p. 38.  (Contributed by NM, 10-May-1994.)  (Proof shortened by Andrew
     Salmon, 25-Jul-2011.) $)
  ordtri3or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ A = B \/ B e. A ) ) $=
    cA word cB word wa cA cB wcel cA cB wceq cB cA wcel w3o cA cB wpss cA cB
    wceq cB cA wpss w3o cA word cB word wa cA cB wss cB cA wss wo cA cB wpss cA
    cB wceq cB cA wpss w3o cA word cB word wa cA cB cin cA wcel wn cB cA cin cB
    wcel wn wo cA cB wss cB cA wss wo cA word cB word wa cA cB cin cA cB cin
    wcel wn cA cB cin cA wcel wn cB cA cin cB wcel wn wo cA word cB word wa cA
    cB cin word cA cB cin cA cB cin wcel wn cA cB ordin cA cB cin ordirr syl cA
    cB cin cA wcel cB cA cin cB wcel wa cA cB cin cA wcel wn cB cA cin cB wcel
    wn wo cA cB cin cA cB cin wcel cA cB cin cA wcel cB cA cin cB wcel ianor cA
    cB cin cA cB cin wcel cA cB cin cA wcel cA cB cin cB wcel wa cA cB cin cA
    wcel cB cA cin cB wcel wa cA cB cin cA cB elin cA cB cin cB wcel cB cA cin
    cB wcel cA cB cin cA wcel cA cB cin cB cA cin cB cA cB incom eleq1i anbi2i
    bitri xchnxbir sylib cA word cB word wa cA cB cin cA wcel wn cA cB wss cB
    cA cin cB wcel wn cB cA wss cA word cB word wa cA cB cin cA wcel wn cA cB
    cin cA wceq cA cB wss cA word cB word wa cA cB cin cA wcel cA cB cin cA
    wceq cA word cB word cA cB cin cA wcel cA cB cin cA wceq wo cA word cB word
    wa cA cB cin word cA word cA cB cin cA wcel cA cB cin cA wceq wo cA cB
    ordin cA cB cin word cA word wa cA cB cin cA wss cA cB cin cA wcel cA cB
    cin cA wceq wo cA cB inss1 cA cB cin cA ordsseleq mpbii sylan anabss1 ord
    cA cB df-ss syl6ibr cA word cB word wa cB cA cin cB wcel wn cB cA cin cB
    wceq cB cA wss cA word cB word wa cB cA cin cB wcel cB cA cin cB wceq cA
    word cB word cB cA cin cB wcel cB cA cin cB wceq wo cB word cA word wa cB
    cA cin word cB word cB cA cin cB wcel cB cA cin cB wceq wo cB cA ordin cB
    cA cin word cB word wa cB cA cin cB wss cB cA cin cB wcel cB cA cin cB wceq
    wo cB cA inss1 cB cA cin cB ordsseleq mpbii sylan anabss4 ord cB cA df-ss
    syl6ibr orim12d mpd cA cB sspsstri sylib cA word cB word wa cA cB wcel cA
    cB wpss cA cB wceq cA cB wceq cB cA wcel cB cA wpss cA cB ordelpss cA word
    cB word wa cA cB wceq biidd cB word cA word cB cA wcel cB cA wpss wb cB cA
    ordelpss ancoms 3orbi123d mpbird $.

  $( A trichotomy law for ordinals.  (Contributed by NM, 25-Mar-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
  ordtri1 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> -. B e. A ) ) $=
    cA word cB word wa cA cB wss cA cB wcel cA cB wceq wo cB cA wcel wn cA cB
    ordsseleq cA word cB word wa cA cB wcel cA cB wceq wo cB cA wcel wn cA word
    cA cB wcel cB cA wcel wn cB word cA cB wceq cA word cA cB wcel cB cA wcel
    wa wn cA cB wcel cB cA wcel wn wi cA cB ordn2lp cA cB wcel cB cA wcel imnan
    sylibr cB word cB cA wcel wn cA cB wceq cB cB wcel wn cB ordirr cA cB wceq
    cB cA wcel cB cB wcel cA cB cB eleq2 notbid syl5ibrcom jaao cA word cB word
    wa cB cA wcel cA cB wcel cA cB wceq wo cA word cB word wa cA cB wcel cA cB
    wceq wo cB cA wcel cA word cB word wa cA cB wcel cA cB wceq cB cA wcel w3o
    cA cB wcel cA cB wceq wo cB cA wcel wo cA cB ordtri3or cA cB wcel cA cB
    wceq cB cA wcel df-3or sylib orcomd ord impbid bitrd $.

  $( A trichotomy law for ordinal numbers.  (Contributed by NM, 6-Nov-2003.) $)
  ontri1 $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> -. B e. A ) ) $=
    cA con0 wcel cA word cB word cA cB wss cB cA wcel wn wb cB con0 wcel cA
    eloni cB eloni cA cB ordtri1 syl2an $.

  $( A trichotomy law for ordinals.  (Contributed by NM, 25-Nov-1995.) $)
  ordtri2 $p |- ( ( Ord A /\ Ord B ) ->
               ( A e. B <-> -. ( A = B \/ B e. A ) ) ) $=
    cA word cB word wa cA cB wceq cB cA wcel wo cA cB wcel cB word cA word cA
    cB wceq cB cA wcel wo cA cB wcel wn wb cB word cA word wa cB cA wss cA cB
    wceq cB cA wcel wo cA cB wcel wn cB word cA word wa cB cA wss cB cA wcel cB
    cA wceq wo cA cB wceq cB cA wcel wo cB cA ordsseleq cB cA wcel cB cA wceq
    wo cB cA wcel cA cB wceq wo cA cB wceq cB cA wcel wo cB cA wceq cA cB wceq
    cB cA wcel cB cA eqcom orbi2i cB cA wcel cA cB wceq orcom bitri syl6bb cB
    cA ordtri1 bitr3d ancoms con2bid $.

  $( A trichotomy law for ordinals.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
  ordtri3 $p |- ( ( Ord A /\ Ord B ) ->
               ( A = B <-> -. ( A e. B \/ B e. A ) ) ) $=
    cA word cB word wa cA cB wceq cA cB wcel cB cA wcel wo wn cA word cB word
    wa cA cB wceq cA cB wcel wn cB cA wcel wn wa cA cB wcel cB cA wcel wo wn cA
    cB wceq cA word cB word wa cA cB wcel wn cB cA wcel wn wa cA cB wceq cA
    word cA cB wcel wn cB word cB cA wcel wn cA word cA cA wcel wn cA cB wceq
    cA cB wcel wn cA ordirr cA cB wceq cA cA wcel cA cB wcel cA cB cA eleq2
    notbid syl5ib cB word cB cA wcel wn cA cB wceq cB cB wcel wn cB ordirr cA
    cB wceq cB cA wcel cB cB wcel cA cB cB eleq2 notbid syl5ibr anim12d com12
    cA cB wcel cB cA wcel pm4.56 syl6ib cA word cB word wa cA cB wcel cB cA
    wcel wo cA cB wceq cA word cB word wa cA cB wcel cA cB wceq wo cB cA wcel
    wo cA cB wcel cB cA wcel wo cA cB wceq wo cA word cB word wa cA cB wcel cA
    cB wceq cB cA wcel w3o cA cB wcel cA cB wceq wo cB cA wcel wo cA cB
    ordtri3or cA cB wcel cA cB wceq cB cA wcel df-3or sylib cA cB wcel cA cB
    wceq cB cA wcel or32 sylib ord impbid $.

  $( A trichotomy law for ordinals.  (Contributed by NM, 1-Nov-2003.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
  ordtri4 $p |- ( ( Ord A /\ Ord B ) ->
               ( A = B <-> ( A C_ B /\ -. A e. B ) ) ) $=
    cA cB wceq cA cB wss cB cA wss wa cA word cB word wa cA cB wss cA cB wcel
    wn wa cA cB eqss cA word cB word wa cB cA wss cA cB wcel wn cA cB wss cB
    word cA word cB cA wss cA cB wcel wn wb cB cA ordtri1 ancoms anbi2d syl5bb
    $.

  $( An ordinal class and its singleton are disjoint.  (Contributed by NM,
     19-May-1998.) $)
  orddisj $p |- ( Ord A -> ( A i^i { A } ) = (/) ) $=
    cA word cA cA wcel wn cA cA csn cin c0 wceq cA ordirr cA cA disjsn sylibr
    $.

  ${
    $d x y z $.
    $( The ordinal class is well-founded.  This lemma is needed for ~ ordon in
       order to eliminate the need for the Axiom of Regularity.  (Contributed
       by NM, 17-May-1994.) $)
    onfr $p |- _E Fr On $=
      con0 cep wfr vx cv con0 wss vx cv c0 wne wa vx cv vz cv cin c0 wceq vz vx
      cv wrex wi vx vx vz con0 dfepfr vx cv con0 wss vx cv c0 wne vx cv vz cv
      cin c0 wceq vz vx cv wrex vx cv c0 wne vy cv vx cv wcel vy wex vx cv con0
      wss vx cv vz cv cin c0 wceq vz vx cv wrex vy vx cv n0 vx cv con0 wss vy
      cv vx cv wcel vx cv vz cv cin c0 wceq vz vx cv wrex vy vx cv con0 wss vy
      cv vx cv wcel vx cv vz cv cin c0 wceq vz vx cv wrex vx cv con0 wss vy cv
      vx cv wcel wa vx cv vz cv cin c0 wceq vz vx cv wrex vx cv vy cv cin c0 vy
      cv vx cv wcel vx cv vy cv cin c0 wceq vx cv vz cv cin c0 wceq vz vx cv
      wrex vx cv con0 wss vx cv vz cv cin c0 wceq vx cv vy cv cin c0 wceq vz vy
      cv vx cv vz cv vy cv wceq vx cv vz cv cin vx cv vy cv cin c0 vz cv vy cv
      vx cv ineq2 eqeq1d rspcev adantll vx cv con0 wss vy cv vx cv wcel wa vx
      cv vy cv cin c0 wne wa vx cv vz cv cin c0 wceq vz vx cv vy cv cin wrex vx
      cv vz cv cin c0 wceq vz vx cv wrex vx cv con0 wss vy cv vx cv wcel wa vx
      cv vy cv cin c0 wne wa vx cv vy cv cin vz cv cin c0 wceq vz vx cv vy cv
      cin wrex vx cv vz cv cin c0 wceq vz vx cv vy cv cin wrex vx cv con0 wss
      vy cv vx cv wcel wa vy cv cep wfr vx cv vy cv cin c0 wne vx cv vy cv cin
      vz cv cin c0 wceq vz vx cv vy cv cin wrex vx cv con0 wss vy cv vx cv wcel
      wa vy cv word vy cv cep wfr vx cv con0 wss vy cv vx cv wcel wa vy cv con0
      wcel vy cv word vx cv con0 vy cv ssel2 vy cv eloni syl vy cv ordfr syl vy
      cv cep wfr vx cv vy cv cin vy cv wss vx cv vy cv cin c0 wne vx cv vy cv
      cin vz cv cin c0 wceq vz vx cv vy cv cin wrex vx cv vy cv inss2 vz vy cv
      vx cv vy cv cin vx cv vy cv vx vex inex1 epfrc mp3an2 sylan vx cv con0
      wss vy cv vx cv wcel wa vx cv vy cv cin vz cv cin c0 wceq vz vx cv vy cv
      cin wrex vx cv vz cv cin c0 wceq vz vx cv vy cv cin wrex wb vx cv vy cv
      cin c0 wne vx cv con0 wss vy cv vx cv wcel wa vx cv vy cv cin vz cv cin
      c0 wceq vx cv vz cv cin c0 wceq vz vx cv vy cv cin vx cv con0 wss vy cv
      vx cv wcel wa vz cv vx cv vy cv cin wcel wa vx cv vy cv cin vz cv cin vx
      cv vz cv cin c0 vx cv con0 wss vy cv vx cv wcel wa vz cv vx cv vy cv cin
      wcel wa vx cv vy cv cin vz cv cin vx cv vy cv vz cv cin cin vx cv vz cv
      cin vx cv vy cv vz cv inass vx cv con0 wss vy cv vx cv wcel wa vz cv vx
      cv vy cv cin wcel wa vy cv vz cv cin vz cv vx cv vx cv con0 wss vy cv vx
      cv wcel wa vz cv vx cv vy cv cin wcel wa vz cv vy cv wss vy cv vz cv cin
      vz cv wceq vx cv con0 wss vy cv vx cv wcel wa vz cv vx cv vy cv cin wcel
      wa vy cv word vz cv vy cv wcel vz cv vy cv wss vx cv con0 wss vy cv vx cv
      wcel wa vy cv word vz cv vx cv vy cv cin wcel vx cv con0 wss vy cv vx cv
      wcel wa vy cv con0 wcel vy cv word vx cv con0 vy cv ssel2 vy cv eloni syl
      adantr vx cv con0 wss vy cv vx cv wcel wa vz cv vx cv vy cv cin wcel wa
      vx cv vy cv cin vy cv vz cv vx cv vy cv inss2 vx cv con0 wss vy cv vx cv
      wcel wa vz cv vx cv vy cv cin wcel simpr sseldi vy cv vz cv ordelss
      syl2anc vz cv vy cv dfss1 sylib ineq2d syl5eq eqeq1d rexbidva adantr
      mpbid vx cv vy cv cin vx cv wss vx cv vz cv cin c0 wceq vz vx cv vy cv
      cin wrex vx cv vz cv cin c0 wceq vz vx cv wrex wi vx cv vy cv inss1 vx cv
      vz cv cin c0 wceq vz vx cv vy cv cin vx cv ssrexv ax-mp syl pm2.61dane ex
      exlimdv syl5bi imp mpgbir $.
  $}

  $( Relationship between membership and proper subset of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)
  onelpss $p |- ( ( A e. On /\ B e. On ) ->
               ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $=
    cA con0 wcel cA word cB word cA cB wcel cA cB wss cA cB wne wa wb cB con0
    wcel cA eloni cB eloni cA cB ordelssne syl2an $.

  $( Relationship between subset and membership of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)
  onsseleq $p |- ( ( A e. On /\ B e. On ) ->
                 ( A C_ B <-> ( A e. B \/ A = B ) ) ) $=
    cA con0 wcel cA word cB word cA cB wss cA cB wcel cA cB wceq wo wb cB con0
    wcel cA eloni cB eloni cA cB ordsseleq syl2an $.

  $( An element of an ordinal number is a subset of the number.  (Contributed
     by NM, 5-Jun-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  onelss $p |- ( A e. On -> ( B e. A -> B C_ A ) ) $=
    cA con0 wcel cA word cB cA wcel cB cA wss wi cA eloni cA word cB cA wcel cB
    cA wss cA cB ordelss ex syl $.

  $( Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.) $)
  ordtr1 $p |- ( Ord C -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $=
    cC word cC wtr cA cB wcel cB cC wcel wa cA cC wcel wi cC ordtr cC cA cB
    trel syl $.

  $( Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  ordtr2 $p |- ( ( Ord A /\ Ord C ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) ) $=
    cA word cC word wa cA cB wss cB cC wcel wa cA cC wpss cA cC wcel cC word cA
    cB wss cB cC wcel wa cA cC wpss wi cA word cC word cA cB wss cB cC wcel cA
    cC wpss cC word cB cC wcel cC word cB cC wcel cB word wa wa cA cB wss cA cC
    wpss cC word cB cC wcel cB cC wcel cB word wa cC word cB cC wcel cB word cC
    word cB cC wcel cB word cC cB ordelord ex ancld anc2li cC word cB cC wcel
    cB word wa wa cA cB wss cA cC wpss cC word cB cC wcel cB word cA cB wss cA
    cC wpss wi cC word cB word cB cC wcel cA cB wss cA cC wpss wi cC word cB
    word cB cC wcel cA cB wss cA cC wpss wi wi cC word cB word wa cB cC wcel cB
    cC wpss cA cB wss cA cC wpss wi cB word cC word cB cC wcel cB cC wpss wb cB
    cC ordelpss ancoms cA cB wss cB cC wpss cA cC wpss cA cB cC sspsstr expcom
    syl6bi ex com23 imp32 com12 syl9 imp3a adantl cA cC ordelpss sylibrd $.

  $( Transitive law for ordinal classes.  (Contributed by Mario Carneiro,
     30-Dec-2014.) $)
  ordtr3 $p |- ( ( Ord B /\ Ord C ) -> ( A e. B -> ( A e. C \/ C e. B ) ) ) $=
    cB word cC word wa cA cB wcel cA cC wcel cC cB wcel wo cB word cC word wa
    cA cB wcel wa cA cC wcel cC cB wcel cB word cC word wa cA cB wcel wa cA cC
    wcel wn cC cA wss cC cB wcel cB word cC word wa cA cB wcel wa cC word cA
    word cC cA wss cA cC wcel wn wb cB word cC word cA cB wcel simplr cB word
    cA cB wcel cA word cC word cB cA ordelord adantlr cC cA ordtri1 syl2anc cB
    word cC word wa cA cB wcel cC cA wss cC cB wcel cB word cC word wa cC cA
    wss cA cB wcel cC cB wcel cC word cB word cC cA wss cA cB wcel wa cC cB
    wcel wi cC cA cB ordtr2 ancoms ancomsd expdimp sylbird orrd ex $.

  $( Transitive law for ordinal numbers.  Theorem 7M(b) of [Enderton] p. 192.
     (Contributed by NM, 11-Aug-1994.) $)
  ontr1 $p |- ( C e. On -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $=
    cC con0 wcel cC word cA cB wcel cB cC wcel wa cA cC wcel wi cC eloni cA cB
    cC ordtr1 syl $.

  $( Transitive law for ordinal numbers.  Exercise 3 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Nov-2003.) $)
  ontr2 $p |- ( ( A e. On /\ C e. On ) ->
              ( ( A C_ B /\ B e. C ) -> A e. C ) ) $=
    cA con0 wcel cA word cC word cA cB wss cB cC wcel wa cA cC wcel wi cC con0
    wcel cA eloni cC eloni cA cB cC ordtr2 syl2an $.

  ${
    $d x y A $.  $d x y B $.
    $( The union of an ordinal stays the same if a subset equal to one of its
       elements is removed.  (Contributed by NM, 10-Dec-2004.) $)
    ordunidif $p |- ( ( Ord A /\ B e. A ) -> U. ( A \ B ) = U. A ) $=
      cA word cB cA wcel wa vx cv vy cv wss vy cA cB cdif wrex vx cA wral cA cB
      cdif cuni cA cuni wceq cA word cB cA wcel wa vx cv vy cv wss vy cA cB
      cdif wrex vx cA cA word cB cA wcel wa vx cv cA wcel wa vx cv cB wcel vx
      cv vy cv wss vy cA cB cdif wrex cA word cB cA wcel wa vx cv cA wcel wa vx
      cv cB wcel cB cA cB cdif wcel vx cv cB wss wa vx cv vy cv wss vy cA cB
      cdif wrex cA word cB cA wcel wa vx cv cB wcel cB cA cB cdif wcel vx cv cB
      wss wa wi vx cv cA wcel cA word cB cA wcel wa vx cv cB wcel vx cv cB wss
      cB cA cB cdif wcel cA word cB cA wcel wa cB con0 wcel vx cv cB wcel vx cv
      cB wss wi cA cB ordelon cB vx cv onelss syl cA word cB cA wcel wa cB con0
      wcel cB cA cB cdif wcel cA cB ordelon cB cA wcel cB con0 wcel cB cA cB
      cdif wcel wi cA word cB con0 wcel cB cB wcel wn cB cA wcel cB cA cB cdif
      wcel cB con0 wcel cB word cB cB wcel wn cB eloni cB ordirr syl cB cA cB
      cdif wcel cB cA wcel cB cB wcel wn cB cA cB eldif simplbi2 syl5 adantl
      mpd jctild adantr vx cv vy cv wss vx cv cB wss vy cB cA cB cdif vy cv cB
      vx cv sseq2 rspcev syl6 vx cv cA wcel vx cv cB wcel wn vx cv vy cv wss vy
      cA cB cdif wrex wi cA word cB cA wcel wa vx cv cA wcel vx cv cB wcel wn
      vx cv cA cB cdif wcel vx cv vx cv wss wa vx cv vy cv wss vy cA cB cdif
      wrex vx cv cA wcel vx cv cB wcel wn vx cv cA cB cdif wcel vx cv vx cv wss
      wa vx cv cA wcel vx cv cB wcel wn wa vx cv cA cB cdif wcel vx cv vx cv
      wss vx cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cA cB
      eldif biimpri vx cv ssid jctir ex vx cv vy cv wss vx cv vx cv wss vy vx
      cv cA cB cdif vy cv vx cv vx cv sseq2 rspcev syl6 adantl pm2.61d
      ralrimiva vx vy cA cB unidif syl $.

    $( If ` B ` is smaller than ` A ` , then it equals the intersection of the
       difference.  Exercise 11 in [TakeutiZaring] p. 44.  (Contributed by
       Andrew Salmon, 14-Nov-2011.) $)
    ordintdif $p |- ( ( Ord A /\ Ord B /\ ( A \ B ) =/= (/) )
      -> B = |^| ( A \ B ) ) $=
      cA cB cdif c0 wne cA word cB word cA cB wss wn cB cA cB cdif cint wceq cA
      cB wss cA cB cdif c0 cA cB ssdif0 necon3bbii cA word cB word cA cB wss wn
      w3a cA cB cdif cint vx cv cB wcel wn vx cA crab cint cB cA cB cdif vx cv
      cB wcel wn vx cA crab vx cA cB dfdif2 inteqi cA word cB word cA cB wss wn
      vx cv cB wcel wn vx cA crab cint cB wceq cA word cB word wa cA cB wss wn
      cB cA wcel vx cv cB wcel wn vx cA crab cint cB wceq cA word cB word wa cA
      cB wss cB cA wcel cA cB ordtri1 con2bid cA word cB word wa cB cA wcel vx
      cv cB wcel wn vx cA crab cint cB wceq cA word cB word wa cB cA wcel vx cv
      cB wcel wn vx cA crab cint cB vx cv wss vx cA crab cint cB cA word cB
      word wa vx cv cB wcel wn vx cA crab cB vx cv wss vx cA crab cA word cB
      word wa vx cv cB wcel wn cB vx cv wss vx cA cA word cB word wa vx cv cA
      wcel wa cB vx cv wss vx cv cB wcel wn cA word vx cv cA wcel cB word cB vx
      cv wss vx cv cB wcel wn wb cA word vx cv cA wcel wa vx cv word cB word cB
      vx cv wss vx cv cB wcel wn wb cA vx cv ordelord cB word vx cv word cB vx
      cv wss vx cv cB wcel wn wb cB vx cv ordtri1 ancoms sylan an32s bicomd
      rabbidva inteqd vx cB cA intmin sylan9eq ex sylbird 3impia syl5req
      syl3an3br $.
  $}

  ${
    $d x ps $.  $d x A $.
    onintss.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( If a property is true for an ordinal number, then the minimum ordinal
       number for which it is true is smaller or equal.  Theorem Schema 61 of
       [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)
    onintss $p |- ( A e. On -> ( ps -> |^| { x e. On | ph } C_ A ) ) $=
      cA con0 wcel wps wph vx con0 crab cint cA wss wph wps vx cA con0
      onintss.1 intminss ex $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A way to show that an ordinal number equals the minimum of a collection
       of ordinal numbers: it must be in the collection, and it must not be
       larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)
    oneqmini $p |- ( B C_ On -> ( ( A e. B /\ A. x e. A -. x e. B )
                    -> A = |^| B ) ) $=
      cB con0 wss cA cB wcel vx cv cB wcel wn vx cA wral wa cA cB cint wss cB
      cint cA wss wa cA cB cint wceq cB con0 wss cA cB wcel vx cv cB wcel wn vx
      cA wral wa cA cB cint wss cB cint cA wss cB con0 wss cA cB wcel vx cv cB
      wcel wn vx cA wral cA cB cint wss cB con0 wss cA cB wcel wa cA cB cint
      wss vx cv cB wcel wn vx cA wral cA cB cint wss cA vx cv wss vx cB wral cB
      con0 wss cA cB wcel wa vx cv cB wcel wn vx cA wral vx cA cB ssint cB con0
      wss cA cB wcel wa cA vx cv wss vx cv cB wcel wn vx cB cA cB con0 wss cA
      cB wcel wa vx cv cB wcel cA vx cv wss wi vx cv cB wcel vx cv cA wcel wn
      wi vx cv cA wcel vx cv cB wcel wn wi cB con0 wss cA cB wcel wa vx cv cB
      wcel cA vx cv wss vx cv cA wcel wn cB con0 wss cA cB wcel vx cv cB wcel
      cA vx cv wss vx cv cA wcel wn wb cB con0 wss cA cB wcel vx cv cB wcel wa
      cA con0 wcel vx cv con0 wcel wa cA vx cv wss vx cv cA wcel wn wb cB con0
      wss cA cB wcel cA con0 wcel vx cv cB wcel vx cv con0 wcel cB con0 cA ssel
      cB con0 vx cv ssel anim12d cA vx cv ontri1 syl6 expdimp pm5.74d vx cv cB
      wcel vx cv cA wcel con2b syl6bb ralbidv2 syl5bb biimprd expimpd cB con0
      wss cA cB wcel cB cint cA wss vx cv cB wcel wn vx cA wral cA cB wcel cB
      cint cA wss wi cB con0 wss cA cB intss1 a1i adantrd jcad cA cB cint eqss
      syl6ibr $.
  $}

  $( The empty set is an ordinal class.  (Contributed by NM, 11-May-1994.) $)
  ord0 $p |- Ord (/) $=
    c0 word c0 wtr c0 cep wwe tr0 cep we0 c0 df-ord mpbir2an $.

  $( The empty set is an ordinal number.  Corollary 7N(b) of [Enderton]
     p. 193.  (Contributed by NM, 17-Sep-1993.) $)
  0elon $p |- (/) e. On $=
    c0 con0 wcel c0 word ord0 c0 0ex elon mpbir $.

  $( A non-empty ordinal contains the empty set.  (Contributed by NM,
     25-Nov-1995.) $)
  ord0eln0 $p |- ( Ord A -> ( (/) e. A <-> A =/= (/) ) ) $=
    cA word c0 cA wcel cA c0 wne cA c0 ne0i cA c0 wne cA c0 wceq wn cA word c0
    cA wcel cA c0 df-ne cA word cA c0 wceq c0 cA wcel cA word c0 word cA c0
    wceq c0 cA wcel wo ord0 cA word c0 word wa cA c0 wceq c0 cA wcel wo cA c0
    wcel wn cA noel cA word c0 word wa cA c0 wcel cA c0 wceq c0 cA wcel wo cA
    c0 ordtri2 con2bid mpbiri mpan2 ord syl5bi impbid2 $.

  $( An ordinal number contains zero iff it is nonzero.  (Contributed by NM,
     6-Dec-2004.) $)
  on0eln0 $p |- ( A e. On -> ( (/) e. A <-> A =/= (/) ) ) $=
    cA con0 wcel cA word c0 cA wcel cA c0 wne wb cA eloni cA ord0eln0 syl $.

  $( An alternate definition of a limit ordinal.  (Contributed by NM,
     4-Nov-2004.) $)
  dflim2 $p |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A = U. A ) ) $=
    cA wlim cA word cA c0 wne cA cA cuni wceq w3a cA word c0 cA wcel cA cA cuni
    wceq w3a cA df-lim cA word c0 cA wcel cA cA cuni wceq wa wa cA word cA c0
    wne cA cA cuni wceq wa wa cA word c0 cA wcel cA cA cuni wceq w3a cA word cA
    c0 wne cA cA cuni wceq w3a cA word c0 cA wcel cA cA cuni wceq wa cA c0 wne
    cA cA cuni wceq wa cA word c0 cA wcel cA c0 wne cA cA cuni wceq cA ord0eln0
    anbi1d pm5.32i cA word c0 cA wcel cA cA cuni wceq 3anass cA word cA c0 wne
    cA cA cuni wceq 3anass 3bitr4i bitr4i $.

  $( The intersection of the class of ordinal numbers is the empty set.
     (Contributed by NM, 20-Oct-2003.) $)
  inton $p |- |^| On = (/) $=
    c0 con0 wcel con0 cint c0 wceq 0elon con0 int0el ax-mp $.

  $( The empty set is not a limit ordinal.  (Contributed by NM, 24-Mar-1995.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  nlim0 $p |- -. Lim (/) $=
    c0 wlim c0 word c0 c0 wcel c0 c0 cuni wceq w3a c0 word c0 c0 wcel c0 c0
    cuni wceq w3a c0 c0 wcel c0 noel c0 word c0 c0 wcel c0 c0 cuni wceq simp2
    mto c0 dflim2 mtbir $.

  $( A limit ordinal is ordinal.  (Contributed by NM, 4-May-1995.) $)
  limord $p |- ( Lim A -> Ord A ) $=
    cA wlim cA word cA c0 wne cA cA cuni wceq cA df-lim simp1bi $.

  $( A limit ordinal is its own supremum (union).  (Contributed by NM,
     4-May-1995.) $)
  limuni $p |- ( Lim A -> A = U. A ) $=
    cA wlim cA word cA c0 wne cA cA cuni wceq cA df-lim simp3bi $.

  $( The union of a limit ordinal is a limit ordinal.  (Contributed by NM,
     19-Sep-2006.) $)
  limuni2 $p |- ( Lim A -> Lim U. A ) $=
    cA wlim cA cuni wlim cA wlim cA cA cuni wceq cA wlim cA cuni wlim wb cA
    limuni cA cA cuni limeq syl ibi $.

  $( A limit ordinal contains the empty set.  (Contributed by NM,
     15-May-1994.) $)
  0ellim $p |- ( Lim A -> (/) e. A ) $=
    cA wlim c0 cA wcel cA c0 wne cA wlim cA c0 cA c0 wceq cA wlim c0 wlim nlim0
    cA c0 limeq mtbiri necon2ai cA wlim cA word c0 cA wcel cA c0 wne wb cA
    limord cA ord0eln0 syl mpbird $.

  $( A limit ordinal class that is also a set is an ordinal number.
     (Contributed by NM, 26-Apr-2004.) $)
  limelon $p |- ( ( A e. B /\ Lim A ) -> A e. On ) $=
    cA cB wcel cA wlim cA con0 wcel cA wlim cA con0 wcel cA cB wcel cA word cA
    limord cA cB elong syl5ibr imp $.

  $( The class of all ordinal numbers in not empty.  (Contributed by NM,
     17-Sep-1995.) $)
  onn0 $p |- On =/= (/) $=
    c0 con0 wcel con0 c0 wne 0elon con0 c0 ne0i ax-mp $.

  $( Equality of successors.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
  suceq $p |- ( A = B -> suc A = suc B ) $=
    cA cB wceq cA cA csn cun cB cB csn cun cA csuc cB csuc cA cB wceq cA cB cA
    csn cB csn cA cB wceq id cA cB sneq uneq12d cA df-suc cB df-suc 3eqtr4g $.

  $( Membership in a successor.  This one-way implication does not require that
     either ` A ` or ` B ` be sets.  (Contributed by NM, 6-Jun-1994.) $)
  elsuci $p |- ( A e. suc B -> ( A e. B \/ A = B ) ) $=
    cA cB csuc wcel cA cB wcel cA cB csn wcel wo cA cB wcel cA cB wceq wo cA cB
    csuc wcel cA cB cB csn cun wcel cA cB wcel cA cB csn wcel wo cB csuc cB cB
    csn cun cA cB df-suc eleq2i cA cB cB csn elun bitri cA cB csn wcel cA cB
    wceq cA cB wcel cA cB elsni orim2i sylbi $.

  $( Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
     (Contributed by NM, 15-Sep-1995.) $)
  elsucg $p |- ( A e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $=
    cA cB csuc wcel cA cB wcel cA cB csn wcel wo cA cV wcel cA cB wcel cA cB
    wceq wo cA cB csuc wcel cA cB cB csn cun wcel cA cB wcel cA cB csn wcel wo
    cB csuc cB cB csn cun cA cB df-suc eleq2i cA cB cB csn elun bitri cA cV
    wcel cA cB csn wcel cA cB wceq cA cB wcel cA cB cV elsncg orbi2d syl5bb $.

  $( Variant of membership in a successor, requiring that ` B ` rather than
     ` A ` be a set.  (Contributed by NM, 28-Oct-2003.) $)
  elsuc2g $p |- ( B e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $=
    cA cB csuc wcel cA cB cB csn cun wcel cB cV wcel cA cB wcel cA cB wceq wo
    cB csuc cB cB csn cun cA cB df-suc eleq2i cA cB cB csn cun wcel cA cB wcel
    cA cB csn wcel wo cB cV wcel cA cB wcel cA cB wceq wo cA cB cB csn elun cB
    cV wcel cA cB csn wcel cA cB wceq cA cB wcel cA cB cV elsnc2g orbi2d syl5bb
    syl5bb $.

  ${
    elsuc.1 $e |- A e. _V $.
    $( Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 15-Sep-2003.) $)
    elsuc $p |- ( A e. suc B <-> ( A e. B \/ A = B ) ) $=
      cA cvv wcel cA cB csuc wcel cA cB wcel cA cB wceq wo wb elsuc.1 cA cB cvv
      elsucg ax-mp $.

    $( Membership in a successor.  (Contributed by NM, 15-Sep-2003.) $)
    elsuc2 $p |- ( B e. suc A <-> ( B e. A \/ B = A ) ) $=
      cA cvv wcel cB cA csuc wcel cB cA wcel cB cA wceq wo wb elsuc.1 cB cA cvv
      elsuc2g ax-mp $.
  $}

  ${
    $d y A $.  $d x y $.
    nfsuc.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for successor.  (Contributed by NM,
       15-Sep-2003.) $)
    nfsuc $p |- F/_ x suc A $=
      vx cA csuc cA cA csn cun cA df-suc vx cA cA csn nfsuc.1 vx cA nfsuc.1
      nfsn nfun nfcxfr $.
  $}

  $( Membership in a successor.  (Contributed by NM, 20-Jun-1998.) $)
  elelsuc $p |- ( A e. B -> A e. suc B ) $=
    cA cB wcel cA cB csuc wcel cA cB wcel cA cB wceq wo cA cB wcel cA cB wceq
    orc cA cB cB elsucg mpbird $.

  ${
    $d x y A $.  $d x B $.
    $( Membership of a successor in another class.  (Contributed by NM,
       29-Jun-2004.) $)
    sucel $p |- ( suc A e. B <->
                E. x e. B A. y ( y e. x <-> ( y e. A \/ y = A ) ) ) $=
      cA csuc cB wcel vx cv cA csuc wceq vx cB wrex vy cv vx cv wcel vy cv cA
      wcel vy cv cA wceq wo wb vy wal vx cB wrex vx cA csuc cB risset vx cv cA
      csuc wceq vy cv vx cv wcel vy cv cA wcel vy cv cA wceq wo wb vy wal vx cB
      vx cv cA csuc wceq vy cv vx cv wcel vy cv cA csuc wcel wb vy wal vy cv vx
      cv wcel vy cv cA wcel vy cv cA wceq wo wb vy wal vy vx cv cA csuc dfcleq
      vy cv vx cv wcel vy cv cA csuc wcel wb vy cv vx cv wcel vy cv cA wcel vy
      cv cA wceq wo wb vy vy cv cA csuc wcel vy cv cA wcel vy cv cA wceq wo vy
      cv vx cv wcel vy cv cA vy vex elsuc bibi2i albii bitri rexbii bitri $.
  $}

  $( The successor of the empty set.  (Contributed by NM, 1-Feb-2005.) $)
  suc0 $p |- suc (/) = { (/) } $=
    c0 csuc c0 c0 csn cun c0 csn c0 cun c0 csn c0 df-suc c0 c0 csn uncom c0 csn
    un0 3eqtri $.

  $( A proper class is its own successor.  (Contributed by NM, 3-Apr-1995.) $)
  sucprc $p |- ( -. A e. _V -> suc A = A ) $=
    cA cvv wcel wn cA csuc cA c0 cun cA cA cvv wcel wn cA csuc cA cA csn cun cA
    c0 cun cA df-suc cA cvv wcel wn cA csn c0 wceq cA cA csn cun cA c0 cun wceq
    cA snprc cA csn c0 cA uneq2 sylbi syl5eq cA un0 syl6eq $.

  ${
    unisuc.1 $e |- A e. _V $.
    $( A transitive class is equal to the union of its successor.  Combines
       Theorem 4E of [Enderton] p. 72 and Exercise 6 of [Enderton] p. 73.
       (Contributed by NM, 30-Aug-1993.) $)
    unisuc $p |- ( Tr A <-> U. suc A = A ) $=
      cA cuni cA wss cA cuni cA cun cA wceq cA wtr cA csuc cuni cA wceq cA cuni
      cA ssequn1 cA df-tr cA csuc cuni cA cuni cA cun cA cA csuc cuni cA cA csn
      cun cuni cA cuni cA csn cuni cun cA cuni cA cun cA csuc cA cA csn cun cA
      df-suc unieqi cA cA csn uniun cA csn cuni cA cA cuni cA unisuc.1 unisn
      uneq2i 3eqtri eqeq1i 3bitr4i $.
  $}

  $( A class is included in its own successor.  Part of Proposition 7.23 of
     [TakeutiZaring] p. 41 (generalized to arbitrary classes).  (Contributed by
     NM, 31-May-1994.) $)
  sssucid $p |- A C_ suc A $=
    cA cA cA csn cun cA csuc cA cA csn ssun1 cA df-suc sseqtr4i $.

  $( Part of Proposition 7.23 of [TakeutiZaring] p. 41 (generalized).
     (Contributed by NM, 25-Mar-1995.)  (Proof shortened by Scott Fenton,
     20-Feb-2012.) $)
  sucidg $p |- ( A e. V -> A e. suc A ) $=
    cA cV wcel cA cA csuc wcel cA cA wcel cA cA wceq wo cA cA wceq cA cA wcel
    cA eqid olci cA cA cV elsucg mpbiri $.

  ${
    sucid.1 $e |- A e. _V $.
    $( A set belongs to its successor.  (Contributed by NM, 22-Jun-1994.)
       (Proof shortened by Alan Sare, 18-Feb-2012.)  (Proof shortened by Scott
       Fenton, 20-Feb-2012.) $)
    sucid $p |- A e. suc A $=
      cA cvv wcel cA cA csuc wcel sucid.1 cA cvv sucidg ax-mp $.
  $}

  $( No successor is empty.  (Contributed by NM, 3-Apr-1995.) $)
  nsuceq0 $p |- suc A =/= (/) $=
    cA csuc c0 wne cA csuc c0 wceq wn cA cvv wcel cA csuc c0 wceq wn cA cvv
    wcel cA csuc c0 wceq cA c0 wcel cA noel cA cvv wcel cA cA csuc wcel cA csuc
    c0 wceq cA c0 wcel cA cvv sucidg cA csuc c0 cA eleq2 syl5ibcom mtoi cA cvv
    wcel wn cA csuc c0 wceq wn cA cvv wcel wn cA csuc c0 wceq cA cvv wcel cA
    cvv wcel wn cA csuc c0 wceq cA c0 wceq cA cvv wcel cA cvv wcel wn cA csuc
    cA c0 cA sucprc eqeq1d cA c0 wceq cA cvv wcel c0 cvv wcel 0ex cA c0 cvv
    eleq1 mpbiri syl6bi con3d pm2.43i pm2.61i cA csuc c0 df-ne mpbir $.

  ${
    eqelsuc.1 $e |- A e. _V $.
    $( A set belongs to the successor of an equal set.  (Contributed by NM,
       18-Aug-1994.) $)
    eqelsuc $p |- ( A = B -> A e. suc B ) $=
      cA cB wceq cA cA csuc cB csuc cA eqelsuc.1 sucid cA cB suceq syl5eleq $.
  $}

  ${
    $d A x y $.  $d B y $.  $d C x y $.
    iunsuc.1 $e |- A e. _V $.
    iunsuc.2 $e |- ( x = A -> B = C ) $.
    $( Inductive definition for the indexed union at a successor.  (Contributed
       by Mario Carneiro, 4-Feb-2013.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
    iunsuc $p |- U_ x e. suc A B = ( U_ x e. A B u. C ) $=
      vx cA csuc cB ciun vx cA cA csn cun cB ciun vx cA cB ciun vx cA csn cB
      ciun cun vx cA cB ciun cC cun cA csuc cA cA csn cun wceq vx cA csuc cB
      ciun vx cA cA csn cun cB ciun wceq cA df-suc vx cA csuc cA cA csn cun cB
      iuneq1 ax-mp vx cA cA csn cB iunxun vx cA csn cB ciun cC vx cA cB ciun vx
      cA cB cC iunsuc.1 iunsuc.2 iunxsn uneq2i 3eqtri $.
  $}

  ${
    $d z y A $.
    $( The successor of a transtive class is transitive.  (Contributed by Alan
       Sare, 11-Apr-2009.) $)
    suctr $p |- ( Tr A -> Tr suc A ) $=
      cA wtr vz cv vy cv wcel vy cv cA csuc wcel wa vz cv cA csuc wcel wi vy
      wal vz wal cA csuc wtr cA wtr vz cv vy cv wcel vy cv cA csuc wcel wa vz
      cv cA csuc wcel wi vz vy cA wtr vz cv vy cv wcel vy cv cA csuc wcel wa vy
      cv cA wcel vy cv cA wceq wo vz cv cA csuc wcel vz cv vy cv wcel vy cv cA
      csuc wcel wa vy cv cA csuc wcel vy cv cA wcel vy cv cA wceq wo vz cv vy
      cv wcel vy cv cA csuc wcel simpr vy cv cA vy vex elsuc sylib cA wtr vz cv
      vy cv wcel vy cv cA csuc wcel wa vy cv cA wceq vz cv cA csuc wcel wi vy
      cv cA wcel vy cv cA wceq wo vz cv cA csuc wcel wi vz cv vy cv wcel vy cv
      cA csuc wcel wa vy cv cA wceq vz cv cA wcel vz cv cA csuc wcel vz cv vy
      cv wcel vy cv cA csuc wcel wa vz cv vy cv wcel vy cv cA wceq vz cv cA
      wcel vz cv vy cv wcel vy cv cA csuc wcel simpl vy cv cA vz cv eleq2
      syl5ibcom vz cv cA elelsuc syl6 cA wtr vz cv vy cv wcel vy cv cA csuc
      wcel wa vy cv cA wcel vz cv cA csuc wcel wi vy cv cA wceq vz cv cA csuc
      wcel wi vy cv cA wcel vy cv cA wceq wo vz cv cA csuc wcel wi wi cA wtr vz
      cv vy cv wcel vy cv cA csuc wcel wa vy cv cA wcel vz cv cA wcel vz cv cA
      csuc wcel cA wtr vz cv vy cv wcel vy cv cA wcel vz cv cA wcel wi vy cv cA
      csuc wcel cA wtr vz cv vy cv wcel vy cv cA wcel vz cv cA wcel cA vz cv vy
      cv trel exp3a adantrd vz cv cA elelsuc syl8 vy cv cA wcel vz cv cA csuc
      wcel vy cv cA wceq jao syl6 mpdi mpdi alrimivv vz vy cA csuc dftr2 sylibr
      $.
  $}

  $( A set whose successor belongs to a transitive class also belongs.
     (Contributed by NM, 5-Sep-2003.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)
  trsuc $p |- ( ( Tr A /\ suc B e. A ) -> B e. A ) $=
    cA wtr cB csuc cA wcel cB cA wcel cB csuc cA wcel cB cB csuc wcel cB csuc
    cA wcel wa cA wtr cB cA wcel cB csuc cA wcel cB cB csuc wcel cB csuc cA
    wcel cB cvv wcel cB cB csuc wcel cB cB csuc wss cB csuc cA wcel cB cvv wcel
    cB sssucid cB cB csuc cA ssexg mpan cB cvv sucidg syl ancri cA cB cB csuc
    trel syl5 imp $.

  ${
    $d x y A $.
    $( Obsolete proof of ~ suctr as of 5-Apr-2016.  The successor of a
       transitive set is transitive.  (Contributed by Scott Fenton,
       21-Feb-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    trsuc2OLD $p |- ( Tr A -> Tr suc A ) $=
      cA wtr vx cv vy cv wcel vy cv cA wcel vy cv cA csn wcel wo wa vx cv cA
      wcel vx cv cA csn wcel wo wi vy wal vx wal cA csuc wtr cA wtr vx cv vy cv
      wcel vy cv cA wcel vy cv cA csn wcel wo wa vx cv cA wcel vx cv cA csn
      wcel wo wi vx vy vx cv vy cv wcel vy cv cA wcel vy cv cA csn wcel wo wa
      vx cv vy cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cA csn wcel wa
      wo cA wtr vx cv cA wcel vx cv cA csn wcel wo vx cv vy cv wcel vy cv cA
      wcel vy cv cA csn wcel andi cA wtr vx cv vy cv wcel vy cv cA wcel wa vx
      cv vy cv wcel vy cv cA wceq wa wo vx cv cA wcel vx cv cA wceq wo vx cv vy
      cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cA csn wcel wa wo vx cv
      cA wcel vx cv cA csn wcel wo vx cv vy cv wcel vy cv cA wcel wa vx cv vy
      cv wcel vy cv cA wceq wa wo vx cv vy cv wcel vy cv cA wcel wa vx cv cA
      wcel wo cA wtr vx cv cA wcel vx cv cA wceq wo vx cv vy cv wcel vy cv cA
      wceq wa vx cv cA wcel vx cv vy cv wcel vy cv cA wcel wa vy cv cA wceq vx
      cv vy cv wcel vx cv cA wcel vy cv cA vx cv eleq2 biimpac orim2i cA wtr vx
      cv vy cv wcel vy cv cA wcel wa vx cv cA wcel vx cv cA wceq wo vx cv cA
      wcel cA wtr vx cv vy cv wcel vy cv cA wcel wa vx cv cA wcel vx cv cA wcel
      vx cv cA wceq wo cA vx cv vy cv trel vx cv cA wcel vx cv cA wceq orc syl6
      vx cv cA wcel vx cv cA wcel vx cv cA wceq wo wi cA wtr vx cv cA wcel vx
      cv cA wceq orc a1i jaod syl5 vx cv vy cv wcel vy cv cA csn wcel wa vx cv
      vy cv wcel vy cv cA wceq wa vx cv vy cv wcel vy cv cA wcel wa vy cv cA
      csn wcel vy cv cA wceq vx cv vy cv wcel vy cA elsn anbi2i orbi2i vx cv cA
      csn wcel vx cv cA wceq vx cv cA wcel vx cA elsn orbi2i 3imtr4g syl5bi
      alrimivv cA csuc wtr cA cA csn cun wtr vx cv vy cv wcel vy cv cA cA csn
      cun wcel wa vx cv cA cA csn cun wcel wi vy wal vx wal vx cv vy cv wcel vy
      cv cA wcel vy cv cA csn wcel wo wa vx cv cA wcel vx cv cA csn wcel wo wi
      vy wal vx wal cA csuc cA cA csn cun wceq cA csuc wtr cA cA csn cun wtr wb
      cA df-suc cA csuc cA cA csn cun treq ax-mp vx vy cA cA csn cun dftr2 vx
      cv vy cv wcel vy cv cA cA csn cun wcel wa vx cv cA cA csn cun wcel wi vx
      cv vy cv wcel vy cv cA wcel vy cv cA csn wcel wo wa vx cv cA wcel vx cv
      cA csn wcel wo wi vx vy vx cv vy cv wcel vy cv cA cA csn cun wcel wa vx
      cv vy cv wcel vy cv cA wcel vy cv cA csn wcel wo wa vx cv cA cA csn cun
      wcel vx cv cA wcel vx cv cA csn wcel wo vy cv cA cA csn cun wcel vy cv cA
      wcel vy cv cA csn wcel wo vx cv vy cv wcel vy cv cA cA csn elun anbi2i vx
      cv cA cA csn elun imbi12i 2albii 3bitri sylibr $.
  $}

  $( A member of the successor of a transitive class is a subclass of it.
     (Contributed by NM, 4-Oct-2003.) $)
  trsucss $p |- ( Tr A -> ( B e. suc A -> B C_ A ) ) $=
    cB cA csuc wcel cB cA wcel cB cA wceq wo cA wtr cB cA wss cB cA elsuci cA
    wtr cB cA wcel cB cA wss cB cA wceq cA cB trss cB cA wceq cB cA wss wi cA
    wtr cB cA eqimss a1i jaod syl5 $.

  $( A subset of an ordinal belongs to its successor.  (Contributed by NM,
     28-Nov-2003.) $)
  ordsssuc $p |- ( ( A e. On /\ Ord B ) -> ( A C_ B <-> A e. suc B ) ) $=
    cA con0 wcel cB word wa cA cB wss cA cB wcel cA cB wceq wo cA cB csuc wcel
    cA con0 wcel cA word cB word cA cB wss cA cB wcel cA cB wceq wo wb cA eloni
    cA cB ordsseleq sylan cA con0 wcel cA cB csuc wcel cA cB wcel cA cB wceq wo
    wb cB word cA cB con0 elsucg adantr bitr4d $.

  $( A subset of an ordinal number belongs to its successor.  (Contributed by
     NM, 15-Sep-1995.) $)
  onsssuc $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $=
    cB con0 wcel cA con0 wcel cB word cA cB wss cA cB csuc wcel wb cB eloni cA
    cB ordsssuc sylan2 $.

  $( An ordinal subset of an ordinal number belongs to its successor.
     (Contributed by NM, 1-Feb-2005.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)
  ordsssuc2 $p |- ( ( Ord A /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $=
    cA cvv wcel cA word cB con0 wcel wa cA cB wss cA cB csuc wcel wb wi cA cvv
    wcel cA word cB con0 wcel wa cA con0 wcel cB con0 wcel wa cA cB wss cA cB
    csuc wcel wb cA cvv wcel cA word cA con0 wcel cB con0 wcel cA cvv wcel cA
    con0 wcel cA word cA cvv elong biimprd anim1d cA cB onsssuc syl6 cA cvv
    wcel wn cB con0 wcel cA cB wss cA cB csuc wcel wb cA word cB con0 wcel cA
    cvv wcel wn cA cB wss cA cB csuc wcel wb cB con0 wcel cA cvv wcel wn wa cB
    con0 wcel cA cvv wcel wi wn cA cB wss cA cB csuc wcel wb cB con0 wcel cA
    cvv wcel annim cA cB wss cB con0 wcel cA cvv wcel wi cA cB csuc wcel cA cB
    wss cB con0 wcel cA cvv wcel cA cB con0 ssexg ex cA cB csuc wcel cA cvv
    wcel cB con0 wcel cA cB csuc elex a1d pm5.21ni sylbi expcom adantld pm2.61i
    $.

  ${
    $d x A $.  $d x B $.
    $( When its successor is subtracted from a class of ordinal numbers, an
       ordinal number is less than the minimum of the resulting subclass.
       (Contributed by NM, 1-Dec-2003.) $)
    onmindif $p |- ( ( A C_ On /\ B e. On ) -> B e. |^| ( A \ suc B ) ) $=
      cA con0 wss cB con0 wcel wa cB cA cB csuc cdif cint wcel cB vx cv wcel vx
      cA cB csuc cdif wral cA con0 wss cB con0 wcel wa cB vx cv wcel vx cA cB
      csuc cdif vx cv cA cB csuc cdif wcel vx cv cA wcel vx cv cB csuc wcel wn
      wa cA con0 wss cB con0 wcel wa cB vx cv wcel vx cv cA cB csuc eldif cA
      con0 wss cB con0 wcel vx cv cA wcel vx cv cB csuc wcel wn cB vx cv wcel
      cA con0 wss vx cv cA wcel cB con0 wcel vx cv cB csuc wcel wn cB vx cv
      wcel wi cA con0 wss vx cv cA wcel cB con0 wcel vx cv cB csuc wcel wn cB
      vx cv wcel wi cA con0 wss vx cv cA wcel wa cB con0 wcel wa vx cv cB csuc
      wcel wn cB vx cv wcel cA con0 wss vx cv cA wcel wa vx cv con0 wcel cB
      con0 wcel vx cv cB csuc wcel wn cB vx cv wcel wb cA con0 vx cv ssel2 vx
      cv con0 wcel cB con0 wcel wa cB vx cv wcel vx cv cB csuc wcel vx cv con0
      wcel cB con0 wcel wa vx cv cB wss cB vx cv wcel wn vx cv cB csuc wcel vx
      cv cB ontri1 vx cv cB onsssuc bitr3d con1bid sylan biimpd exp31 com23
      imp4b syl5bi ralrimiv cB con0 wcel cB cA cB csuc cdif cint wcel cB vx cv
      wcel vx cA cB csuc cdif wral wb cA con0 wss vx cB cA cB csuc cdif con0
      elintg adantl mpbird $.
  $}

  $( There is no set between an ordinal class and its successor.  Generalized
     Proposition 7.25 of [TakeutiZaring] p. 41.  (Contributed by NM,
     21-Jun-1998.) $)
  ordnbtwn $p |- ( Ord A -> -. ( A e. B /\ B e. suc A ) ) $=
    cA word cA cB wcel cB cA wcel wa cA cA wcel wo cA cB wcel cB cA csuc wcel
    wa cA word cA cB wcel cB cA wcel wa wn cA cA wcel wn cA cB wcel cB cA wcel
    wa cA cA wcel wo wn cA cB ordn2lp cA ordirr cA cB wcel cB cA wcel wa cA cA
    wcel ioran sylanbrc cA cB wcel cB cA csuc wcel wa cA cB wcel cB cA wcel wa
    cA cB wcel cB cA wceq wa wo cA cB wcel cB cA wcel wa cA cA wcel wo cA cB
    wcel cB cA csuc wcel wa cA cB wcel cB cA wcel cB cA wceq wo wa cA cB wcel
    cB cA wcel wa cA cB wcel cB cA wceq wa wo cB cA csuc wcel cB cA wcel cB cA
    wceq wo cA cB wcel cB cA elsuci anim2i cA cB wcel cB cA wcel cB cA wceq
    andi sylib cA cB wcel cB cA wceq wa cA cA wcel cA cB wcel cB cA wcel wa cB
    cA wceq cA cB wcel cA cA wcel cB cA cA eleq2 biimpac orim2i syl nsyl $.

  $( There is no set between an ordinal number and its successor.  Proposition
     7.25 of [TakeutiZaring] p. 41.  (Contributed by NM, 9-Jun-1994.) $)
  onnbtwn $p |- ( A e. On -> -. ( A e. B /\ B e. suc A ) ) $=
    cA con0 wcel cA word cA cB wcel cB cA csuc wcel wa wn cA eloni cA cB
    ordnbtwn syl $.

  $( A set whose successor is a subset of another class is a member of that
     class.  (Contributed by NM, 16-Sep-1995.) $)
  sucssel $p |- ( A e. V -> ( suc A C_ B -> A e. B ) ) $=
    cA cV wcel cA cA csuc wcel cA csuc cB wss cA cB wcel cA cV sucidg cA csuc
    cB cA ssel syl5com $.

  $( Ordinal derived from its successor.  (Contributed by NM, 20-May-1998.) $)
  orddif $p |- ( Ord A -> A = ( suc A \ { A } ) ) $=
    cA word cA cA csn cin c0 wceq cA cA csuc cA csn cdif wceq cA orddisj cA cA
    csn cin c0 wceq cA cA cA csn cdif wceq cA cA csuc cA csn cdif wceq cA cA
    csn disj3 cA csuc cA csn cdif cA cA csn cdif cA cA csuc cA csn cdif cA cA
    csn cun cA csn cdif cA cA csn cdif cA csuc cA cA csn cun cA csn cA df-suc
    difeq1i cA cA csn difun2 eqtri eqeq2i bitr4i sylib $.

  $( An ordinal class includes its union.  (Contributed by NM, 13-Sep-2003.) $)
  orduniss $p |- ( Ord A -> U. A C_ A ) $=
    cA word cA wtr cA cuni cA wss cA ordtr cA df-tr sylib $.

  $( A trichotomy law for ordinal classes.  (Contributed by NM, 13-Sep-2003.)
     (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)
  ordtri2or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ B C_ A ) ) $=
    cA word cB word wa cA cB wcel cB cA wss cA word cB word wa cB cA wss cA cB
    wcel wn cB word cA word cB cA wss cA cB wcel wn wb cB cA ordtri1 ancoms
    biimprd orrd $.

  $( A trichotomy law for ordinal classes.  (Contributed by NM, 2-Nov-2003.) $)
  ordtri2or2 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B \/ B C_ A ) ) $=
    cA word cB word wa cA cB wcel cB cA wss wo cA cB wss cB cA wss wo cA cB
    ordtri2or cB word cA cB wcel cB cA wss wo cA cB wss cB cA wss wo wi cA word
    cB word cA cB wcel cA cB wss cB cA wss cB word cA cB wcel cA cB wss cB cA
    ordelss ex orim1d adantl mpd $.

  $( A consequence of total ordering for ordinal classes.  Similar to
     ~ ordtri2or2 .  (Contributed by David Moews, 1-May-2017.) $)
  ordtri2or3 $p |- ( ( Ord A /\ Ord B ) ->
                     ( A = ( A i^i B ) \/ B = ( A i^i B ) ) ) $=
    cA word cB word wa cA cB wss cB cA wss wo cA cA cB cin wceq cB cA cB cin
    wceq wo cA cB ordtri2or2 cA cB wss cA cA cB cin wceq cB cA wss cB cA cB cin
    wceq cA cB dfss cB cA dfss5 orbi12i sylib $.

  $( The intersection of two ordinal classes is an element of a third if and
     only if either one of them is.  (Contributed by David Moews,
     1-May-2017.) $)
  ordelinel $p |- ( ( Ord A /\ Ord B /\ Ord C ) ->
                    ( ( A i^i B ) e. C <-> ( A e. C \/ B e. C ) ) ) $=
    cA word cB word cC word w3a cA cB cin cC wcel cA cC wcel cB cC wcel wo cA
    word cB word cC word w3a cA cA cB cin wceq cB cA cB cin wceq wo cA cB cin
    cC wcel cA cC wcel cB cC wcel wo wi cA word cB word cA cA cB cin wceq cB cA
    cB cin wceq wo cC word cA cB ordtri2or3 3adant3 cA cA cB cin wceq cA cB cin
    cC wcel cA cC wcel cB cC wcel wo wi cB cA cB cin wceq cA cA cB cin wceq cA
    cB cin cC wcel cA cC wcel cA cC wcel cB cC wcel wo cA cA cB cin cC eleq1 cA
    cC wcel cB cC wcel orc syl6bir cB cA cB cin wceq cA cB cin cC wcel cB cC
    wcel cA cC wcel cB cC wcel wo cB cA cB cin cC eleq1 cB cC wcel cA cC wcel
    olc syl6bir jaoi syl cA word cB word cC word w3a cA cC wcel cA cB cin cC
    wcel cB cC wcel cA word cB word cC word w3a cA cB cin cA wss cA cC wcel cA
    cB cin cC wcel cA cB inss1 cA word cB word cC word w3a cA cB cin word cC
    word wa cA cB cin cA wss cA cC wcel wa cA cB cin cC wcel wi cA word cB word
    cC word cA cB cin word cC word wa cA word cB word wa cA cB cin word cC word
    cA cB ordin anim1i 3impa cA cB cin cA cC ordtr2 syl mpani cA word cB word
    cC word w3a cA cB cin cB wss cB cC wcel cA cB cin cC wcel cA cB inss2 cA
    word cB word cC word w3a cA cB cin word cC word wa cA cB cin cB wss cB cC
    wcel wa cA cB cin cC wcel wi cA word cB word cC word cA cB cin word cC word
    wa cA word cB word wa cA cB cin word cC word cA cB ordin anim1i 3impa cA cB
    cin cB cC ordtr2 syl mpani jaod impbid $.

  $( Property of a subclass of the maximum (i.e. union) of two ordinals.
     (Contributed by NM, 28-Nov-2003.) $)
  ordssun $p |- ( ( Ord B /\ Ord C ) ->
               ( A C_ ( B u. C ) <-> ( A C_ B \/ A C_ C ) ) ) $=
    cB word cC word wa cA cB cC cun wss cA cB wss cA cC wss wo cB word cC word
    wa cB cC wss cC cB wss wo cA cB cC cun wss cA cB wss cA cC wss wo wi cB cC
    ordtri2or2 cB cC wss cA cB cC cun wss cA cB wss cA cC wss wo wi cC cB wss
    cB cC wss cA cB cC cun wss cA cC wss cA cB wss cA cC wss wo cB cC wss cB cC
    cun cC wceq cA cB cC cun wss cA cC wss wb cB cC ssequn1 cB cC cun cC cA
    sseq2 sylbi cA cC wss cA cB wss olc syl6bi cC cB wss cA cB cC cun wss cA cB
    wss cA cB wss cA cC wss wo cC cB wss cB cC cun cB wceq cA cB cC cun wss cA
    cB wss wb cC cB ssequn2 cB cC cun cB cA sseq2 sylbi cA cB wss cA cC wss orc
    syl6bi jaoi syl cA cB cC ssun impbid1 $.

  $( The maximum (i.e. union) of two ordinals is either one or the other.
     Similar to Exercise 14 of [TakeutiZaring] p. 40.  (Contributed by NM,
     28-Nov-2003.) $)
  ordequn $p |- ( ( Ord B /\ Ord C ) ->
               ( A = ( B u. C ) -> ( A = B \/ A = C ) ) ) $=
    cB word cC word wa cB cC wss cC cB wss wo cA cB cC cun wceq cA cB wceq cA
    cC wceq wo wi cB cC ordtri2or2 cB cC wss cA cB cC cun wceq cA cB wceq cA cC
    wceq wo wi cC cB wss cB cC wss cA cB cC cun wceq cA cC wceq cA cB wceq cA
    cC wceq wo cB cC wss cB cC cun cC wceq cA cB cC cun wceq cA cC wceq wb cB
    cC ssequn1 cB cC cun cC cA eqeq2 sylbi cA cC wceq cA cB wceq olc syl6bi cC
    cB wss cA cB cC cun wceq cA cB wceq cA cB wceq cA cC wceq wo cC cB wss cB
    cC cun cB wceq cA cB cC cun wceq cA cB wceq wb cC cB ssequn2 cB cC cun cB
    cA eqeq2 sylbi cA cB wceq cA cC wceq orc syl6bi jaoi syl $.

  $( The maximum (i.e. union) of two ordinals is ordinal.  Exercise 12 of
     [TakeutiZaring] p. 40.  (Contributed by NM, 28-Nov-2003.) $)
  ordun $p |- ( ( Ord A /\ Ord B ) -> Ord ( A u. B ) ) $=
    cA word cB word wa cA cB cun cA wceq cA cB cun cB wceq wo cA cB cun word cA
    word cB word wa cA cB cun cA cB cun wceq cA cB cun cA wceq cA cB cun cB
    wceq wo cA cB cun eqid cA cB cun cA cB ordequn mpi cA word cA cB cun cA
    wceq cA cB cun word cB word cA cB cun cB wceq cA cB cun cA wceq cA cB cun
    word cA word cA cB cun cA ordeq biimprcd cA cB cun cB wceq cA cB cun word
    cB word cA cB cun cB ordeq biimprcd jaao mpd $.

  ${
    $d x A $.  $d x B $.
    $( A subclass relationship for union and successor of ordinal classes.
       (Contributed by NM, 28-Nov-2003.) $)
    ordunisssuc $p |- ( ( A C_ On /\ Ord B ) ->
                      ( U. A C_ B <-> A C_ suc B ) ) $=
      cA con0 wss cB word wa vx cv cB wss vx cA wral vx cv cB csuc wcel vx cA
      wral cA cuni cB wss cA cB csuc wss cA con0 wss cB word wa vx cv cB wss vx
      cv cB csuc wcel vx cA cA con0 wss vx cv cA wcel cB word vx cv cB wss vx
      cv cB csuc wcel wb cA con0 wss vx cv cA wcel wa vx cv con0 wcel cB word
      vx cv cB wss vx cv cB csuc wcel wb cA con0 vx cv ssel2 vx cv cB ordsssuc
      sylan an32s ralbidva vx cA cB unissb vx cA cB csuc dfss3 3bitr4g $.
  $}

  $( The successor operation behaves like a one-to-one function.  Compare
     Exercise 16 of [Enderton] p. 194.  (Contributed by NM, 3-Sep-2003.) $)
  suc11 $p |- ( ( A e. On /\ B e. On ) -> ( suc A = suc B <-> A = B ) ) $=
    cA con0 wcel cB con0 wcel wa cA csuc cB csuc wceq cA cB wceq cA con0 wcel
    cB con0 wcel wa cA cB wcel wn cB cA wcel wn wo cA csuc cB csuc wceq cA cB
    wceq wi cA con0 wcel cA cB wcel wn cB cA wcel wn wo cB con0 wcel cA con0
    wcel cA word cA cB wcel wn cB cA wcel wn wo cA eloni cA word cA cB wcel cB
    cA wcel wa wn cA cB wcel wn cB cA wcel wn wo cA cB ordn2lp cA cB wcel cB cA
    wcel ianor sylib syl adantr cA con0 wcel cA cB wcel wn cA csuc cB csuc wceq
    cA cB wceq wi cB con0 wcel cB cA wcel wn cA con0 wcel cA csuc cB csuc wceq
    cA cB csuc wcel cA cB wcel wn cA cB wceq cA csuc cB csuc wceq cA csuc cB
    csuc wss cA con0 wcel cA cB csuc wcel cA csuc cB csuc eqimss cA cB csuc
    con0 sucssel syl5 cA cB csuc wcel cA cB wcel wn cA cB wceq cA cB csuc wcel
    cA cB wcel cA cB wceq cA cB elsuci ord com12 syl9 cB con0 wcel cA csuc cB
    csuc wceq cB cA csuc wcel cB cA wcel wn cA cB wceq cA csuc cB csuc wceq cB
    csuc cA csuc wss cB con0 wcel cB cA csuc wcel cB csuc cA csuc eqimss2 cB cA
    csuc con0 sucssel syl5 cB cA wcel wn cB cA csuc wcel cB cA wceq cA cB wceq
    cB cA csuc wcel cB cA wcel wn cB cA wceq cB cA csuc wcel cB cA wcel cB cA
    wceq cB cA elsuci ord com12 cB cA eqcom syl6ib syl9 jaao mpd cA cB suceq
    impbid1 $.

  ${
    on.1 $e |- A e. On $.
    $( An ordinal number is an ordinal class.  (Contributed by NM,
       11-Jun-1994.) $)
    onordi $p |- Ord A $=
      cA con0 wcel cA word on.1 cA eloni ax-mp $.

    $( An ordinal number is a transitive class.  (Contributed by NM,
       11-Jun-1994.) $)
    ontrci $p |- Tr A $=
      cA word cA wtr cA on.1 onordi cA ordtr ax-mp $.

    $( An ordinal number is not a member of itself.  Theorem 7M(c) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)
    onirri $p |- -. A e. A $=
      cA word cA cA wcel wn cA on.1 onordi cA ordirr ax-mp $.

    $( A member of an ordinal number is an ordinal number.  Theorem 7M(a) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)
    oneli $p |- ( B e. A -> B e. On ) $=
      cA con0 wcel cB cA wcel cB con0 wcel on.1 cA cB onelon mpan $.

    $( A member of an ordinal number is a subset of it.  (Contributed by NM,
       11-Aug-1994.) $)
    onelssi $p |- ( B e. A -> B C_ A ) $=
      cA con0 wcel cB cA wcel cB cA wss wi on.1 cA cB onelss ax-mp $.

    $( An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)
    onssneli $p |- ( A C_ B -> -. B e. A ) $=
      cB cA wcel cA cB wss cB cA wcel cA cB wss cB cB wcel cB cA wcel cB con0
      wcel cB word cB cB wcel wn cA cB on.1 oneli cB eloni cB ordirr 3syl cA cB
      wss cB cA wcel cB cB wcel cA cB cB ssel com12 mtod con2i $.

    $( An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)
    onssnel2i $p |- ( B C_ A -> -. A e. B ) $=
      cB cA wss cA cB wcel cA cA wcel cA on.1 onirri cB cA cA ssel mtoi $.

    $( An element of an ordinal number equals the intersection with it.
       (Contributed by NM, 11-Jun-1994.) $)
    onelini $p |- ( B e. A -> B = ( B i^i A ) ) $=
      cB cA wcel cB cA wss cB cB cA cin wceq cA cB on.1 onelssi cB cA dfss
      sylib $.

    $( An ordinal number equals its union with any element.  (Contributed by
       NM, 13-Jun-1994.) $)
    oneluni $p |- ( B e. A -> ( A u. B ) = A ) $=
      cB cA wcel cB cA wss cA cB cun cA wceq cA cB on.1 onelssi cB cA ssequn2
      sylib $.

    $( An ordinal number is equal to the union of its successor.  (Contributed
       by NM, 12-Jun-1994.) $)
    onunisuci $p |- U. suc A = A $=
      cA wtr cA csuc cuni cA wceq cA on.1 ontrci cA cA con0 on.1 elexi unisuc
      mpbi $.

    ${
      on.2 $e |- B e. On $.
      $( Subset is equivalent to membership or equality for ordinal numbers.
         (Contributed by NM, 15-Sep-1995.) $)
      onsseli $p |- ( A C_ B <-> ( A e. B \/ A = B ) ) $=
        cA con0 wcel cB con0 wcel cA cB wss cA cB wcel cA cB wceq wo wb on.1
        on.2 cA cB onsseleq mp2an $.

      $( The union of two ordinal numbers is an ordinal number.  (Contributed
         by NM, 13-Jun-1994.) $)
      onun2i $p |- ( A u. B ) e. On $=
        cB cA wcel cA cB wss wo cA cB cun con0 wcel cB word cA word cB cA wcel
        cA cB wss wo cB on.2 onordi cA on.1 onordi cB cA ordtri2or mp2an cB cA
        wcel cA cB cun con0 wcel cA cB wss cB cA wcel cA cB cun cA con0 cA cB
        on.1 oneluni on.1 syl6eqel cA cB wss cA cB cun cB wceq cA cB cun con0
        wcel cA cB ssequn1 cA cB cun cB wceq cA cB cun con0 wcel cB con0 wcel
        on.2 cA cB cun cB con0 eleq1 mpbiri sylbi jaoi ax-mp $.
    $}
  $}

  $( An ordinal equal to its own union is either zero or a limit ordinal.
     (Contributed by NM, 1-Oct-2003.) $)
  unizlim $p |- ( Ord A -> ( A = U. A <-> ( A = (/) \/ Lim A ) ) ) $=
    cA word cA cA cuni wceq cA c0 wceq cA wlim wo cA word cA cA cuni wceq cA c0
    wceq cA wlim wo cA word cA cA cuni wceq wa cA c0 wceq cA wlim cA word cA cA
    cuni wceq cA c0 wceq wn cA wlim wi cA word cA c0 wceq wn cA cA cuni wceq cA
    wlim cA c0 wceq wn cA c0 wne cA word cA cA cuni wceq cA wlim wi cA c0 df-ne
    cA word cA c0 wne cA cA cuni wceq cA wlim cA wlim cA word cA c0 wne cA cA
    cuni wceq w3a cA df-lim biimpri 3exp syl5bir com23 imp orrd ex cA c0 wceq
    cA cA cuni wceq cA wlim cA c0 wceq c0 c0 cuni cA cA cuni c0 cuni c0 uni0
    eqcomi cA c0 wceq id cA c0 unieq 3eqtr4a cA limuni jaoi impbid1 $.

  $( An ordinal number either equals zero or contains zero.  (Contributed by
     NM, 1-Jun-2004.) $)
  on0eqel $p |- ( A e. On -> ( A = (/) \/ (/) e. A ) ) $=
    cA con0 wcel c0 cA wcel c0 cA wceq wo cA c0 wceq c0 cA wcel wo cA con0 wcel
    c0 cA wss c0 cA wcel c0 cA wceq wo cA 0ss c0 con0 wcel cA con0 wcel c0 cA
    wss c0 cA wcel c0 cA wceq wo wb 0elon c0 cA onsseleq mpan mpbii c0 cA wcel
    c0 cA wceq wo c0 cA wcel cA c0 wceq wo cA c0 wceq c0 cA wcel wo c0 cA wceq
    cA c0 wceq c0 cA wcel c0 cA eqcom orbi2i c0 cA wcel cA c0 wceq orcom bitri
    sylib $.

  $( The singleton of the singleton of the empty set is not an ordinal (nor a
     natural number by ~ omsson ).  It can be used to represent an "undefined"
     value for a partial operation on natural or ordinal numbers.  See also
     ~ onxpdisj .  (Contributed by NM, 21-May-2004.)  (Proof shortened by
     Andrew Salmon, 12-Aug-2011.) $)
  snsn0non $p |- -. { { (/) } } e. On $=
    c0 csn csn con0 wcel c0 csn csn c0 wceq c0 c0 csn csn wcel wo c0 csn csn c0
    wceq c0 c0 csn csn wcel c0 csn c0 csn csn wcel c0 csn csn c0 wceq wn c0 csn
    p0ex snid c0 csn csn c0 csn n0i ax-mp c0 c0 csn csn wcel c0 c0 csn wceq c0
    c0 csn wceq c0 csn c0 wceq c0 c0 csn wcel c0 csn c0 wceq wn c0 0ex snid c0
    csn c0 n0i ax-mp c0 c0 csn eqcom mtbir c0 c0 csn 0ex elsnc mtbir pm3.2ni c0
    csn csn on0eqel mto $.



