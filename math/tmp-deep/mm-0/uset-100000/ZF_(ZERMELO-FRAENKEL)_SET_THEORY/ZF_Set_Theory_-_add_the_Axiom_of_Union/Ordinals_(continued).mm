$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Introduce_the_Axiom_of_Union.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals (continued)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The class of all ordinal numbers is ordinal.  Proposition 7.12 of
       [TakeutiZaring] p. 38, but without using the Axiom of Regularity.
       (Contributed by NM, 17-May-1994.) $)
${
	$d x y $.
	iordon_0 $f set x $.
	iordon_1 $f set y $.
	ordon $p |- Ord On $= con0 word con0 wtr con0 cep wwe tron con0 cep wwe con0 cep wfr iordon_0 cv iordon_1 cv cep wbr iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv cep wbr w3o iordon_1 con0 wral iordon_0 con0 wral onfr iordon_0 cv iordon_1 cv cep wbr iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv cep wbr w3o iordon_0 iordon_1 con0 iordon_0 cv con0 wcel iordon_0 cv word iordon_1 cv word iordon_0 cv iordon_1 cv cep wbr iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv cep wbr w3o iordon_1 cv con0 wcel iordon_0 cv eloni iordon_1 cv eloni iordon_0 cv word iordon_1 cv word wa iordon_0 cv iordon_1 cv wcel iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv wcel w3o iordon_0 cv iordon_1 cv cep wbr iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv cep wbr w3o iordon_0 cv iordon_1 cv ordtri3or iordon_0 cv iordon_1 cv cep wbr iordon_0 cv iordon_1 cv wcel iordon_0 cv iordon_1 cv wceq iordon_0 cv iordon_1 cv wceq iordon_1 cv iordon_0 cv cep wbr iordon_1 cv iordon_0 cv wcel iordon_0 iordon_1 epel iordon_0 cv iordon_1 cv wceq biid iordon_1 iordon_0 epel 3orbi123i sylibr syl2an rgen2a iordon_0 iordon_1 con0 cep dfwe2 mpbir2an con0 df-ord mpbir2an $.
$}
$( The epsilon relation well-orders the class of ordinal numbers.
     Proposition 4.8(g) of [Mendelson] p. 244.  (Contributed by NM,
     1-Nov-2003.) $)
${
	epweon $p |- _E We On $= con0 word con0 cep wwe ordon con0 ordwe ax-mp $.
$}
$( No set contains all ordinal numbers.  Proposition 7.13 of [TakeutiZaring]
     p. 38, but without using the Axiom of Regularity.  This is also known as
     the Burali-Forti paradox (remark in [Enderton] p. 194).  In 1897, Cesare
     Burali-Forti noticed that since the "set" of all ordinal numbers is an
     ordinal class ( ~ ordon ), it must be both an element of the set of all
     ordinal numbers yet greater than every such element.  ZF set theory
     resolves this paradox by not allowing the class of all ordinal numbers to
     be a set (so instead it is a proper class).  Here we prove the denial of
     its existence.  (Contributed by NM, 18-May-1994.) $)
${
	onprc $p |- -. On e. _V $= con0 cvv wcel con0 con0 wcel con0 word con0 con0 wcel wn ordon con0 ordirr ax-mp con0 cvv wcel con0 con0 wcel con0 word ordon con0 cvv elong mpbiri mto $.
$}
$( The union of a class of ordinal numbers is ordinal.  Proposition 7.19 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 30-May-1994.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	$d x y A $.
	issorduni_0 $f set x $.
	issorduni_1 $f set y $.
	fssorduni_0 $f class A $.
	ssorduni $p |- ( A C_ On -> Ord U. A ) $= fssorduni_0 con0 wss fssorduni_0 cuni wtr fssorduni_0 cuni con0 wss fssorduni_0 cuni word fssorduni_0 con0 wss issorduni_0 cv fssorduni_0 cuni wss issorduni_0 fssorduni_0 cuni wral fssorduni_0 cuni wtr fssorduni_0 con0 wss issorduni_0 cv fssorduni_0 cuni wss issorduni_0 fssorduni_0 cuni issorduni_0 cv fssorduni_0 cuni wcel issorduni_0 cv issorduni_1 cv wcel issorduni_1 fssorduni_0 wrex fssorduni_0 con0 wss issorduni_0 cv fssorduni_0 cuni wss issorduni_1 issorduni_0 cv fssorduni_0 eluni2 fssorduni_0 con0 wss issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv fssorduni_0 cuni wss issorduni_1 fssorduni_0 fssorduni_0 con0 wss issorduni_1 cv fssorduni_0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv issorduni_1 cv wss issorduni_1 cv fssorduni_0 wcel wa issorduni_0 cv fssorduni_0 cuni wss fssorduni_0 con0 wss issorduni_1 cv fssorduni_0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv issorduni_1 cv wss wi wi issorduni_1 cv fssorduni_0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv issorduni_1 cv wss issorduni_1 cv fssorduni_0 wcel wa wi wi fssorduni_0 con0 wss issorduni_1 cv fssorduni_0 wcel issorduni_1 cv con0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv issorduni_1 cv wss wi fssorduni_0 con0 issorduni_1 cv ssel issorduni_1 cv issorduni_0 cv onelss syl6 issorduni_1 cv fssorduni_0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv issorduni_1 cv wss anc2r syl issorduni_0 cv issorduni_1 cv fssorduni_0 ssuni syl8 rexlimdv syl5bi ralrimiv issorduni_0 fssorduni_0 cuni dftr3 sylibr fssorduni_0 con0 wss issorduni_0 fssorduni_0 cuni con0 issorduni_0 cv fssorduni_0 cuni wcel issorduni_0 cv issorduni_1 cv wcel issorduni_1 fssorduni_0 wrex fssorduni_0 con0 wss issorduni_0 cv con0 wcel issorduni_1 issorduni_0 cv fssorduni_0 eluni2 fssorduni_0 con0 wss issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv con0 wcel issorduni_1 fssorduni_0 fssorduni_0 con0 wss issorduni_1 cv fssorduni_0 wcel issorduni_1 cv con0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv con0 wcel wi fssorduni_0 con0 issorduni_1 cv ssel issorduni_1 cv con0 wcel issorduni_0 cv issorduni_1 cv wcel issorduni_0 cv con0 wcel issorduni_1 cv issorduni_0 cv onelon ex syl6 rexlimdv syl5bi ssrdv fssorduni_0 cuni wtr fssorduni_0 cuni con0 wss con0 word fssorduni_0 cuni word ordon fssorduni_0 cuni wtr fssorduni_0 cuni con0 wss con0 word fssorduni_0 cuni word fssorduni_0 cuni con0 trssord 3exp mpii sylc $.
$}
$( The union of a set of ordinal numbers is an ordinal number.  Theorem 9 of
     [Suppes] p. 132.  (Contributed by NM, 1-Nov-2003.) $)
${
	fssonuni_0 $f class A $.
	fssonuni_1 $f class V $.
	ssonuni $p |- ( A e. V -> ( A C_ On -> U. A e. On ) ) $= fssonuni_0 con0 wss fssonuni_0 cuni con0 wcel fssonuni_0 fssonuni_1 wcel fssonuni_0 cuni word fssonuni_0 ssorduni fssonuni_0 fssonuni_1 wcel fssonuni_0 cuni cvv wcel fssonuni_0 cuni con0 wcel fssonuni_0 cuni word wb fssonuni_0 fssonuni_1 uniexg fssonuni_0 cuni cvv elong syl syl5ibr $.
$}
$( The union of a set of ordinal numbers is an ordinal number.  Corollary
       7N(d) of [Enderton] p. 193.  (Contributed by NM, 20-Sep-2003.) $)
${
	fssonunii_0 $f class A $.
	essonunii_0 $e |- A e. _V $.
	ssonunii $p |- ( A C_ On -> U. A e. On ) $= fssonunii_0 cvv wcel fssonunii_0 con0 wss fssonunii_0 cuni con0 wcel wi essonunii_0 fssonunii_0 cvv ssonuni ax-mp $.
$}
$( A way to express the ordinal property of a class in terms of the class of
     ordinal numbers.  Corollary 7.14 of [TakeutiZaring] p. 38 and its
     converse.  (Contributed by NM, 1-Jun-2003.) $)
${
	fordeleqon_0 $f class A $.
	ordeleqon $p |- ( Ord A <-> ( A e. On \/ A = On ) ) $= fordeleqon_0 word fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq wo fordeleqon_0 word fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq wo con0 fordeleqon_0 wcel con0 fordeleqon_0 wcel con0 cvv wcel onprc con0 fordeleqon_0 elex mto fordeleqon_0 word fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq wo con0 fordeleqon_0 wcel fordeleqon_0 word fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq con0 fordeleqon_0 wcel w3o fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq wo con0 fordeleqon_0 wcel wo fordeleqon_0 word con0 word fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq con0 fordeleqon_0 wcel w3o ordon fordeleqon_0 con0 ordtri3or mpan2 fordeleqon_0 con0 wcel fordeleqon_0 con0 wceq con0 fordeleqon_0 wcel df-3or sylib ord mt3i fordeleqon_0 con0 wcel fordeleqon_0 word fordeleqon_0 con0 wceq fordeleqon_0 eloni fordeleqon_0 con0 wceq fordeleqon_0 word con0 word ordon fordeleqon_0 con0 ordeq mpbiri jaoi impbii $.
$}
$( Any ordinal class is a subclass of the class of ordinal numbers.
     Corollary 7.15 of [TakeutiZaring] p. 38.  (Contributed by NM,
     18-May-1994.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	fordsson_0 $f class A $.
	ordsson $p |- ( Ord A -> A C_ On ) $= fordsson_0 word con0 word fordsson_0 con0 wss ordon fordsson_0 word con0 word wa fordsson_0 con0 wss fordsson_0 con0 wcel fordsson_0 con0 wceq wo fordsson_0 word fordsson_0 con0 wcel fordsson_0 con0 wceq wo con0 word fordsson_0 word fordsson_0 con0 wcel fordsson_0 con0 wceq wo fordsson_0 ordeleqon biimpi adantr fordsson_0 con0 ordsseleq mpbird mpan2 $.
$}
$( An ordinal number is a subset of the class of ordinal numbers.
     (Contributed by NM, 5-Jun-1994.) $)
${
	fonss_0 $f class A $.
	onss $p |- ( A e. On -> A C_ On ) $= fonss_0 con0 wcel fonss_0 word fonss_0 con0 wss fonss_0 eloni fonss_0 ordsson syl $.
$}
$( Two ways of saying a class of ordinals is unbounded.  (Contributed by
     Mario Carneiro, 8-Jun-2013.) $)
${
	fssonprc_0 $f class A $.
	ssonprc $p |- ( A C_ On -> ( A e/ _V <-> U. A = On ) ) $= fssonprc_0 cvv wnel fssonprc_0 cvv wcel wn fssonprc_0 con0 wss fssonprc_0 cuni con0 wceq fssonprc_0 cvv df-nel fssonprc_0 con0 wss fssonprc_0 cvv wcel wn fssonprc_0 cuni con0 wceq fssonprc_0 con0 wss fssonprc_0 cuni con0 wceq fssonprc_0 cvv wcel fssonprc_0 con0 wss fssonprc_0 cuni con0 wceq wn fssonprc_0 cuni con0 wcel fssonprc_0 cvv wcel fssonprc_0 con0 wss fssonprc_0 cuni con0 wceq fssonprc_0 cuni con0 wcel fssonprc_0 con0 wss fssonprc_0 cuni con0 wcel fssonprc_0 cuni con0 wceq fssonprc_0 con0 wss fssonprc_0 cuni word fssonprc_0 cuni con0 wcel fssonprc_0 cuni con0 wceq wo fssonprc_0 ssorduni fssonprc_0 cuni ordeleqon sylib orcomd ord fssonprc_0 cuni con0 wcel fssonprc_0 cuni cvv wcel fssonprc_0 cvv wcel fssonprc_0 cuni con0 elex fssonprc_0 uniexb sylibr syl6 con1d fssonprc_0 cuni con0 wceq fssonprc_0 cvv wcel con0 cvv wcel onprc fssonprc_0 cvv wcel fssonprc_0 cuni cvv wcel fssonprc_0 cuni con0 wceq con0 cvv wcel fssonprc_0 cvv uniexg fssonprc_0 cuni con0 cvv eleq1 syl5ib mtoi impbid1 syl5bb $.
$}
$( The union of an ordinal number is an ordinal number.  (Contributed by NM,
     29-Sep-2006.) $)
${
	fonuni_0 $f class A $.
	onuni $p |- ( A e. On -> U. A e. On ) $= fonuni_0 con0 wcel fonuni_0 con0 wss fonuni_0 cuni con0 wcel fonuni_0 onss fonuni_0 con0 ssonuni mpd $.
$}
$( The union of an ordinal class is ordinal.  (Contributed by NM,
     12-Sep-2003.) $)
${
	forduni_0 $f class A $.
	orduni $p |- ( Ord A -> Ord U. A ) $= forduni_0 word forduni_0 con0 wss forduni_0 cuni word forduni_0 ordsson forduni_0 ssorduni syl $.
$}
$( The intersection (infimum) of a non-empty class of ordinal numbers
       belongs to the class.  Compare Exercise 4 of [TakeutiZaring] p. 45.
       (Contributed by NM, 31-Jan-1997.) $)
${
	$d x y z A $.
	ionint_0 $f set x $.
	ionint_1 $f set y $.
	ionint_2 $f set z $.
	fonint_0 $f class A $.
	onint $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. A ) $= fonint_0 con0 wss fonint_0 c0 wne fonint_0 cint fonint_0 wcel fonint_0 con0 wss fonint_0 c0 wne wa fonint_0 ionint_0 cv cin c0 wceq ionint_0 fonint_0 wrex fonint_0 con0 wss fonint_0 cint fonint_0 wcel con0 word fonint_0 con0 wss fonint_0 c0 wne fonint_0 ionint_0 cv cin c0 wceq ionint_0 fonint_0 wrex ordon ionint_0 con0 fonint_0 tz7.5 mp3an1 fonint_0 con0 wss fonint_0 ionint_0 cv cin c0 wceq fonint_0 cint fonint_0 wcel ionint_0 fonint_0 fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq fonint_0 cint fonint_0 wcel wi fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq ionint_0 cv fonint_0 wcel fonint_0 cint fonint_0 wcel fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq ionint_0 cv fonint_0 wcel fonint_0 cint fonint_0 wcel wi fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq wa wa ionint_0 cv fonint_0 wcel fonint_0 cint fonint_0 wcel fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq wa wa ionint_0 cv fonint_0 cint fonint_0 fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq wa wa ionint_0 cv fonint_0 cint fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq wa wa ionint_1 ionint_0 cv fonint_0 cint fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq ionint_1 cv ionint_0 cv wcel ionint_1 cv fonint_0 cint wcel wi ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq ionint_1 cv fonint_0 cint wcel ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv fonint_0 wcel fonint_0 ionint_0 cv cin c0 wceq ionint_1 cv fonint_0 cint wcel wi fonint_0 con0 wss ionint_0 cv fonint_0 wcel wa ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv con0 wcel wa fonint_0 ionint_0 cv cin c0 wceq ionint_1 cv fonint_0 cint wcel wi fonint_0 con0 wss ionint_0 cv fonint_0 wcel ionint_0 cv con0 wcel fonint_0 con0 ionint_0 cv ssel imdistani ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv con0 wcel wa wa ionint_2 cv ionint_0 cv wcel wn ionint_2 fonint_0 wral ionint_1 cv ionint_2 cv wcel ionint_2 fonint_0 wral fonint_0 ionint_0 cv cin c0 wceq ionint_1 cv fonint_0 cint wcel ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv con0 wcel wa wa ionint_2 cv ionint_0 cv wcel wn ionint_1 cv ionint_2 cv wcel ionint_2 fonint_0 ionint_1 cv ionint_0 cv wcel fonint_0 con0 wss ionint_0 cv con0 wcel wa ionint_2 cv fonint_0 wcel ionint_2 cv ionint_0 cv wcel wn ionint_1 cv ionint_2 cv wcel wi fonint_0 con0 wss ionint_0 cv con0 wcel wa ionint_2 cv fonint_0 wcel ionint_2 cv ionint_0 cv wcel wn ionint_1 cv ionint_0 cv wcel ionint_1 cv ionint_2 cv wcel fonint_0 con0 wss ionint_2 cv fonint_0 wcel ionint_2 cv con0 wcel ionint_0 cv con0 wcel ionint_2 cv ionint_0 cv wcel wn ionint_1 cv ionint_0 cv wcel ionint_1 cv ionint_2 cv wcel wi wi fonint_0 con0 ionint_2 cv ssel ionint_0 cv con0 wcel ionint_2 cv con0 wcel ionint_2 cv ionint_0 cv wcel wn ionint_1 cv ionint_0 cv wcel ionint_1 cv ionint_2 cv wcel wi wi ionint_0 cv con0 wcel ionint_2 cv con0 wcel wa ionint_2 cv ionint_0 cv wcel wn ionint_0 cv ionint_2 cv wss ionint_1 cv ionint_0 cv wcel ionint_1 cv ionint_2 cv wcel wi ionint_0 cv ionint_2 cv ontri1 ionint_0 cv ionint_2 cv ionint_1 cv ssel syl6bir ex sylan9 com4r imp31 ralimdva ionint_2 fonint_0 ionint_0 cv disj ionint_2 ionint_1 cv fonint_0 ionint_1 vex elint2 3imtr4g sylan2 exp32 com4l imp32 ssrdv ionint_0 cv fonint_0 wcel fonint_0 cint ionint_0 cv wss fonint_0 con0 wss fonint_0 ionint_0 cv cin c0 wceq ionint_0 cv fonint_0 intss1 ad2antrl eqssd eleq1d biimpd exp32 com34 pm2.43d rexlimdv syl5 anabsi5 $.
$}
$( The intersection of a class of ordinal numbers is zero iff the class
     contains zero.  (Contributed by NM, 24-Apr-2004.) $)
${
	fonint0_0 $f class A $.
	onint0 $p |- ( A C_ On -> ( |^| A = (/) <-> (/) e. A ) ) $= fonint0_0 con0 wss fonint0_0 cint c0 wceq c0 fonint0_0 wcel fonint0_0 con0 wss fonint0_0 cint c0 wceq c0 fonint0_0 wcel fonint0_0 con0 wss fonint0_0 cint c0 wceq wa fonint0_0 cint fonint0_0 wcel c0 fonint0_0 wcel fonint0_0 cint c0 wceq fonint0_0 con0 wss fonint0_0 c0 wne fonint0_0 cint fonint0_0 wcel fonint0_0 cint c0 wceq fonint0_0 cint cvv wcel fonint0_0 c0 wne fonint0_0 cint c0 wceq fonint0_0 cint cvv wcel c0 cvv wcel 0ex fonint0_0 cint c0 cvv eleq1 mpbiri fonint0_0 intex sylibr fonint0_0 onint sylan2 fonint0_0 cint c0 wceq fonint0_0 cint fonint0_0 wcel c0 fonint0_0 wcel wb fonint0_0 con0 wss fonint0_0 cint c0 fonint0_0 eleq1 adantl mpbid ex fonint0_0 int0el impbid1 $.
$}
$( A non-empty class of ordinal numbers has the smallest member.  Exercise
       9 of [TakeutiZaring] p. 40.  (Contributed by NM, 3-Oct-2003.) $)
${
	$d x y A $.
	fonssmin_0 $f set x $.
	fonssmin_1 $f set y $.
	fonssmin_2 $f class A $.
	onssmin $p |- ( ( A C_ On /\ A =/= (/) ) -> E. x e. A A. y e. A x C_ y ) $= fonssmin_2 con0 wss fonssmin_2 c0 wne wa fonssmin_2 cint fonssmin_2 wcel fonssmin_2 cint fonssmin_1 cv wss fonssmin_1 fonssmin_2 wral fonssmin_0 cv fonssmin_1 cv wss fonssmin_1 fonssmin_2 wral fonssmin_0 fonssmin_2 wrex fonssmin_2 onint fonssmin_2 cint fonssmin_1 cv wss fonssmin_1 fonssmin_2 fonssmin_1 cv fonssmin_2 intss1 rgen fonssmin_0 cv fonssmin_1 cv wss fonssmin_1 fonssmin_2 wral fonssmin_2 cint fonssmin_1 cv wss fonssmin_1 fonssmin_2 wral fonssmin_0 fonssmin_2 cint fonssmin_2 fonssmin_0 cv fonssmin_2 cint wceq fonssmin_0 cv fonssmin_1 cv wss fonssmin_2 cint fonssmin_1 cv wss fonssmin_1 fonssmin_2 fonssmin_0 cv fonssmin_2 cint fonssmin_1 cv sseq1 ralbidv rspcev sylancl $.
$}
$( If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses explicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 29-Sep-2003.) $)
${
	fonminesb_0 $f wff ph $.
	fonminesb_1 $f set x $.
	onminesb $p |- ( E. x e. On ph -> [. |^| { x e. On | ph } / x ]. ph ) $= fonminesb_0 fonminesb_1 con0 wrex fonminesb_0 fonminesb_1 con0 crab cint fonminesb_0 fonminesb_1 con0 crab wcel fonminesb_0 fonminesb_1 fonminesb_0 fonminesb_1 con0 crab cint wsbc fonminesb_0 fonminesb_1 con0 wrex fonminesb_0 fonminesb_1 con0 crab c0 wne fonminesb_0 fonminesb_1 con0 crab cint fonminesb_0 fonminesb_1 con0 crab wcel fonminesb_0 fonminesb_1 con0 rabn0 fonminesb_0 fonminesb_1 con0 crab con0 wss fonminesb_0 fonminesb_1 con0 crab c0 wne fonminesb_0 fonminesb_1 con0 crab cint fonminesb_0 fonminesb_1 con0 crab wcel fonminesb_0 fonminesb_1 con0 ssrab2 fonminesb_0 fonminesb_1 con0 crab onint mpan sylbir fonminesb_0 fonminesb_1 con0 crab cint fonminesb_0 fonminesb_1 con0 crab wcel fonminesb_0 fonminesb_1 con0 crab cint con0 wcel fonminesb_0 fonminesb_1 fonminesb_0 fonminesb_1 con0 crab cint wsbc fonminesb_0 fonminesb_1 fonminesb_0 fonminesb_1 con0 crab cint con0 fonminesb_1 con0 nfcv elrabsf simprbi syl $.
$}
$( If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses implicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)
${
	fonminsb_0 $f wff ph $.
	fonminsb_1 $f wff ps $.
	fonminsb_2 $f set x $.
	eonminsb_0 $e |- F/ x ps $.
	eonminsb_1 $e |- ( x = |^| { x e. On | ph } -> ( ph <-> ps ) ) $.
	onminsb $p |- ( E. x e. On ph -> ps ) $= fonminsb_0 fonminsb_2 con0 wrex fonminsb_0 fonminsb_2 con0 crab cint fonminsb_0 fonminsb_2 con0 crab wcel fonminsb_1 fonminsb_0 fonminsb_2 con0 wrex fonminsb_0 fonminsb_2 con0 crab c0 wne fonminsb_0 fonminsb_2 con0 crab cint fonminsb_0 fonminsb_2 con0 crab wcel fonminsb_0 fonminsb_2 con0 rabn0 fonminsb_0 fonminsb_2 con0 crab con0 wss fonminsb_0 fonminsb_2 con0 crab c0 wne fonminsb_0 fonminsb_2 con0 crab cint fonminsb_0 fonminsb_2 con0 crab wcel fonminsb_0 fonminsb_2 con0 ssrab2 fonminsb_0 fonminsb_2 con0 crab onint mpan sylbir fonminsb_0 fonminsb_2 con0 crab cint fonminsb_0 fonminsb_2 con0 crab wcel fonminsb_0 fonminsb_2 con0 crab cint con0 wcel fonminsb_1 fonminsb_0 fonminsb_1 fonminsb_2 fonminsb_0 fonminsb_2 con0 crab cint con0 fonminsb_2 fonminsb_0 fonminsb_2 con0 crab fonminsb_0 fonminsb_2 con0 nfrab1 nfint fonminsb_2 con0 nfcv eonminsb_0 eonminsb_1 elrabf simprbi syl $.
$}
$( The intersection of a non-empty collection of ordinal numbers is an
     ordinal number.  Compare Exercise 6 of [TakeutiZaring] p. 44.
     (Contributed by NM, 29-Jan-1997.) $)
${
	foninton_0 $f class A $.
	oninton $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. On ) $= foninton_0 con0 wss foninton_0 c0 wne foninton_0 cint con0 wcel foninton_0 con0 wss foninton_0 c0 wne foninton_0 cint foninton_0 wcel foninton_0 cint con0 wcel foninton_0 con0 wss foninton_0 c0 wne foninton_0 cint foninton_0 wcel foninton_0 onint ex foninton_0 con0 foninton_0 cint ssel syld imp $.
$}
$( The intersection of a class of ordinal numbers exists iff it is an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)
${
	fonintrab_0 $f wff ph $.
	fonintrab_1 $f set x $.
	onintrab $p |- ( |^| { x e. On | ph } e. _V <-> |^| { x e. On | ph } e. On ) $= fonintrab_0 fonintrab_1 con0 crab cint cvv wcel fonintrab_0 fonintrab_1 con0 crab cint con0 wcel fonintrab_0 fonintrab_1 con0 crab cint cvv wcel fonintrab_0 fonintrab_1 con0 crab c0 wne fonintrab_0 fonintrab_1 con0 crab cint con0 wcel fonintrab_0 fonintrab_1 con0 crab intex fonintrab_0 fonintrab_1 con0 crab con0 wss fonintrab_0 fonintrab_1 con0 crab c0 wne fonintrab_0 fonintrab_1 con0 crab cint con0 wcel fonintrab_0 fonintrab_1 con0 ssrab2 fonintrab_0 fonintrab_1 con0 crab oninton mpan sylbir fonintrab_0 fonintrab_1 con0 crab cint con0 elex impbii $.
$}
$( An existence condition equivalent to an intersection's being an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)
${
	fonintrab2_0 $f wff ph $.
	fonintrab2_1 $f set x $.
	onintrab2 $p |- ( E. x e. On ph <-> |^| { x e. On | ph } e. On ) $= fonintrab2_0 fonintrab2_1 con0 wrex fonintrab2_0 fonintrab2_1 con0 crab cint cvv wcel fonintrab2_0 fonintrab2_1 con0 crab cint con0 wcel fonintrab2_0 fonintrab2_1 con0 intexrab fonintrab2_0 fonintrab2_1 onintrab bitri $.
$}
$( No member of a set of ordinal numbers belongs to its minimum.
     (Contributed by NM, 2-Feb-1997.) $)
${
	fonnmin_0 $f class A $.
	fonnmin_1 $f class B $.
	onnmin $p |- ( ( A C_ On /\ B e. A ) -> -. B e. |^| A ) $= fonnmin_0 con0 wss fonnmin_1 fonnmin_0 wcel wa fonnmin_0 cint fonnmin_1 wss fonnmin_1 fonnmin_0 cint wcel wn fonnmin_1 fonnmin_0 wcel fonnmin_0 cint fonnmin_1 wss fonnmin_0 con0 wss fonnmin_1 fonnmin_0 intss1 adantl fonnmin_0 con0 wss fonnmin_1 fonnmin_0 wcel wa fonnmin_0 cint con0 wcel fonnmin_1 con0 wcel fonnmin_0 cint fonnmin_1 wss fonnmin_1 fonnmin_0 cint wcel wn wb fonnmin_1 fonnmin_0 wcel fonnmin_0 con0 wss fonnmin_0 c0 wne fonnmin_0 cint con0 wcel fonnmin_0 fonnmin_1 ne0i fonnmin_0 oninton sylan2 fonnmin_0 con0 fonnmin_1 ssel2 fonnmin_0 cint fonnmin_1 ontri1 syl2anc mpbid $.
$}
$( An ordinal number smaller than the minimum of a set of ordinal numbers
       does not have the property determining that set. ` ps ` is the wff
       resulting from the substitution of ` A ` for ` x ` in wff ` ph ` .
       (Contributed by NM, 9-Nov-2003.) $)
${
	$d x A $.
	$d x ps $.
	fonnminsb_0 $f wff ph $.
	fonnminsb_1 $f wff ps $.
	fonnminsb_2 $f set x $.
	fonnminsb_3 $f class A $.
	eonnminsb_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	onnminsb $p |- ( A e. On -> ( A e. |^| { x e. On | ph } -> -. ps ) ) $= fonnminsb_3 con0 wcel fonnminsb_1 fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab cint wcel fonnminsb_3 con0 wcel fonnminsb_1 fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab cint wcel wn fonnminsb_3 con0 wcel fonnminsb_1 wa fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab wcel fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab cint wcel wn fonnminsb_0 fonnminsb_1 fonnminsb_2 fonnminsb_3 con0 eonnminsb_0 elrab fonnminsb_0 fonnminsb_2 con0 crab con0 wss fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab wcel fonnminsb_3 fonnminsb_0 fonnminsb_2 con0 crab cint wcel wn fonnminsb_0 fonnminsb_2 con0 ssrab2 fonnminsb_0 fonnminsb_2 con0 crab fonnminsb_3 onnmin mpan sylbir ex con2d $.
$}
$( A way to show that an ordinal number equals the minimum of a non-empty
       collection of ordinal numbers: it must be in the collection, and it must
       not be larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)
${
	$d x A $.
	$d x B $.
	foneqmin_0 $f set x $.
	foneqmin_1 $f class A $.
	foneqmin_2 $f class B $.
	oneqmin $p |- ( ( B C_ On /\ B =/= (/) ) -> ( A = |^| B <-> ( A e. B /\ A. x e. A -. x e. B ) ) ) $= foneqmin_2 con0 wss foneqmin_2 c0 wne wa foneqmin_1 foneqmin_2 cint wceq foneqmin_1 foneqmin_2 wcel foneqmin_0 cv foneqmin_2 wcel wn foneqmin_0 foneqmin_1 wral wa foneqmin_2 con0 wss foneqmin_2 c0 wne wa foneqmin_1 foneqmin_2 cint wceq foneqmin_1 foneqmin_2 wcel foneqmin_0 cv foneqmin_2 wcel wn foneqmin_0 foneqmin_1 wral foneqmin_2 con0 wss foneqmin_2 c0 wne wa foneqmin_1 foneqmin_2 wcel foneqmin_1 foneqmin_2 cint wceq foneqmin_2 cint foneqmin_2 wcel foneqmin_2 onint foneqmin_1 foneqmin_2 cint foneqmin_2 eleq1 syl5ibrcom foneqmin_2 con0 wss foneqmin_1 foneqmin_2 cint wceq foneqmin_0 cv foneqmin_2 wcel wn foneqmin_0 foneqmin_1 wral wi foneqmin_2 c0 wne foneqmin_2 con0 wss foneqmin_1 foneqmin_2 cint wceq foneqmin_0 cv foneqmin_2 wcel wn foneqmin_0 foneqmin_1 foneqmin_1 foneqmin_2 cint wceq foneqmin_0 cv foneqmin_1 wcel foneqmin_0 cv foneqmin_2 cint wcel foneqmin_2 con0 wss foneqmin_0 cv foneqmin_2 wcel wn foneqmin_1 foneqmin_2 cint wceq foneqmin_0 cv foneqmin_1 wcel foneqmin_0 cv foneqmin_2 cint wcel foneqmin_1 foneqmin_2 cint foneqmin_0 cv eleq2 biimpd foneqmin_2 con0 wss foneqmin_0 cv foneqmin_2 wcel foneqmin_0 cv foneqmin_2 cint wcel foneqmin_2 con0 wss foneqmin_0 cv foneqmin_2 wcel foneqmin_0 cv foneqmin_2 cint wcel wn foneqmin_2 foneqmin_0 cv onnmin ex con2d syl9r ralrimdv adantr jcad foneqmin_2 con0 wss foneqmin_1 foneqmin_2 wcel foneqmin_0 cv foneqmin_2 wcel wn foneqmin_0 foneqmin_1 wral wa foneqmin_1 foneqmin_2 cint wceq wi foneqmin_2 c0 wne foneqmin_0 foneqmin_1 foneqmin_2 oneqmini adantr impbid $.
$}
$( Problem 2.5(ii) of [BellMachover] p. 471.  (Contributed by NM,
       20-Sep-2003.) $)
${
	$d x y A $.
	fbm2.5ii_0 $f set x $.
	fbm2.5ii_1 $f set y $.
	fbm2.5ii_2 $f class A $.
	ebm2.5ii_0 $e |- A e. _V $.
	bm2.5ii $p |- ( A C_ On -> U. A = |^| { x e. On | A. y e. A y C_ x } ) $= fbm2.5ii_2 con0 wss fbm2.5ii_2 cuni con0 wcel fbm2.5ii_2 cuni fbm2.5ii_1 cv fbm2.5ii_0 cv wss fbm2.5ii_1 fbm2.5ii_2 wral fbm2.5ii_0 con0 crab cint wceq fbm2.5ii_2 ebm2.5ii_0 ssonunii fbm2.5ii_2 cuni con0 wcel fbm2.5ii_1 cv fbm2.5ii_0 cv wss fbm2.5ii_1 fbm2.5ii_2 wral fbm2.5ii_0 con0 crab cint fbm2.5ii_2 cuni fbm2.5ii_0 cv wss fbm2.5ii_0 con0 crab cint fbm2.5ii_2 cuni fbm2.5ii_2 cuni fbm2.5ii_0 cv wss fbm2.5ii_0 con0 crab fbm2.5ii_1 cv fbm2.5ii_0 cv wss fbm2.5ii_1 fbm2.5ii_2 wral fbm2.5ii_0 con0 crab fbm2.5ii_2 cuni fbm2.5ii_0 cv wss fbm2.5ii_1 cv fbm2.5ii_0 cv wss fbm2.5ii_1 fbm2.5ii_2 wral fbm2.5ii_0 con0 fbm2.5ii_2 cuni fbm2.5ii_0 cv wss fbm2.5ii_1 cv fbm2.5ii_0 cv wss fbm2.5ii_1 fbm2.5ii_2 wral wb fbm2.5ii_0 cv con0 wcel fbm2.5ii_1 fbm2.5ii_2 fbm2.5ii_0 cv unissb a1i rabbiia inteqi fbm2.5ii_0 fbm2.5ii_2 cuni con0 intmin syl5reqr syl $.
$}
$( If a wff is true for an ordinal number, there is the smallest ordinal
       number for which it is true.  (Contributed by NM, 2-Feb-1997.)  (Proof
       shortened by Mario Carneiro, 20-Nov-2016.) $)
${
	$d x y z $.
	$d y z ph $.
	$d x z ps $.
	ionminex_0 $f set z $.
	fonminex_0 $f wff ph $.
	fonminex_1 $f wff ps $.
	fonminex_2 $f set x $.
	fonminex_3 $f set y $.
	eonminex_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	onminex $p |- ( E. x e. On ph -> E. x e. On ( ph /\ A. y e. x -. ps ) ) $= fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 ionminex_0 cv wral wa ionminex_0 con0 wrex fonminex_0 fonminex_1 wn fonminex_3 fonminex_2 cv wral wa fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 crab cint con0 wcel fonminex_0 fonminex_2 fonminex_0 fonminex_2 con0 crab cint wsbc fonminex_1 wn fonminex_3 fonminex_0 fonminex_2 con0 crab cint wral fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 ionminex_0 cv wral wa ionminex_0 con0 wrex fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 crab con0 wss fonminex_0 fonminex_2 con0 crab c0 wne fonminex_0 fonminex_2 con0 crab cint con0 wcel fonminex_0 fonminex_2 con0 ssrab2 fonminex_0 fonminex_2 con0 crab c0 wne fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 rabn0 biimpri fonminex_0 fonminex_2 con0 crab oninton sylancr fonminex_0 fonminex_2 onminesb fonminex_0 fonminex_2 con0 wrex fonminex_1 wn fonminex_3 fonminex_0 fonminex_2 con0 crab cint fonminex_3 cv fonminex_0 fonminex_2 con0 crab cint wcel fonminex_0 fonminex_2 con0 wrex fonminex_3 cv con0 wcel fonminex_1 wn fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 crab cint con0 fonminex_3 cv fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 crab cint con0 wcel fonminex_0 fonminex_2 con0 crab cint con0 wss fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 crab con0 wss fonminex_0 fonminex_2 con0 crab c0 wne fonminex_0 fonminex_2 con0 crab cint con0 wcel fonminex_0 fonminex_2 con0 ssrab2 fonminex_0 fonminex_2 con0 crab c0 wne fonminex_0 fonminex_2 con0 wrex fonminex_0 fonminex_2 con0 rabn0 biimpri fonminex_0 fonminex_2 con0 crab oninton sylancr fonminex_0 fonminex_2 con0 crab cint onss syl sseld fonminex_0 fonminex_1 fonminex_2 fonminex_3 cv eonminex_0 onnminsb syli ralrimiv fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 ionminex_0 cv wral wa fonminex_0 fonminex_2 fonminex_0 fonminex_2 con0 crab cint wsbc fonminex_1 wn fonminex_3 fonminex_0 fonminex_2 con0 crab cint wral wa ionminex_0 fonminex_0 fonminex_2 con0 crab cint con0 ionminex_0 cv fonminex_0 fonminex_2 con0 crab cint wceq fonminex_0 fonminex_2 ionminex_0 wsb fonminex_0 fonminex_2 fonminex_0 fonminex_2 con0 crab cint wsbc fonminex_1 wn fonminex_3 ionminex_0 cv wral fonminex_1 wn fonminex_3 fonminex_0 fonminex_2 con0 crab cint wral fonminex_0 fonminex_2 ionminex_0 fonminex_0 fonminex_2 con0 crab cint dfsbcq2 fonminex_1 wn fonminex_3 ionminex_0 cv fonminex_0 fonminex_2 con0 crab cint raleq anbi12d rspcev syl12anc fonminex_0 fonminex_1 wn fonminex_3 fonminex_2 cv wral wa fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 ionminex_0 cv wral wa fonminex_2 ionminex_0 con0 fonminex_0 fonminex_1 wn fonminex_3 fonminex_2 cv wral wa ionminex_0 nfv fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 ionminex_0 cv wral fonminex_2 fonminex_0 fonminex_2 ionminex_0 nfs1v fonminex_1 wn fonminex_3 ionminex_0 cv wral fonminex_2 nfv nfan fonminex_2 ionminex_0 weq fonminex_0 fonminex_0 fonminex_2 ionminex_0 wsb fonminex_1 wn fonminex_3 fonminex_2 cv wral fonminex_1 wn fonminex_3 ionminex_0 cv wral fonminex_0 fonminex_2 ionminex_0 sbequ12 fonminex_1 wn fonminex_3 fonminex_2 cv ionminex_0 cv raleq anbi12d cbvrex sylibr $.
$}
$( The class of all ordinal numbers is its own successor.  (Contributed by
     NM, 12-Sep-2003.) $)
${
	sucon $p |- suc On = On $= con0 cvv wcel wn con0 csuc con0 wceq onprc con0 sucprc ax-mp $.
$}
$( A successor exists iff its class argument exists.  (Contributed by NM,
     22-Jun-1998.) $)
${
	fsucexb_0 $f class A $.
	sucexb $p |- ( A e. _V <-> suc A e. _V ) $= fsucexb_0 cvv wcel fsucexb_0 csn cvv wcel wa fsucexb_0 fsucexb_0 csn cun cvv wcel fsucexb_0 cvv wcel fsucexb_0 csuc cvv wcel fsucexb_0 fsucexb_0 csn unexb fsucexb_0 csn cvv wcel fsucexb_0 cvv wcel fsucexb_0 snex biantru fsucexb_0 csuc fsucexb_0 fsucexb_0 csn cun cvv fsucexb_0 df-suc eleq1i 3bitr4i $.
$}
$( The successor of a set is a set (generalization).  (Contributed by NM,
     5-Jun-1994.) $)
${
	fsucexg_0 $f class A $.
	fsucexg_1 $f class V $.
	sucexg $p |- ( A e. V -> suc A e. _V ) $= fsucexg_0 fsucexg_1 wcel fsucexg_0 cvv wcel fsucexg_0 csuc cvv wcel fsucexg_0 fsucexg_1 elex fsucexg_0 sucexb sylib $.
$}
$( The successor of a set is a set.  (Contributed by NM, 30-Aug-1993.) $)
${
	fsucex_0 $f class A $.
	esucex_0 $e |- A e. _V $.
	sucex $p |- suc A e. _V $= fsucex_0 cvv wcel fsucex_0 csuc cvv wcel esucex_0 fsucex_0 cvv sucexg ax-mp $.
$}
$( The minimum of a class of ordinal numbers is less than the minimum of
       that class with its minimum removed.  (Contributed by NM,
       20-Nov-2003.) $)
${
	$d x A $.
	ionmindif2_0 $f set x $.
	fonmindif2_0 $f class A $.
	onmindif2 $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. |^| ( A \ { |^| A } ) ) $= fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa fonmindif2_0 cint fonmindif2_0 fonmindif2_0 cint csn cdif cint wcel fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 fonmindif2_0 fonmindif2_0 cint csn cdif wral fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 fonmindif2_0 fonmindif2_0 cint csn cdif ionmindif2_0 cv fonmindif2_0 fonmindif2_0 cint csn cdif wcel ionmindif2_0 cv fonmindif2_0 wcel ionmindif2_0 cv fonmindif2_0 cint wne wa fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 cv fonmindif2_0 fonmindif2_0 cint eldifsn fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel ionmindif2_0 cv fonmindif2_0 cint wne fonmindif2_0 cint ionmindif2_0 cv wcel fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel wa fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 cv fonmindif2_0 cint fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel wa fonmindif2_0 cint ionmindif2_0 cv wcel wn fonmindif2_0 cint ionmindif2_0 cv wceq ionmindif2_0 cv fonmindif2_0 cint wceq fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel wa fonmindif2_0 cint ionmindif2_0 cv wcel fonmindif2_0 cint ionmindif2_0 cv wceq fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel wa ionmindif2_0 cv fonmindif2_0 cint wcel wn fonmindif2_0 cint ionmindif2_0 cv wcel fonmindif2_0 cint ionmindif2_0 cv wceq wo fonmindif2_0 con0 wss ionmindif2_0 cv fonmindif2_0 wcel ionmindif2_0 cv fonmindif2_0 cint wcel wn fonmindif2_0 c0 wne fonmindif2_0 ionmindif2_0 cv onnmin adantlr fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa ionmindif2_0 cv fonmindif2_0 wcel wa fonmindif2_0 cint con0 wcel ionmindif2_0 cv con0 wcel ionmindif2_0 cv fonmindif2_0 cint wcel wn fonmindif2_0 cint ionmindif2_0 cv wcel fonmindif2_0 cint ionmindif2_0 cv wceq wo wb fonmindif2_0 con0 wss fonmindif2_0 c0 wne wa fonmindif2_0 cint con0 wcel ionmindif2_0 cv fonmindif2_0 wcel fonmindif2_0 oninton adantr fonmindif2_0 con0 wss ionmindif2_0 cv fonmindif2_0 wcel ionmindif2_0 cv con0 wcel fonmindif2_0 c0 wne fonmindif2_0 con0 ionmindif2_0 cv ssel2 adantlr fonmindif2_0 cint con0 wcel ionmindif2_0 cv con0 wcel wa fonmindif2_0 cint ionmindif2_0 cv wss ionmindif2_0 cv fonmindif2_0 cint wcel wn fonmindif2_0 cint ionmindif2_0 cv wcel fonmindif2_0 cint ionmindif2_0 cv wceq wo fonmindif2_0 cint ionmindif2_0 cv ontri1 fonmindif2_0 cint ionmindif2_0 cv onsseleq bitr3d syl2anc mpbid ord fonmindif2_0 cint ionmindif2_0 cv eqcom syl6ib necon1ad expimpd syl5bi ralrimiv fonmindif2_0 c0 wne fonmindif2_0 cint fonmindif2_0 fonmindif2_0 cint csn cdif cint wcel fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 fonmindif2_0 fonmindif2_0 cint csn cdif wral wb fonmindif2_0 con0 wss fonmindif2_0 c0 wne fonmindif2_0 cint cvv wcel fonmindif2_0 cint fonmindif2_0 fonmindif2_0 cint csn cdif cint wcel fonmindif2_0 cint ionmindif2_0 cv wcel ionmindif2_0 fonmindif2_0 fonmindif2_0 cint csn cdif wral wb fonmindif2_0 intex ionmindif2_0 fonmindif2_0 cint fonmindif2_0 fonmindif2_0 cint csn cdif cvv elintg sylbi adantl mpbird $.
$}
$( The successor of an ordinal number is an ordinal number.  Proposition
       7.24 of [TakeutiZaring] p. 41.  (Contributed by NM, 6-Jun-1994.) $)
${
	$d x A $.
	isuceloni_0 $f set x $.
	fsuceloni_0 $f class A $.
	suceloni $p |- ( A e. On -> suc A e. On ) $= fsuceloni_0 con0 wcel fsuceloni_0 csuc con0 wcel fsuceloni_0 csuc word fsuceloni_0 con0 wcel fsuceloni_0 csuc wtr fsuceloni_0 csuc con0 wss fsuceloni_0 csuc word fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 csuc wss isuceloni_0 fsuceloni_0 csuc wral fsuceloni_0 csuc wtr fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 csuc wss isuceloni_0 fsuceloni_0 csuc fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 csuc wcel isuceloni_0 cv fsuceloni_0 wss fsuceloni_0 fsuceloni_0 csuc wss isuceloni_0 cv fsuceloni_0 csuc wss fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 wcel isuceloni_0 cv fsuceloni_0 csn wcel wo isuceloni_0 cv fsuceloni_0 wss isuceloni_0 cv fsuceloni_0 wss wo isuceloni_0 cv fsuceloni_0 csuc wcel isuceloni_0 cv fsuceloni_0 wss fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 wcel isuceloni_0 cv fsuceloni_0 wss isuceloni_0 cv fsuceloni_0 csn wcel isuceloni_0 cv fsuceloni_0 wss fsuceloni_0 isuceloni_0 cv onelss isuceloni_0 cv fsuceloni_0 csn wcel isuceloni_0 cv fsuceloni_0 wss wi fsuceloni_0 con0 wcel isuceloni_0 cv fsuceloni_0 csn wcel isuceloni_0 cv fsuceloni_0 wceq isuceloni_0 cv fsuceloni_0 wss isuceloni_0 fsuceloni_0 elsn isuceloni_0 cv fsuceloni_0 eqimss sylbi a1i orim12d isuceloni_0 cv fsuceloni_0 csuc wcel isuceloni_0 cv fsuceloni_0 fsuceloni_0 csn cun wcel isuceloni_0 cv fsuceloni_0 wcel isuceloni_0 cv fsuceloni_0 csn wcel wo fsuceloni_0 csuc fsuceloni_0 fsuceloni_0 csn cun isuceloni_0 cv fsuceloni_0 df-suc eleq2i isuceloni_0 cv fsuceloni_0 fsuceloni_0 csn elun bitr2i isuceloni_0 cv fsuceloni_0 wss oridm 3imtr3g fsuceloni_0 sssucid isuceloni_0 cv fsuceloni_0 fsuceloni_0 csuc sstr2 syl6mpi ralrimiv isuceloni_0 fsuceloni_0 csuc dftr3 sylibr fsuceloni_0 con0 wcel fsuceloni_0 csuc fsuceloni_0 fsuceloni_0 csn cun con0 fsuceloni_0 df-suc fsuceloni_0 con0 wcel fsuceloni_0 fsuceloni_0 csn con0 fsuceloni_0 onss fsuceloni_0 con0 snssi unssd syl5eqss fsuceloni_0 csuc wtr fsuceloni_0 csuc con0 wss con0 word fsuceloni_0 csuc word ordon fsuceloni_0 csuc wtr fsuceloni_0 csuc con0 wss con0 word fsuceloni_0 csuc word fsuceloni_0 csuc con0 trssord 3exp mpii sylc fsuceloni_0 con0 wcel fsuceloni_0 csuc cvv wcel fsuceloni_0 csuc con0 wcel fsuceloni_0 csuc word wb fsuceloni_0 con0 sucexg fsuceloni_0 csuc cvv elong syl mpbird $.
$}
$( The successor of an ordinal class is ordinal.  (Contributed by NM,
     3-Apr-1995.) $)
${
	fordsuc_0 $f class A $.
	ordsuc $p |- ( Ord A <-> Ord suc A ) $= fordsuc_0 cvv wcel fordsuc_0 word fordsuc_0 csuc word wb fordsuc_0 cvv wcel fordsuc_0 word fordsuc_0 csuc word fordsuc_0 cvv wcel fordsuc_0 word fordsuc_0 con0 wcel fordsuc_0 csuc word fordsuc_0 cvv elong fordsuc_0 con0 wcel fordsuc_0 csuc con0 wcel fordsuc_0 csuc word fordsuc_0 suceloni fordsuc_0 csuc eloni syl syl6bir fordsuc_0 cvv wcel fordsuc_0 fordsuc_0 csuc wcel fordsuc_0 csuc word fordsuc_0 word fordsuc_0 cvv sucidg fordsuc_0 csuc word fordsuc_0 fordsuc_0 csuc wcel fordsuc_0 word fordsuc_0 csuc fordsuc_0 ordelord ex syl5com impbid fordsuc_0 cvv wcel wn fordsuc_0 fordsuc_0 csuc wceq fordsuc_0 word fordsuc_0 csuc word wb fordsuc_0 cvv wcel wn fordsuc_0 csuc fordsuc_0 fordsuc_0 sucprc eqcomd fordsuc_0 fordsuc_0 csuc ordeq syl pm2.61i $.
$}
$( The collection of ordinals in the power class of an ordinal is its
       successor.  (Contributed by NM, 30-Jan-2005.) $)
${
	$d x A $.
	iordpwsuc_0 $f set x $.
	fordpwsuc_0 $f class A $.
	ordpwsuc $p |- ( Ord A -> ( ~P A i^i On ) = suc A ) $= fordpwsuc_0 word iordpwsuc_0 fordpwsuc_0 cpw con0 cin fordpwsuc_0 csuc iordpwsuc_0 cv fordpwsuc_0 cpw con0 cin wcel iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 wss wa fordpwsuc_0 word iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv fordpwsuc_0 cpw con0 cin wcel iordpwsuc_0 cv fordpwsuc_0 cpw wcel iordpwsuc_0 cv con0 wcel wa iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 wss wa iordpwsuc_0 cv fordpwsuc_0 cpw con0 elin iordpwsuc_0 cv fordpwsuc_0 cpw wcel iordpwsuc_0 cv fordpwsuc_0 wss iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 iordpwsuc_0 vex elpw anbi2ci bitri fordpwsuc_0 word iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 wss wa iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 csuc wcel wa iordpwsuc_0 cv fordpwsuc_0 csuc wcel fordpwsuc_0 word iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 wss iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv con0 wcel fordpwsuc_0 word iordpwsuc_0 cv fordpwsuc_0 wss iordpwsuc_0 cv fordpwsuc_0 csuc wcel wb iordpwsuc_0 cv fordpwsuc_0 ordsssuc expcom pm5.32d fordpwsuc_0 word iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 csuc wcel wa iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv con0 wcel iordpwsuc_0 cv fordpwsuc_0 csuc wcel simpr fordpwsuc_0 word iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv con0 wcel fordpwsuc_0 word fordpwsuc_0 csuc word iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv con0 wcel wi fordpwsuc_0 ordsuc fordpwsuc_0 csuc word iordpwsuc_0 cv fordpwsuc_0 csuc wcel iordpwsuc_0 cv con0 wcel fordpwsuc_0 csuc iordpwsuc_0 cv ordelon ex sylbi ancrd impbid2 bitrd syl5bb eqrdv $.
$}
$( The collection of ordinal numbers in the power set of an ordinal number
       is its successor.  (Contributed by NM, 19-Oct-2004.) $)
${
	fonpwsuc_0 $f class A $.
	onpwsuc $p |- ( A e. On -> ( ~P A i^i On ) = suc A ) $= fonpwsuc_0 con0 wcel fonpwsuc_0 word fonpwsuc_0 cpw con0 cin fonpwsuc_0 csuc wceq fonpwsuc_0 eloni fonpwsuc_0 ordpwsuc syl $.
$}
$( The successor of an ordinal number is an ordinal number.  (Contributed by
     NM, 9-Sep-2003.) $)
${
	fsucelon_0 $f class A $.
	sucelon $p |- ( A e. On <-> suc A e. On ) $= fsucelon_0 word fsucelon_0 cvv wcel wa fsucelon_0 csuc word fsucelon_0 csuc cvv wcel wa fsucelon_0 con0 wcel fsucelon_0 csuc con0 wcel fsucelon_0 word fsucelon_0 csuc word fsucelon_0 cvv wcel fsucelon_0 csuc cvv wcel fsucelon_0 ordsuc fsucelon_0 sucexb anbi12i fsucelon_0 elon2 fsucelon_0 csuc elon2 3bitr4i $.
$}
$( The successor of an element of an ordinal class is a subset of it.
     (Contributed by NM, 21-Jun-1998.) $)
${
	fordsucss_0 $f class A $.
	fordsucss_1 $f class B $.
	ordsucss $p |- ( Ord B -> ( A e. B -> suc A C_ B ) ) $= fordsucss_1 word fordsucss_0 fordsucss_1 wcel fordsucss_0 csuc fordsucss_1 wss fordsucss_0 fordsucss_1 wcel fordsucss_1 word fordsucss_0 fordsucss_1 wcel fordsucss_0 csuc fordsucss_1 wss wi fordsucss_1 word fordsucss_0 fordsucss_1 wcel fordsucss_1 word fordsucss_0 fordsucss_1 wcel fordsucss_0 csuc fordsucss_1 wss wi fordsucss_1 word fordsucss_0 fordsucss_1 wcel wa fordsucss_0 word fordsucss_1 word fordsucss_0 fordsucss_1 wcel fordsucss_0 csuc fordsucss_1 wss wi fordsucss_1 fordsucss_0 ordelord fordsucss_0 word fordsucss_1 word wa fordsucss_0 fordsucss_1 wcel fordsucss_1 fordsucss_0 csuc wcel wn fordsucss_0 csuc fordsucss_1 wss fordsucss_0 word fordsucss_0 fordsucss_1 wcel fordsucss_1 fordsucss_0 csuc wcel wn wi fordsucss_1 word fordsucss_0 word fordsucss_0 fordsucss_1 wcel fordsucss_1 fordsucss_0 csuc wcel wa wn fordsucss_0 fordsucss_1 wcel fordsucss_1 fordsucss_0 csuc wcel wn wi fordsucss_0 fordsucss_1 ordnbtwn fordsucss_0 fordsucss_1 wcel fordsucss_1 fordsucss_0 csuc wcel imnan sylibr adantr fordsucss_0 word fordsucss_0 csuc word fordsucss_1 word fordsucss_0 csuc fordsucss_1 wss fordsucss_1 fordsucss_0 csuc wcel wn wb fordsucss_0 ordsuc fordsucss_0 csuc fordsucss_1 ordtri1 sylanb sylibrd sylan exp31 pm2.43b pm2.43b $.
$}
$( An ordinal number is a proper subset of its successor.  (Contributed by
     Stefan O'Rear, 18-Nov-2014.) $)
${
	fonpsssuc_0 $f class A $.
	onpsssuc $p |- ( A e. On -> A C. suc A ) $= fonpsssuc_0 con0 wcel fonpsssuc_0 fonpsssuc_0 csuc wcel fonpsssuc_0 fonpsssuc_0 csuc wpss fonpsssuc_0 con0 sucidg fonpsssuc_0 con0 wcel fonpsssuc_0 word fonpsssuc_0 csuc word fonpsssuc_0 fonpsssuc_0 csuc wcel fonpsssuc_0 fonpsssuc_0 csuc wpss wb fonpsssuc_0 eloni fonpsssuc_0 con0 wcel fonpsssuc_0 word fonpsssuc_0 csuc word fonpsssuc_0 eloni fonpsssuc_0 ordsuc sylib fonpsssuc_0 fonpsssuc_0 csuc ordelpss syl2anc mpbid $.
$}
$( A set belongs to an ordinal iff its successor is a subset of the ordinal.
     Exercise 8 of [TakeutiZaring] p. 42 and its converse.  (Contributed by NM,
     29-Nov-2003.) $)
${
	fordelsuc_0 $f class A $.
	fordelsuc_1 $f class B $.
	fordelsuc_2 $f class C $.
	ordelsuc $p |- ( ( A e. C /\ Ord B ) -> ( A e. B <-> suc A C_ B ) ) $= fordelsuc_0 fordelsuc_2 wcel fordelsuc_1 word wa fordelsuc_0 fordelsuc_1 wcel fordelsuc_0 csuc fordelsuc_1 wss fordelsuc_1 word fordelsuc_0 fordelsuc_1 wcel fordelsuc_0 csuc fordelsuc_1 wss wi fordelsuc_0 fordelsuc_2 wcel fordelsuc_0 fordelsuc_1 ordsucss adantl fordelsuc_0 fordelsuc_2 wcel fordelsuc_0 csuc fordelsuc_1 wss fordelsuc_0 fordelsuc_1 wcel wi fordelsuc_1 word fordelsuc_0 fordelsuc_1 fordelsuc_2 sucssel adantr impbid $.
$}
$( The successor of an ordinal number is the smallest larger ordinal
       number.  (Contributed by NM, 28-Nov-2003.) $)
${
	$d x A $.
	fonsucmin_0 $f set x $.
	fonsucmin_1 $f class A $.
	onsucmin $p |- ( A e. On -> suc A = |^| { x e. On | A e. x } ) $= fonsucmin_1 con0 wcel fonsucmin_1 fonsucmin_0 cv wcel fonsucmin_0 con0 crab cint fonsucmin_1 csuc fonsucmin_0 cv wss fonsucmin_0 con0 crab cint fonsucmin_1 csuc fonsucmin_1 con0 wcel fonsucmin_1 fonsucmin_0 cv wcel fonsucmin_0 con0 crab fonsucmin_1 csuc fonsucmin_0 cv wss fonsucmin_0 con0 crab fonsucmin_1 con0 wcel fonsucmin_1 fonsucmin_0 cv wcel fonsucmin_1 csuc fonsucmin_0 cv wss fonsucmin_0 con0 fonsucmin_0 cv con0 wcel fonsucmin_1 con0 wcel fonsucmin_0 cv word fonsucmin_1 fonsucmin_0 cv wcel fonsucmin_1 csuc fonsucmin_0 cv wss wb fonsucmin_0 cv eloni fonsucmin_1 fonsucmin_0 cv con0 ordelsuc sylan2 rabbidva inteqd fonsucmin_1 con0 wcel fonsucmin_1 csuc con0 wcel fonsucmin_1 csuc fonsucmin_0 cv wss fonsucmin_0 con0 crab cint fonsucmin_1 csuc wceq fonsucmin_1 sucelon fonsucmin_0 fonsucmin_1 csuc con0 intmin sylbi eqtr2d $.
$}
$( Membership is inherited by successors.  Generalization of Exercise 9 of
     [TakeutiZaring] p. 42.  (Contributed by NM, 22-Jun-1998.)  (Proof
     shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	fordsucelsuc_0 $f class A $.
	fordsucelsuc_1 $f class B $.
	ordsucelsuc $p |- ( Ord B -> ( A e. B <-> suc A e. suc B ) ) $= fordsucelsuc_1 word fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_1 word fordsucelsuc_0 fordsucelsuc_1 wcel wa fordsucelsuc_1 word fordsucelsuc_0 word fordsucelsuc_1 word fordsucelsuc_0 fordsucelsuc_1 wcel simpl fordsucelsuc_1 fordsucelsuc_0 ordelord jca fordsucelsuc_1 word fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel wa fordsucelsuc_1 word fordsucelsuc_0 word fordsucelsuc_1 word fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel simpl fordsucelsuc_1 word fordsucelsuc_1 csuc word fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_0 word fordsucelsuc_1 ordsuc fordsucelsuc_1 csuc word fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel wa fordsucelsuc_0 csuc word fordsucelsuc_0 word fordsucelsuc_1 csuc fordsucelsuc_0 csuc ordelord fordsucelsuc_0 ordsuc sylibr sylanb jca fordsucelsuc_0 cvv wcel fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel wb wi fordsucelsuc_0 cvv wcel fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel wb fordsucelsuc_0 cvv wcel fordsucelsuc_1 word fordsucelsuc_0 word wa wa fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo wb fordsucelsuc_0 cvv wcel fordsucelsuc_0 word fordsucelsuc_1 word fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo wb fordsucelsuc_0 word fordsucelsuc_0 csuc word fordsucelsuc_1 word fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo wb fordsucelsuc_0 ordsuc fordsucelsuc_0 csuc fordsucelsuc_1 ordsseleq sylanb ancoms adantl fordsucelsuc_0 cvv wcel fordsucelsuc_1 word fordsucelsuc_0 word wa wa fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_1 word fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wss wi fordsucelsuc_0 cvv wcel fordsucelsuc_0 word fordsucelsuc_0 fordsucelsuc_1 ordsucss ad2antrl fordsucelsuc_0 cvv wcel fordsucelsuc_0 csuc fordsucelsuc_1 wss fordsucelsuc_0 fordsucelsuc_1 wcel wi fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 fordsucelsuc_1 cvv sucssel adantr impbid fordsucelsuc_0 cvv wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo wb fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 cvv wcel fordsucelsuc_0 csuc cvv wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_0 csuc fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 wceq wo wb fordsucelsuc_0 sucexb fordsucelsuc_0 csuc fordsucelsuc_1 cvv elsucg sylbi adantr 3bitr4d ex fordsucelsuc_0 cvv wcel wn fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel wb fordsucelsuc_1 word fordsucelsuc_0 word wa fordsucelsuc_0 fordsucelsuc_1 wcel fordsucelsuc_0 cvv wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_0 fordsucelsuc_1 elex fordsucelsuc_0 csuc fordsucelsuc_1 csuc wcel fordsucelsuc_0 csuc cvv wcel fordsucelsuc_0 cvv wcel fordsucelsuc_0 csuc fordsucelsuc_1 csuc elex fordsucelsuc_0 sucexb sylibr pm5.21ni a1d pm2.61i pm5.21nd $.
$}
$( The subclass relationship between two ordinal classes is inherited by
     their successors.  (Contributed by NM, 4-Oct-2003.) $)
${
	fordsucsssuc_0 $f class A $.
	fordsucsssuc_1 $f class B $.
	ordsucsssuc $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> suc A C_ suc B ) ) $= fordsucsssuc_0 word fordsucsssuc_1 word wa fordsucsssuc_1 fordsucsssuc_0 wcel wn fordsucsssuc_1 csuc fordsucsssuc_0 csuc wcel wn fordsucsssuc_0 fordsucsssuc_1 wss fordsucsssuc_0 csuc fordsucsssuc_1 csuc wss fordsucsssuc_0 word fordsucsssuc_1 fordsucsssuc_0 wcel wn fordsucsssuc_1 csuc fordsucsssuc_0 csuc wcel wn wb fordsucsssuc_1 word fordsucsssuc_0 word fordsucsssuc_1 fordsucsssuc_0 wcel fordsucsssuc_1 csuc fordsucsssuc_0 csuc wcel fordsucsssuc_1 fordsucsssuc_0 ordsucelsuc notbid adantr fordsucsssuc_0 fordsucsssuc_1 ordtri1 fordsucsssuc_0 word fordsucsssuc_0 csuc word fordsucsssuc_1 csuc word fordsucsssuc_0 csuc fordsucsssuc_1 csuc wss fordsucsssuc_1 csuc fordsucsssuc_0 csuc wcel wn wb fordsucsssuc_1 word fordsucsssuc_0 ordsuc fordsucsssuc_1 ordsuc fordsucsssuc_0 csuc fordsucsssuc_1 csuc ordtri1 syl2anb 3bitr4d $.
$}
$( Given an element ` A ` of the union of an ordinal ` B ` , ` suc A ` is an
     element of ` B ` itself.  (Contributed by Scott Fenton, 28-Mar-2012.)
     (Proof shortened by Mario Carneiro, 29-May-2015.) $)
${
	fordsucuniel_0 $f class A $.
	fordsucuniel_1 $f class B $.
	ordsucuniel $p |- ( Ord B -> ( A e. U. B <-> suc A e. B ) ) $= fordsucuniel_1 word fordsucuniel_0 word fordsucuniel_0 fordsucuniel_1 cuni wcel fordsucuniel_0 csuc fordsucuniel_1 wcel fordsucuniel_1 word fordsucuniel_1 cuni word fordsucuniel_0 fordsucuniel_1 cuni wcel fordsucuniel_0 word wi fordsucuniel_1 orduni fordsucuniel_1 cuni word fordsucuniel_0 fordsucuniel_1 cuni wcel fordsucuniel_0 word fordsucuniel_1 cuni fordsucuniel_0 ordelord ex syl fordsucuniel_1 word fordsucuniel_0 csuc fordsucuniel_1 wcel fordsucuniel_0 word fordsucuniel_1 word fordsucuniel_0 csuc fordsucuniel_1 wcel wa fordsucuniel_0 csuc word fordsucuniel_0 word fordsucuniel_1 fordsucuniel_0 csuc ordelord fordsucuniel_0 ordsuc sylibr ex fordsucuniel_1 word fordsucuniel_0 word fordsucuniel_0 fordsucuniel_1 cuni wcel fordsucuniel_0 csuc fordsucuniel_1 wcel wb fordsucuniel_1 word fordsucuniel_0 word wa fordsucuniel_0 fordsucuniel_1 cuni wcel fordsucuniel_0 csuc fordsucuniel_1 wcel fordsucuniel_1 word fordsucuniel_0 word wa fordsucuniel_1 cuni fordsucuniel_0 wss fordsucuniel_1 fordsucuniel_0 csuc wss fordsucuniel_0 fordsucuniel_1 cuni wcel wn fordsucuniel_0 csuc fordsucuniel_1 wcel wn fordsucuniel_1 word fordsucuniel_1 con0 wss fordsucuniel_0 word fordsucuniel_1 cuni fordsucuniel_0 wss fordsucuniel_1 fordsucuniel_0 csuc wss wb fordsucuniel_1 ordsson fordsucuniel_1 fordsucuniel_0 ordunisssuc sylan fordsucuniel_1 word fordsucuniel_1 cuni word fordsucuniel_0 word fordsucuniel_1 cuni fordsucuniel_0 wss fordsucuniel_0 fordsucuniel_1 cuni wcel wn wb fordsucuniel_1 orduni fordsucuniel_1 cuni fordsucuniel_0 ordtri1 sylan fordsucuniel_0 word fordsucuniel_1 word fordsucuniel_0 csuc word fordsucuniel_1 fordsucuniel_0 csuc wss fordsucuniel_0 csuc fordsucuniel_1 wcel wn wb fordsucuniel_0 ordsuc fordsucuniel_1 fordsucuniel_0 csuc ordtri1 sylan2b 3bitr3d con4bid ex pm5.21ndd $.
$}
$( The successor of the maximum (i.e. union) of two ordinals is the maximum
       of their successors.  (Contributed by NM, 28-Nov-2003.) $)
${
	$d x A $.
	$d x B $.
	iordsucun_0 $f set x $.
	fordsucun_0 $f class A $.
	fordsucun_1 $f class B $.
	ordsucun $p |- ( ( Ord A /\ Ord B ) -> suc ( A u. B ) = ( suc A u. suc B ) ) $= fordsucun_0 word fordsucun_1 word wa iordsucun_0 fordsucun_0 fordsucun_1 cun csuc fordsucun_0 csuc fordsucun_1 csuc cun fordsucun_0 word fordsucun_1 word wa iordsucun_0 cv con0 wcel iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel fordsucun_0 word fordsucun_1 word wa fordsucun_0 fordsucun_1 cun word iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv con0 wcel wi fordsucun_0 fordsucun_1 ordun fordsucun_0 fordsucun_1 cun word fordsucun_0 fordsucun_1 cun csuc word iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv con0 wcel wi fordsucun_0 fordsucun_1 cun ordsuc fordsucun_0 fordsucun_1 cun csuc word iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv con0 wcel fordsucun_0 fordsucun_1 cun csuc iordsucun_0 cv ordelon ex sylbi syl fordsucun_0 word fordsucun_0 csuc word fordsucun_1 csuc word iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel iordsucun_0 cv con0 wcel wi fordsucun_1 word fordsucun_0 ordsuc fordsucun_1 ordsuc fordsucun_0 csuc word fordsucun_1 csuc word wa fordsucun_0 csuc fordsucun_1 csuc cun word iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel iordsucun_0 cv con0 wcel wi fordsucun_0 csuc fordsucun_1 csuc ordun fordsucun_0 csuc fordsucun_1 csuc cun word iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel iordsucun_0 cv con0 wcel fordsucun_0 csuc fordsucun_1 csuc cun iordsucun_0 cv ordelon ex syl syl2anb iordsucun_0 cv con0 wcel fordsucun_0 word fordsucun_1 word wa iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel wb iordsucun_0 cv con0 wcel fordsucun_0 word fordsucun_1 word wa wa iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv fordsucun_0 csuc wcel iordsucun_0 cv fordsucun_1 csuc wcel wo iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc cun wcel iordsucun_0 cv con0 wcel fordsucun_0 word fordsucun_1 word wa wa iordsucun_0 cv fordsucun_0 fordsucun_1 cun wss iordsucun_0 cv fordsucun_0 wss iordsucun_0 cv fordsucun_1 wss wo iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel iordsucun_0 cv fordsucun_0 csuc wcel iordsucun_0 cv fordsucun_1 csuc wcel wo fordsucun_0 word fordsucun_1 word wa iordsucun_0 cv fordsucun_0 fordsucun_1 cun wss iordsucun_0 cv fordsucun_0 wss iordsucun_0 cv fordsucun_1 wss wo wb iordsucun_0 cv con0 wcel iordsucun_0 cv fordsucun_0 fordsucun_1 ordssun adantl fordsucun_0 word fordsucun_1 word wa iordsucun_0 cv con0 wcel fordsucun_0 fordsucun_1 cun word iordsucun_0 cv fordsucun_0 fordsucun_1 cun wss iordsucun_0 cv fordsucun_0 fordsucun_1 cun csuc wcel wb fordsucun_0 fordsucun_1 ordun iordsucun_0 cv fordsucun_0 fordsucun_1 cun ordsssuc sylan2 iordsucun_0 cv con0 wcel fordsucun_0 word fordsucun_1 word wa wa iordsucun_0 cv fordsucun_0 wss iordsucun_0 cv fordsucun_0 csuc wcel iordsucun_0 cv fordsucun_1 wss iordsucun_0 cv fordsucun_1 csuc wcel iordsucun_0 cv con0 wcel fordsucun_0 word iordsucun_0 cv fordsucun_0 wss iordsucun_0 cv fordsucun_0 csuc wcel wb fordsucun_1 word iordsucun_0 cv fordsucun_0 ordsssuc adantrr iordsucun_0 cv con0 wcel fordsucun_1 word iordsucun_0 cv fordsucun_1 wss iordsucun_0 cv fordsucun_1 csuc wcel wb fordsucun_0 word iordsucun_0 cv fordsucun_1 ordsssuc adantrl orbi12d 3bitr3d iordsucun_0 cv fordsucun_0 csuc fordsucun_1 csuc elun syl6bbr expcom pm5.21ndd eqrdv $.
$}
$( The maximum of two ordinals is equal to one of them.  (Contributed by
     Mario Carneiro, 25-Jun-2015.) $)
${
	fordunpr_0 $f class B $.
	fordunpr_1 $f class C $.
	ordunpr $p |- ( ( B e. On /\ C e. On ) -> ( B u. C ) e. { B , C } ) $= fordunpr_0 con0 wcel fordunpr_1 con0 wcel wa fordunpr_0 fordunpr_1 cun fordunpr_0 fordunpr_1 cpr wcel fordunpr_0 fordunpr_1 cun fordunpr_0 wceq fordunpr_0 fordunpr_1 cun fordunpr_1 wceq wo fordunpr_0 con0 wcel fordunpr_1 con0 wcel wa fordunpr_1 fordunpr_0 wss fordunpr_0 fordunpr_1 wss wo fordunpr_0 fordunpr_1 cun fordunpr_0 wceq fordunpr_0 fordunpr_1 cun fordunpr_1 wceq wo fordunpr_0 con0 wcel fordunpr_1 con0 wcel wa fordunpr_0 fordunpr_1 wss fordunpr_1 fordunpr_0 wss fordunpr_0 con0 wcel fordunpr_0 word fordunpr_1 word fordunpr_0 fordunpr_1 wss fordunpr_1 fordunpr_0 wss wo fordunpr_1 con0 wcel fordunpr_0 eloni fordunpr_1 eloni fordunpr_0 fordunpr_1 ordtri2or2 syl2an orcomd fordunpr_1 fordunpr_0 wss fordunpr_0 fordunpr_1 cun fordunpr_0 wceq fordunpr_0 fordunpr_1 wss fordunpr_0 fordunpr_1 cun fordunpr_1 wceq fordunpr_1 fordunpr_0 ssequn2 fordunpr_0 fordunpr_1 ssequn1 orbi12i sylib fordunpr_0 con0 wcel fordunpr_1 con0 wcel wa fordunpr_0 fordunpr_1 cun cvv wcel fordunpr_0 fordunpr_1 cun fordunpr_0 fordunpr_1 cpr wcel fordunpr_0 fordunpr_1 cun fordunpr_0 wceq fordunpr_0 fordunpr_1 cun fordunpr_1 wceq wo wb fordunpr_0 fordunpr_1 con0 con0 unexg fordunpr_0 fordunpr_1 cun fordunpr_0 fordunpr_1 cvv elprg syl mpbird $.
$}
$( The maximum of two ordinals belongs to a third if each of them do.
     (Contributed by NM, 18-Sep-2006.)  (Revised by Mario Carneiro,
     25-Jun-2015.) $)
${
	fordunel_0 $f class A $.
	fordunel_1 $f class B $.
	fordunel_2 $f class C $.
	ordunel $p |- ( ( Ord A /\ B e. A /\ C e. A ) -> ( B u. C ) e. A ) $= fordunel_0 word fordunel_1 fordunel_0 wcel fordunel_2 fordunel_0 wcel w3a fordunel_1 fordunel_2 cpr fordunel_0 fordunel_1 fordunel_2 cun fordunel_1 fordunel_0 wcel fordunel_2 fordunel_0 wcel fordunel_1 fordunel_2 cpr fordunel_0 wss fordunel_0 word fordunel_1 fordunel_2 fordunel_0 prssi 3adant1 fordunel_0 word fordunel_1 fordunel_0 wcel fordunel_2 fordunel_0 wcel w3a fordunel_1 con0 wcel fordunel_2 con0 wcel fordunel_1 fordunel_2 cun fordunel_1 fordunel_2 cpr wcel fordunel_0 word fordunel_1 fordunel_0 wcel fordunel_1 con0 wcel fordunel_2 fordunel_0 wcel fordunel_0 fordunel_1 ordelon 3adant3 fordunel_0 word fordunel_2 fordunel_0 wcel fordunel_2 con0 wcel fordunel_1 fordunel_0 wcel fordunel_0 fordunel_2 ordelon 3adant2 fordunel_1 fordunel_2 ordunpr syl2anc sseldd $.
$}
$( A class of ordinal numbers is a subclass of the successor of its union.
     Similar to Proposition 7.26 of [TakeutiZaring] p. 41.  (Contributed by NM,
     19-Sep-2003.) $)
${
	fonsucuni_0 $f class A $.
	onsucuni $p |- ( A C_ On -> A C_ suc U. A ) $= fonsucuni_0 con0 wss fonsucuni_0 cuni word fonsucuni_0 fonsucuni_0 cuni csuc wss fonsucuni_0 ssorduni fonsucuni_0 con0 wss fonsucuni_0 cuni word wa fonsucuni_0 cuni fonsucuni_0 cuni wss fonsucuni_0 fonsucuni_0 cuni csuc wss fonsucuni_0 cuni ssid fonsucuni_0 fonsucuni_0 cuni ordunisssuc mpbii mpdan $.
$}
$( An ordinal class is a subclass of the successor of its union.
     (Contributed by NM, 12-Sep-2003.) $)
${
	fordsucuni_0 $f class A $.
	ordsucuni $p |- ( Ord A -> A C_ suc U. A ) $= fordsucuni_0 word fordsucuni_0 con0 wss fordsucuni_0 fordsucuni_0 cuni csuc wss fordsucuni_0 ordsson fordsucuni_0 onsucuni syl $.
$}
$( An ordinal class is either its union or the successor of its union.  If we
     adopt the view that zero is a limit ordinal, this means every ordinal
     class is either a limit or a successor.  (Contributed by NM,
     13-Sep-2003.) $)
${
	forduniorsuc_0 $f class A $.
	orduniorsuc $p |- ( Ord A -> ( A = U. A \/ A = suc U. A ) ) $= forduniorsuc_0 word forduniorsuc_0 forduniorsuc_0 cuni wceq forduniorsuc_0 forduniorsuc_0 cuni csuc wceq forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wne forduniorsuc_0 forduniorsuc_0 cuni csuc wss forduniorsuc_0 cuni csuc forduniorsuc_0 wss wa forduniorsuc_0 forduniorsuc_0 cuni wceq wn forduniorsuc_0 forduniorsuc_0 cuni csuc wceq forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wne forduniorsuc_0 cuni csuc forduniorsuc_0 wss forduniorsuc_0 forduniorsuc_0 cuni csuc wss forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wne forduniorsuc_0 cuni forduniorsuc_0 wcel forduniorsuc_0 cuni csuc forduniorsuc_0 wss forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wss forduniorsuc_0 cuni forduniorsuc_0 wne forduniorsuc_0 cuni forduniorsuc_0 wcel forduniorsuc_0 orduniss forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wcel forduniorsuc_0 cuni forduniorsuc_0 wss forduniorsuc_0 cuni forduniorsuc_0 wne wa forduniorsuc_0 cuni word forduniorsuc_0 word forduniorsuc_0 cuni forduniorsuc_0 wcel forduniorsuc_0 cuni forduniorsuc_0 wss forduniorsuc_0 cuni forduniorsuc_0 wne wa wb forduniorsuc_0 orduni forduniorsuc_0 cuni forduniorsuc_0 ordelssne mpancom biimprd mpand forduniorsuc_0 cuni forduniorsuc_0 ordsucss syld forduniorsuc_0 ordsucuni jctild forduniorsuc_0 forduniorsuc_0 cuni wceq wn forduniorsuc_0 forduniorsuc_0 cuni wne forduniorsuc_0 cuni forduniorsuc_0 wne forduniorsuc_0 forduniorsuc_0 cuni df-ne forduniorsuc_0 forduniorsuc_0 cuni necom bitr3i forduniorsuc_0 forduniorsuc_0 cuni csuc eqss 3imtr4g orrd $.
$}
$( The class of all ordinal numbers is its own union.  Exercise 11 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 12-Nov-2003.) $)
${
	$d x y $.
	iunon_0 $f set x $.
	iunon_1 $f set y $.
	unon $p |- U. On = On $= iunon_0 con0 cuni con0 iunon_0 cv con0 cuni wcel iunon_0 cv con0 wcel iunon_0 cv con0 cuni wcel iunon_0 cv iunon_1 cv wcel iunon_1 con0 wrex iunon_0 cv con0 wcel iunon_1 iunon_0 cv con0 eluni2 iunon_0 cv iunon_1 cv wcel iunon_0 cv con0 wcel iunon_1 con0 iunon_1 cv iunon_0 cv onelon rexlimiva sylbi iunon_0 cv con0 wcel iunon_0 cv iunon_0 cv csuc wcel iunon_0 cv csuc con0 wcel iunon_0 cv con0 cuni wcel iunon_0 cv iunon_0 vex sucid iunon_0 cv suceloni iunon_0 cv iunon_0 cv csuc con0 elunii sylancr impbii eqriv $.
$}
$( An ordinal class is equal to the union of its successor.  (Contributed
       by NM, 10-Dec-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$d x A $.
	iordunisuc_0 $f set x $.
	fordunisuc_0 $f class A $.
	ordunisuc $p |- ( Ord A -> U. suc A = A ) $= fordunisuc_0 word fordunisuc_0 con0 wcel fordunisuc_0 con0 wceq wo fordunisuc_0 csuc cuni fordunisuc_0 wceq fordunisuc_0 ordeleqon fordunisuc_0 con0 wcel fordunisuc_0 csuc cuni fordunisuc_0 wceq fordunisuc_0 con0 wceq iordunisuc_0 cv csuc cuni iordunisuc_0 cv wceq fordunisuc_0 csuc cuni fordunisuc_0 wceq iordunisuc_0 fordunisuc_0 con0 iordunisuc_0 cv fordunisuc_0 wceq iordunisuc_0 cv csuc cuni fordunisuc_0 csuc cuni iordunisuc_0 cv fordunisuc_0 iordunisuc_0 cv fordunisuc_0 wceq iordunisuc_0 cv csuc fordunisuc_0 csuc iordunisuc_0 cv fordunisuc_0 suceq unieqd iordunisuc_0 cv fordunisuc_0 wceq id eqeq12d iordunisuc_0 cv con0 wcel iordunisuc_0 cv wtr iordunisuc_0 cv csuc cuni iordunisuc_0 cv wceq iordunisuc_0 cv con0 wcel iordunisuc_0 cv word iordunisuc_0 cv wtr iordunisuc_0 cv eloni iordunisuc_0 cv ordtr syl iordunisuc_0 cv iordunisuc_0 vex unisuc sylib vtoclga fordunisuc_0 con0 wceq con0 csuc cuni con0 fordunisuc_0 csuc cuni fordunisuc_0 con0 csuc cuni con0 cuni con0 con0 csuc con0 sucon unieqi unon eqtri fordunisuc_0 con0 wceq fordunisuc_0 csuc con0 csuc fordunisuc_0 con0 suceq unieqd fordunisuc_0 con0 wceq id 3eqtr4a jaoi sylbi $.
$}
$( The union of the ordinal subsets of an ordinal number is that number.
       (Contributed by NM, 30-Jan-2005.) $)
${
	$d x A $.
	forduniss2_0 $f set x $.
	forduniss2_1 $f class A $.
	orduniss2 $p |- ( Ord A -> U. { x e. On | x C_ A } = A ) $= forduniss2_1 word forduniss2_0 cv forduniss2_1 wss forduniss2_0 con0 crab cuni forduniss2_1 csuc cuni forduniss2_1 forduniss2_1 word forduniss2_0 cv forduniss2_1 wss forduniss2_0 con0 crab forduniss2_1 csuc forduniss2_1 word forduniss2_0 cv forduniss2_1 wss forduniss2_0 con0 crab forduniss2_1 cpw con0 cin forduniss2_1 csuc forduniss2_0 cv forduniss2_1 wss forduniss2_0 con0 crab forduniss2_0 cv con0 wcel forduniss2_0 cv forduniss2_1 wss wa forduniss2_0 cab forduniss2_1 cpw con0 cin forduniss2_0 cv forduniss2_1 wss forduniss2_0 con0 df-rab forduniss2_0 cv con0 wcel forduniss2_0 cab forduniss2_0 cv forduniss2_1 wss forduniss2_0 cab cin forduniss2_0 cv forduniss2_1 wss forduniss2_0 cab forduniss2_0 cv con0 wcel forduniss2_0 cab cin forduniss2_0 cv con0 wcel forduniss2_0 cv forduniss2_1 wss wa forduniss2_0 cab forduniss2_1 cpw con0 cin forduniss2_0 cv con0 wcel forduniss2_0 cab forduniss2_0 cv forduniss2_1 wss forduniss2_0 cab incom forduniss2_0 cv con0 wcel forduniss2_0 cv forduniss2_1 wss forduniss2_0 inab forduniss2_0 cv forduniss2_1 wss forduniss2_0 cab forduniss2_1 cpw forduniss2_0 cv con0 wcel forduniss2_0 cab con0 forduniss2_1 cpw forduniss2_0 cv forduniss2_1 wss forduniss2_0 cab forduniss2_0 forduniss2_1 df-pw eqcomi forduniss2_0 con0 abid2 ineq12i 3eqtr3i eqtri forduniss2_1 ordpwsuc syl5eq unieqd forduniss2_1 ordunisuc eqtrd $.
$}
$( A successor ordinal is the successor of its union.  (Contributed by NM,
     10-Dec-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fonsucuni2_0 $f class A $.
	fonsucuni2_1 $f class B $.
	onsucuni2 $p |- ( ( A e. On /\ A = suc B ) -> suc U. A = A ) $= fonsucuni2_0 con0 wcel fonsucuni2_0 fonsucuni2_1 csuc wceq wa fonsucuni2_0 cuni csuc fonsucuni2_0 csuc cuni fonsucuni2_0 fonsucuni2_0 con0 wcel fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 cuni csuc fonsucuni2_0 csuc cuni wceq fonsucuni2_0 con0 wcel fonsucuni2_0 fonsucuni2_1 csuc wceq wa fonsucuni2_0 cuni csuc fonsucuni2_0 csuc cuni wceq fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_1 csuc cuni csuc fonsucuni2_1 csuc csuc cuni wceq fonsucuni2_0 con0 wcel fonsucuni2_0 fonsucuni2_1 csuc wceq wa fonsucuni2_1 csuc con0 wcel fonsucuni2_1 csuc word fonsucuni2_1 csuc cuni csuc fonsucuni2_1 csuc csuc cuni wceq fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 con0 wcel fonsucuni2_1 csuc con0 wcel fonsucuni2_0 fonsucuni2_1 csuc con0 eleq1 biimpac fonsucuni2_1 csuc eloni fonsucuni2_1 csuc word fonsucuni2_1 csuc cuni csuc fonsucuni2_1 csuc fonsucuni2_1 csuc csuc cuni fonsucuni2_1 csuc word fonsucuni2_1 csuc cuni fonsucuni2_1 wceq fonsucuni2_1 csuc cuni csuc fonsucuni2_1 csuc wceq fonsucuni2_1 csuc word fonsucuni2_1 word fonsucuni2_1 csuc cuni fonsucuni2_1 wceq fonsucuni2_1 ordsuc fonsucuni2_1 ordunisuc sylbir fonsucuni2_1 csuc cuni fonsucuni2_1 suceq syl fonsucuni2_1 csuc ordunisuc eqtr4d 3syl fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 cuni csuc fonsucuni2_1 csuc cuni csuc fonsucuni2_0 csuc cuni fonsucuni2_1 csuc csuc cuni fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 cuni fonsucuni2_1 csuc cuni wceq fonsucuni2_0 cuni csuc fonsucuni2_1 csuc cuni csuc wceq fonsucuni2_0 fonsucuni2_1 csuc unieq fonsucuni2_0 cuni fonsucuni2_1 csuc cuni suceq syl fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 csuc fonsucuni2_1 csuc csuc fonsucuni2_0 fonsucuni2_1 csuc suceq unieqd eqeq12d syl5ibr anabsi7 fonsucuni2_0 con0 wcel fonsucuni2_0 csuc cuni fonsucuni2_0 wceq fonsucuni2_0 fonsucuni2_1 csuc wceq fonsucuni2_0 con0 wcel fonsucuni2_0 word fonsucuni2_0 csuc cuni fonsucuni2_0 wceq fonsucuni2_0 eloni fonsucuni2_0 ordunisuc syl adantr eqtrd $.
$}
$( The successor of an ordinal class contains the empty set.  (Contributed by
     NM, 4-Apr-1995.) $)
${
	f0elsuc_0 $f class A $.
	0elsuc $p |- ( Ord A -> (/) e. suc A ) $= f0elsuc_0 word f0elsuc_0 csuc word c0 f0elsuc_0 csuc wcel f0elsuc_0 ordsuc f0elsuc_0 csuc word c0 f0elsuc_0 csuc wcel f0elsuc_0 csuc c0 wne f0elsuc_0 nsuceq0 f0elsuc_0 csuc ord0eln0 mpbiri sylbi $.
$}
$( The class of ordinal numbers is a limit ordinal.  (Contributed by NM,
     24-Mar-1995.) $)
${
	limon $p |- Lim On $= con0 wlim con0 word con0 c0 wne con0 con0 cuni wceq ordon onn0 con0 cuni con0 unon eqcomi con0 df-lim mpbir3an $.
$}
$( An ordinal number is a subset of ` On ` .  (Contributed by NM,
       11-Aug-1994.) $)
${
	fonssi_0 $f class A $.
	eonssi_0 $e |- A e. On $.
	onssi $p |- A C_ On $= fonssi_0 con0 wcel fonssi_0 con0 wss eonssi_0 fonssi_0 onss ax-mp $.
$}
$( The successor of an ordinal number is an ordinal number.  Corollary
       7N(c) of [Enderton] p. 193.  (Contributed by NM, 12-Jun-1994.) $)
${
	fonsuci_0 $f class A $.
	eonsuci_0 $e |- A e. On $.
	onsuci $p |- suc A e. On $= fonsuci_0 con0 wcel fonsuci_0 csuc con0 wcel eonsuci_0 fonsuci_0 suceloni ax-mp $.
$}
$( An ordinal number is either its own union (if zero or a limit ordinal)
       or the successor of its union.  (Contributed by NM, 13-Jun-1994.) $)
${
	fonuniorsuci_0 $f class A $.
	eonuniorsuci_0 $e |- A e. On $.
	onuniorsuci $p |- ( A = U. A \/ A = suc U. A ) $= fonuniorsuci_0 word fonuniorsuci_0 fonuniorsuci_0 cuni wceq fonuniorsuci_0 fonuniorsuci_0 cuni csuc wceq wo fonuniorsuci_0 eonuniorsuci_0 onordi fonuniorsuci_0 orduniorsuc ax-mp $.
$}
$( A limit ordinal is not a successor ordinal.  (Contributed by NM,
         18-Feb-2004.) $)
${
	$d x A $.
	fonuninsuci_0 $f set x $.
	fonuninsuci_1 $f class A $.
	eonuninsuci_0 $e |- A e. On $.
	onuninsuci $p |- ( A = U. A <-> -. E. x e. On A = suc x ) $= fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 con0 wrex fonuninsuci_1 fonuninsuci_1 cuni wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 con0 wrex fonuninsuci_1 fonuninsuci_1 cuni wceq wn fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni wceq wn fonuninsuci_0 con0 fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni wceq wa fonuninsuci_1 fonuninsuci_1 wcel fonuninsuci_1 eonuninsuci_0 onirri fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni wceq wa fonuninsuci_1 fonuninsuci_0 cv fonuninsuci_1 fonuninsuci_1 fonuninsuci_1 cuni wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni fonuninsuci_0 cv fonuninsuci_1 fonuninsuci_1 cuni wceq id fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 cuni fonuninsuci_0 cv cuni fonuninsuci_0 cv cun fonuninsuci_0 cv fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 cuni fonuninsuci_0 cv fonuninsuci_0 cv csn cun cuni fonuninsuci_0 cv cuni fonuninsuci_0 cv cun fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_0 cv fonuninsuci_0 cv csn cun wceq fonuninsuci_1 cuni fonuninsuci_0 cv fonuninsuci_0 cv csn cun cuni wceq fonuninsuci_0 cv csuc fonuninsuci_0 cv fonuninsuci_0 cv csn cun fonuninsuci_1 fonuninsuci_0 cv df-suc eqeq2i fonuninsuci_1 fonuninsuci_0 cv fonuninsuci_0 cv csn cun unieq sylbi fonuninsuci_0 cv fonuninsuci_0 cv csn cun cuni fonuninsuci_0 cv cuni fonuninsuci_0 cv csn cuni cun fonuninsuci_0 cv cuni fonuninsuci_0 cv cun fonuninsuci_0 cv fonuninsuci_0 cv csn uniun fonuninsuci_0 cv csn cuni fonuninsuci_0 cv fonuninsuci_0 cv cuni fonuninsuci_0 cv fonuninsuci_0 vex unisn uneq2i eqtri syl6eq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 cv cuni fonuninsuci_0 cv wss fonuninsuci_0 cv cuni fonuninsuci_0 cv cun fonuninsuci_0 cv wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 cv con0 wcel fonuninsuci_0 cv cuni fonuninsuci_0 cv wss fonuninsuci_1 fonuninsuci_0 cv csuc wceq con0 wtr fonuninsuci_0 cv csuc con0 wcel fonuninsuci_0 cv con0 wcel tron fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 con0 wcel fonuninsuci_0 cv csuc con0 wcel eonuninsuci_0 fonuninsuci_1 fonuninsuci_0 cv csuc con0 eleq1 mpbii con0 fonuninsuci_0 cv trsuc sylancr fonuninsuci_0 cv con0 wcel fonuninsuci_0 cv wtr fonuninsuci_0 cv cuni fonuninsuci_0 cv wss fonuninsuci_0 cv con0 wcel fonuninsuci_0 cv word fonuninsuci_0 cv wtr fonuninsuci_0 cv eloni fonuninsuci_0 cv ordtr syl fonuninsuci_0 cv df-tr sylib syl fonuninsuci_0 cv cuni fonuninsuci_0 cv ssequn1 sylib eqtrd sylan9eqr fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 cv fonuninsuci_1 wcel fonuninsuci_1 fonuninsuci_1 cuni wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 cv fonuninsuci_1 wcel fonuninsuci_0 cv fonuninsuci_0 cv csuc wcel fonuninsuci_0 cv fonuninsuci_0 vex sucid fonuninsuci_1 fonuninsuci_0 cv csuc fonuninsuci_0 cv eleq2 mpbiri adantr eqeltrd mto imnani rexlimivw fonuninsuci_1 fonuninsuci_1 cuni wceq wn fonuninsuci_1 cuni con0 wcel fonuninsuci_1 fonuninsuci_1 cuni csuc wceq fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_0 con0 wrex fonuninsuci_1 con0 wcel fonuninsuci_1 cuni con0 wcel eonuninsuci_0 fonuninsuci_1 onuni ax-mp fonuninsuci_1 fonuninsuci_1 cuni wceq fonuninsuci_1 fonuninsuci_1 cuni csuc wceq fonuninsuci_1 eonuninsuci_0 onuniorsuci ori fonuninsuci_1 fonuninsuci_0 cv csuc wceq fonuninsuci_1 fonuninsuci_1 cuni csuc wceq fonuninsuci_0 fonuninsuci_1 cuni con0 fonuninsuci_0 cv fonuninsuci_1 cuni wceq fonuninsuci_0 cv csuc fonuninsuci_1 cuni csuc fonuninsuci_1 fonuninsuci_0 cv fonuninsuci_1 cuni suceq eqeq2d rspcev sylancr impbii con2bii $.
$}
$( A set belongs to an ordinal number iff its successor is a subset of
         the ordinal number.  Exercise 8 of [TakeutiZaring] p. 42 and its
         converse.  (Contributed by NM, 16-Sep-1995.) $)
${
	fonsucssi_0 $f class A $.
	fonsucssi_1 $f class B $.
	eonsucssi_0 $e |- A e. On $.
	eonsucssi_1 $e |- B e. On $.
	onsucssi $p |- ( A e. B <-> suc A C_ B ) $= fonsucssi_0 con0 wcel fonsucssi_1 word fonsucssi_0 fonsucssi_1 wcel fonsucssi_0 csuc fonsucssi_1 wss wb eonsucssi_0 fonsucssi_1 eonsucssi_1 onordi fonsucssi_0 fonsucssi_1 con0 ordelsuc mp2an $.
$}
$( A successor is not a limit ordinal.  (Contributed by NM, 25-Mar-1995.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fnlimsucg_0 $f class A $.
	fnlimsucg_1 $f class V $.
	nlimsucg $p |- ( A e. V -> -. Lim suc A ) $= fnlimsucg_0 csuc wlim fnlimsucg_0 fnlimsucg_1 wcel fnlimsucg_0 csuc wlim fnlimsucg_0 word fnlimsucg_0 csuc fnlimsucg_0 csuc cuni wceq fnlimsucg_0 fnlimsucg_1 wcel wn fnlimsucg_0 csuc wlim fnlimsucg_0 csuc word fnlimsucg_0 word fnlimsucg_0 csuc limord fnlimsucg_0 ordsuc sylibr fnlimsucg_0 csuc limuni fnlimsucg_0 word fnlimsucg_0 csuc fnlimsucg_0 csuc cuni wceq fnlimsucg_0 csuc fnlimsucg_0 wceq fnlimsucg_0 fnlimsucg_1 wcel wn fnlimsucg_0 word fnlimsucg_0 csuc cuni fnlimsucg_0 fnlimsucg_0 csuc fnlimsucg_0 ordunisuc eqeq2d fnlimsucg_0 word fnlimsucg_0 csuc fnlimsucg_0 wceq fnlimsucg_0 fnlimsucg_0 csuc wcel wn fnlimsucg_0 fnlimsucg_1 wcel wn fnlimsucg_0 word fnlimsucg_0 fnlimsucg_0 csuc wcel wn fnlimsucg_0 csuc fnlimsucg_0 wceq fnlimsucg_0 fnlimsucg_0 wcel wn fnlimsucg_0 ordirr fnlimsucg_0 csuc fnlimsucg_0 wceq fnlimsucg_0 fnlimsucg_0 csuc wcel fnlimsucg_0 fnlimsucg_0 wcel fnlimsucg_0 csuc fnlimsucg_0 fnlimsucg_0 eleq2 notbid syl5ibrcom fnlimsucg_0 fnlimsucg_1 wcel fnlimsucg_0 fnlimsucg_0 csuc wcel fnlimsucg_0 fnlimsucg_1 sucidg con3i syl6 sylbid sylc con2i $.
$}
$( An ordinal equal to its union is not a successor.  (Contributed by NM,
       18-Feb-2004.) $)
${
	$d x A $.
	forduninsuc_0 $f set x $.
	forduninsuc_1 $f class A $.
	orduninsuc $p |- ( Ord A -> ( A = U. A <-> -. E. x e. On A = suc x ) ) $= forduninsuc_1 word forduninsuc_1 con0 wcel forduninsuc_1 con0 wceq wo forduninsuc_1 forduninsuc_1 cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb forduninsuc_1 ordeleqon forduninsuc_1 con0 wcel forduninsuc_1 forduninsuc_1 cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb forduninsuc_1 con0 wceq forduninsuc_1 con0 wcel forduninsuc_1 forduninsuc_1 cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_1 con0 wcel forduninsuc_1 c0 cif cuni wceq forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb forduninsuc_1 c0 forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif wceq forduninsuc_1 forduninsuc_1 cuni wceq forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_1 con0 wcel forduninsuc_1 c0 cif cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif wceq forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_1 cuni forduninsuc_1 con0 wcel forduninsuc_1 c0 cif cuni forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif wceq id forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif unieq eqeq12d forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_0 cv csuc wceq forduninsuc_0 con0 forduninsuc_1 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_0 cv csuc eqeq1 rexbidv notbid bibi12d forduninsuc_0 forduninsuc_1 con0 wcel forduninsuc_1 c0 cif forduninsuc_1 c0 con0 0elon elimel onuninsuci dedth forduninsuc_1 con0 wceq forduninsuc_1 forduninsuc_1 cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb con0 con0 cuni wceq con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn wb con0 con0 cuni wceq con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn con0 cuni con0 unon eqcomi con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 con0 forduninsuc_0 cv csuc wceq wn forduninsuc_0 cv con0 wcel con0 forduninsuc_0 cv csuc wceq con0 cvv wcel onprc con0 forduninsuc_0 cv csuc wceq con0 cvv wcel forduninsuc_0 cv csuc cvv wcel forduninsuc_0 cv forduninsuc_0 vex sucex con0 forduninsuc_0 cv csuc cvv eleq1 mpbiri mto a1i nrex 2th forduninsuc_1 con0 wceq forduninsuc_1 forduninsuc_1 cuni wceq con0 con0 cuni wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex wn forduninsuc_1 con0 wceq forduninsuc_1 con0 forduninsuc_1 cuni con0 cuni forduninsuc_1 con0 wceq id forduninsuc_1 con0 unieq eqeq12d forduninsuc_1 con0 wceq forduninsuc_1 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 wrex forduninsuc_1 con0 wceq forduninsuc_1 forduninsuc_0 cv csuc wceq con0 forduninsuc_0 cv csuc wceq forduninsuc_0 con0 forduninsuc_1 con0 forduninsuc_0 cv csuc eqeq1 rexbidv notbid bibi12d mpbiri jaoi sylbi $.
$}
$( An ordinal equal to its union contains the successor of each of its
       members.  (Contributed by NM, 1-Feb-2005.) $)
${
	$d x A $.
	fordunisuc2_0 $f set x $.
	fordunisuc2_1 $f class A $.
	ordunisuc2 $p |- ( Ord A -> ( A = U. A <-> A. x e. A suc x e. A ) ) $= fordunisuc2_1 word fordunisuc2_1 fordunisuc2_1 cuni wceq fordunisuc2_1 fordunisuc2_0 cv csuc wceq fordunisuc2_0 con0 wrex wn fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 fordunisuc2_1 wral fordunisuc2_0 fordunisuc2_1 orduninsuc fordunisuc2_1 fordunisuc2_0 cv csuc wceq fordunisuc2_0 con0 wrex wn fordunisuc2_1 fordunisuc2_0 cv csuc wceq wn fordunisuc2_0 con0 wral fordunisuc2_1 word fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 fordunisuc2_1 wral fordunisuc2_1 fordunisuc2_0 cv csuc wceq fordunisuc2_0 con0 ralnex fordunisuc2_1 word fordunisuc2_1 fordunisuc2_0 cv csuc wceq wn fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 con0 fordunisuc2_1 fordunisuc2_1 word fordunisuc2_0 cv con0 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wceq wn wi fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wi fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wceq wn fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo fordunisuc2_1 fordunisuc2_0 cv csuc wceq wn fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv csuc wceq fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo fordunisuc2_0 cv con0 wcel fordunisuc2_1 word fordunisuc2_0 cv csuc word fordunisuc2_1 fordunisuc2_0 cv csuc wceq fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo wn wb fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv csuc con0 wcel fordunisuc2_0 cv csuc word fordunisuc2_0 cv suceloni fordunisuc2_0 cv csuc eloni syl fordunisuc2_1 fordunisuc2_0 cv csuc ordtri3 sylan2 con2bid fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 cv con0 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv fordunisuc2_1 wcel wn fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel wa wn fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel wn wi fordunisuc2_0 cv fordunisuc2_1 onnbtwn fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv csuc wcel imnan sylibr con2d fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel pm2.21 syl6 adantl fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_0 cv fordunisuc2_1 wcel ax-1 a1i jaod fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wa fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_0 cv fordunisuc2_1 wcel wo fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wo fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_0 cv fordunisuc2_1 wcel wo fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_0 cv con0 wcel fordunisuc2_1 word fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv wss wo fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv word fordunisuc2_1 word fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_1 fordunisuc2_0 cv wss wo fordunisuc2_0 cv eloni fordunisuc2_0 cv fordunisuc2_1 ordtri2or sylan ancoms orcomd adantr fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wa fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_1 fordunisuc2_0 cv csuc wcel wi fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_1 fordunisuc2_0 cv wss fordunisuc2_1 fordunisuc2_0 cv csuc wcel fordunisuc2_1 fordunisuc2_0 cv ordsssuc2 biimpd adantr fordunisuc2_1 word fordunisuc2_0 cv con0 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi simpr orim12d mpd ex impbid bitr3d pm5.74da fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi wi fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel wa fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_1 word fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel wi fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel impexp fordunisuc2_1 word fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv csuc fordunisuc2_1 wcel fordunisuc2_1 word fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel wa fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv con0 wcel fordunisuc2_0 cv fordunisuc2_1 wcel simpr fordunisuc2_1 word fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv con0 wcel fordunisuc2_1 word fordunisuc2_0 cv fordunisuc2_1 wcel fordunisuc2_0 cv con0 wcel fordunisuc2_1 fordunisuc2_0 cv ordelon ex ancrd impbid2 imbi1d syl5bbr bitrd ralbidv2 syl5bbr bitrd $.
$}
$( An ordinal is zero, a successor ordinal, or a limit ordinal.
       (Contributed by NM, 1-Oct-2003.) $)
${
	$d x A $.
	fordzsl_0 $f set x $.
	fordzsl_1 $f class A $.
	ordzsl $p |- ( Ord A <-> ( A = (/) \/ E. x e. On A = suc x \/ Lim A ) ) $= fordzsl_1 word fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim w3o fordzsl_1 word fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 c0 wceq fordzsl_1 wlim wo wo fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim w3o fordzsl_1 word fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 c0 wceq fordzsl_1 wlim wo fordzsl_1 word fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex wn fordzsl_1 fordzsl_1 cuni wceq fordzsl_1 c0 wceq fordzsl_1 wlim wo fordzsl_1 word fordzsl_1 fordzsl_1 cuni wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex wn fordzsl_0 fordzsl_1 orduninsuc biimprd fordzsl_1 unizlim sylibd orrd fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim w3o fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim wo wo fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 c0 wceq fordzsl_1 wlim wo wo fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim 3orass fordzsl_1 c0 wceq fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim or12 bitri sylibr fordzsl_1 c0 wceq fordzsl_1 word fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 con0 wrex fordzsl_1 wlim fordzsl_1 c0 wceq fordzsl_1 word c0 word ord0 fordzsl_1 c0 ordeq mpbiri fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_1 word fordzsl_0 con0 fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 cv con0 wcel fordzsl_1 con0 wcel fordzsl_1 word fordzsl_0 cv con0 wcel fordzsl_1 con0 wcel fordzsl_1 fordzsl_0 cv csuc wceq fordzsl_0 cv csuc con0 wcel fordzsl_0 cv suceloni fordzsl_1 fordzsl_0 cv csuc con0 eleq1 syl5ibr fordzsl_1 eloni syl6com rexlimiv fordzsl_1 limord 3jaoi impbii $.
$}
$( An ordinal number is zero, a successor ordinal, or a limit ordinal
       number.  (Contributed by NM, 1-Oct-2003.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x A $.
	fonzsl_0 $f set x $.
	fonzsl_1 $f class A $.
	onzsl $p |- ( A e. On <-> ( A = (/) \/ E. x e. On A = suc x \/ ( A e. _V /\ Lim A ) ) ) $= fonzsl_1 con0 wcel fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_1 con0 wcel fonzsl_1 cvv wcel fonzsl_1 word fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_1 con0 elex fonzsl_1 eloni fonzsl_1 word fonzsl_1 cvv wcel fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 wlim w3o fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_0 fonzsl_1 ordzsl fonzsl_1 cvv wcel fonzsl_1 c0 wceq fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 wlim fonzsl_1 c0 wceq fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_1 cvv wcel fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa 3mix1 adantl fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa w3o fonzsl_1 cvv wcel fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 c0 wceq fonzsl_1 cvv wcel fonzsl_1 wlim wa 3mix2 adantl fonzsl_1 cvv wcel fonzsl_1 wlim wa fonzsl_1 c0 wceq fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex 3mix3 3jaodan sylan2b syl2anc fonzsl_1 c0 wceq fonzsl_1 con0 wcel fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 con0 wrex fonzsl_1 cvv wcel fonzsl_1 wlim wa fonzsl_1 c0 wceq fonzsl_1 con0 wcel c0 con0 wcel 0elon fonzsl_1 c0 con0 eleq1 mpbiri fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_1 con0 wcel fonzsl_0 con0 fonzsl_0 cv con0 wcel fonzsl_1 con0 wcel fonzsl_1 fonzsl_0 cv csuc wceq fonzsl_0 cv csuc con0 wcel fonzsl_0 cv suceloni fonzsl_1 fonzsl_0 cv csuc con0 eleq1 syl5ibrcom rexlimiv fonzsl_1 cvv limelon 3jaoi impbii $.
$}
$( An alternate definition of a limit ordinal, which is any ordinal that is
       neither zero nor a successor.  (Contributed by NM, 1-Nov-2004.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x A $.
	fdflim3_0 $f set x $.
	fdflim3_1 $f class A $.
	dflim3 $p |- ( Lim A <-> ( Ord A /\ -. ( A = (/) \/ E. x e. On A = suc x ) ) ) $= fdflim3_1 wlim fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 fdflim3_1 cuni wceq w3a fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 fdflim3_1 cuni wceq wa wa fdflim3_1 word fdflim3_1 c0 wceq fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex wo wn wa fdflim3_1 df-lim fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 fdflim3_1 cuni wceq 3anass fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 fdflim3_1 cuni wceq wa fdflim3_1 c0 wceq fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex wo wn fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 fdflim3_1 cuni wceq wa fdflim3_1 c0 wceq wn fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex wn wa fdflim3_1 c0 wceq fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex wo wn fdflim3_1 word fdflim3_1 c0 wne fdflim3_1 c0 wceq wn fdflim3_1 fdflim3_1 cuni wceq fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex wn fdflim3_1 c0 wne fdflim3_1 c0 wceq wn wb fdflim3_1 word fdflim3_1 c0 df-ne a1i fdflim3_0 fdflim3_1 orduninsuc anbi12d fdflim3_1 c0 wceq fdflim3_1 fdflim3_0 cv csuc wceq fdflim3_0 con0 wrex ioran syl6bbr pm5.32i 3bitri $.
$}
$( An alternate definition of a limit ordinal.  (Contributed by NM,
       1-Feb-2005.) $)
${
	$d x A $.
	fdflim4_0 $f set x $.
	fdflim4_1 $f class A $.
	dflim4 $p |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A. x e. A suc x e. A ) ) $= fdflim4_1 wlim fdflim4_1 word c0 fdflim4_1 wcel fdflim4_1 fdflim4_1 cuni wceq w3a fdflim4_1 word c0 fdflim4_1 wcel fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral w3a fdflim4_1 dflim2 fdflim4_1 word c0 fdflim4_1 wcel fdflim4_1 fdflim4_1 cuni wceq wa wa fdflim4_1 word c0 fdflim4_1 wcel fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral wa wa fdflim4_1 word c0 fdflim4_1 wcel fdflim4_1 fdflim4_1 cuni wceq w3a fdflim4_1 word c0 fdflim4_1 wcel fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral w3a fdflim4_1 word c0 fdflim4_1 wcel fdflim4_1 fdflim4_1 cuni wceq wa c0 fdflim4_1 wcel fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral wa fdflim4_1 word fdflim4_1 fdflim4_1 cuni wceq fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral c0 fdflim4_1 wcel fdflim4_0 fdflim4_1 ordunisuc2 anbi2d pm5.32i fdflim4_1 word c0 fdflim4_1 wcel fdflim4_1 fdflim4_1 cuni wceq 3anass fdflim4_1 word c0 fdflim4_1 wcel fdflim4_0 cv csuc fdflim4_1 wcel fdflim4_0 fdflim4_1 wral 3anass 3bitr4i bitri $.
$}
$( The successor of a member of a limit ordinal is also a member.
       (Contributed by NM, 3-Sep-2003.) $)
${
	$d x A $.
	$d x B $.
	ilimsuc_0 $f set x $.
	flimsuc_0 $f class A $.
	flimsuc_1 $f class B $.
	limsuc $p |- ( Lim A -> ( B e. A <-> suc B e. A ) ) $= flimsuc_0 wlim flimsuc_1 flimsuc_0 wcel flimsuc_1 csuc flimsuc_0 wcel flimsuc_0 wlim flimsuc_0 word c0 flimsuc_0 wcel ilimsuc_0 cv csuc flimsuc_0 wcel ilimsuc_0 flimsuc_0 wral w3a flimsuc_1 flimsuc_0 wcel flimsuc_1 csuc flimsuc_0 wcel wi ilimsuc_0 flimsuc_0 dflim4 ilimsuc_0 cv csuc flimsuc_0 wcel ilimsuc_0 flimsuc_0 wral flimsuc_0 word flimsuc_1 flimsuc_0 wcel flimsuc_1 csuc flimsuc_0 wcel wi c0 flimsuc_0 wcel ilimsuc_0 cv csuc flimsuc_0 wcel flimsuc_1 csuc flimsuc_0 wcel ilimsuc_0 flimsuc_1 flimsuc_0 ilimsuc_0 cv flimsuc_1 wceq ilimsuc_0 cv csuc flimsuc_1 csuc flimsuc_0 ilimsuc_0 cv flimsuc_1 suceq eleq1d rspccv 3ad2ant3 sylbi flimsuc_0 wlim flimsuc_0 word flimsuc_0 wtr flimsuc_1 csuc flimsuc_0 wcel flimsuc_1 flimsuc_0 wcel wi flimsuc_0 limord flimsuc_0 ordtr flimsuc_0 wtr flimsuc_1 csuc flimsuc_0 wcel flimsuc_1 flimsuc_0 wcel flimsuc_0 flimsuc_1 trsuc ex 3syl impbid $.
$}
$( A class includes a limit ordinal iff the successor of the class includes
       it.  (Contributed by NM, 30-Oct-2003.) $)
${
	$d x A $.
	$d x B $.
	ilimsssuc_0 $f set x $.
	flimsssuc_0 $f class A $.
	flimsssuc_1 $f class B $.
	limsssuc $p |- ( Lim A -> ( A C_ B <-> A C_ suc B ) ) $= flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 wss flimsssuc_0 flimsssuc_1 csuc wss flimsssuc_0 flimsssuc_1 wss flimsssuc_1 flimsssuc_1 csuc wss flimsssuc_0 flimsssuc_1 csuc wss flimsssuc_1 sssucid flimsssuc_0 flimsssuc_1 flimsssuc_1 csuc sstr2 mpi flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss flimsssuc_0 flimsssuc_1 wss flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss wa ilimsssuc_0 flimsssuc_0 flimsssuc_1 flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss wa ilimsssuc_0 cv flimsssuc_0 wcel ilimsssuc_0 cv flimsssuc_1 wcel flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss wa ilimsssuc_0 cv flimsssuc_0 wcel wa ilimsssuc_0 cv flimsssuc_1 wceq wn ilimsssuc_0 cv flimsssuc_1 wcel flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel ilimsssuc_0 cv flimsssuc_1 wceq wn flimsssuc_0 wlim ilimsssuc_0 cv flimsssuc_0 wcel flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_1 wceq wn flimsssuc_0 wlim ilimsssuc_0 cv flimsssuc_0 wcel flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_1 wceq wn wi flimsssuc_0 wlim ilimsssuc_0 cv flimsssuc_0 wcel wa ilimsssuc_0 cv flimsssuc_1 wceq flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel ilimsssuc_0 cv flimsssuc_1 wceq flimsssuc_1 flimsssuc_0 wcel flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss wn ilimsssuc_0 cv flimsssuc_1 wceq ilimsssuc_0 cv flimsssuc_0 wcel flimsssuc_1 flimsssuc_0 wcel ilimsssuc_0 cv flimsssuc_1 flimsssuc_0 eleq1 biimpcd flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel flimsssuc_0 flimsssuc_1 csuc wss wn flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel wa flimsssuc_1 csuc flimsssuc_0 wcel flimsssuc_0 flimsssuc_1 csuc wss wn flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel flimsssuc_1 csuc flimsssuc_0 wcel flimsssuc_0 flimsssuc_1 limsuc biimpa flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel wa flimsssuc_0 flimsssuc_1 csuc wss flimsssuc_1 csuc flimsssuc_0 wcel flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel wa flimsssuc_0 word flimsssuc_1 csuc word flimsssuc_0 flimsssuc_1 csuc wss flimsssuc_1 csuc flimsssuc_0 wcel wn wb flimsssuc_0 wlim flimsssuc_0 word flimsssuc_1 flimsssuc_0 wcel flimsssuc_0 limord adantr flimsssuc_0 wlim flimsssuc_1 flimsssuc_0 wcel wa flimsssuc_1 word flimsssuc_1 csuc word flimsssuc_0 wlim flimsssuc_0 word flimsssuc_1 flimsssuc_0 wcel flimsssuc_1 word flimsssuc_0 limord flimsssuc_0 flimsssuc_1 ordelord sylan flimsssuc_1 ordsuc sylib flimsssuc_0 flimsssuc_1 csuc ordtri1 syl2anc con2bid mpbid ex sylan9r con2d ex com23 imp31 flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel ilimsssuc_0 cv flimsssuc_1 wceq wn ilimsssuc_0 cv flimsssuc_1 wcel wi flimsssuc_0 wlim flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel wa ilimsssuc_0 cv flimsssuc_1 wcel ilimsssuc_0 cv flimsssuc_1 wceq flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel wa ilimsssuc_0 cv flimsssuc_1 wcel ilimsssuc_0 cv flimsssuc_1 wceq flimsssuc_0 flimsssuc_1 csuc wss ilimsssuc_0 cv flimsssuc_0 wcel wa ilimsssuc_0 cv flimsssuc_1 csuc wcel ilimsssuc_0 cv flimsssuc_1 wcel ilimsssuc_0 cv flimsssuc_1 wceq wo flimsssuc_0 flimsssuc_1 csuc ilimsssuc_0 cv ssel2 ilimsssuc_0 cv flimsssuc_1 ilimsssuc_0 vex elsuc sylib ord con1d adantll mpd ex ssrdv ex impbid2 $.
$}
$( Two ways to express the class of non-limit ordinal numbers.  Part of
       Definition 7.27 of [TakeutiZaring] p. 42, who use the symbol K_I for
       this class.  (Contributed by NM, 1-Nov-2004.) $)
${
	$d x y $.
	fnlimon_0 $f set x $.
	fnlimon_1 $f set y $.
	nlimon $p |- { x e. On | ( x = (/) \/ E. y e. On x = suc y ) } = { x e. On | -. Lim x } $= fnlimon_0 cv c0 wceq fnlimon_0 cv fnlimon_1 cv csuc wceq fnlimon_1 con0 wrex wo fnlimon_0 cv wlim wn fnlimon_0 con0 fnlimon_0 cv con0 wcel fnlimon_0 cv word fnlimon_0 cv c0 wceq fnlimon_0 cv fnlimon_1 cv csuc wceq fnlimon_1 con0 wrex wo fnlimon_0 cv wlim wn wb fnlimon_0 cv eloni fnlimon_0 cv word fnlimon_0 cv wlim fnlimon_0 cv c0 wceq fnlimon_0 cv fnlimon_1 cv csuc wceq fnlimon_1 con0 wrex wo fnlimon_0 cv wlim fnlimon_0 cv word fnlimon_0 cv c0 wceq fnlimon_0 cv fnlimon_1 cv csuc wceq fnlimon_1 con0 wrex wo wn fnlimon_1 fnlimon_0 cv dflim3 baib con2bid syl rabbiia $.
$}
$( The union of a nonempty class of limit ordinals is a limit ordinal.
       (Contributed by NM, 1-Feb-2005.) $)
${
	$d x y z A $.
	ilimuni3_0 $f set y $.
	ilimuni3_1 $f set z $.
	flimuni3_0 $f set x $.
	flimuni3_1 $f class A $.
	limuni3 $p |- ( ( A =/= (/) /\ A. x e. A Lim x ) -> Lim U. A ) $= flimuni3_1 c0 wne flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral wa flimuni3_1 cuni word c0 flimuni3_1 cuni wcel ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_0 flimuni3_1 cuni wral flimuni3_1 cuni wlim flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral flimuni3_1 cuni word flimuni3_1 c0 wne flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral flimuni3_1 con0 wss flimuni3_1 cuni word flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_1 flimuni3_1 con0 ilimuni3_1 cv flimuni3_1 wcel flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_1 cv wlim ilimuni3_1 cv con0 wcel flimuni3_0 cv wlim ilimuni3_1 cv wlim flimuni3_0 ilimuni3_1 cv flimuni3_1 flimuni3_0 cv ilimuni3_1 cv limeq rspcv ilimuni3_1 cv cvv wcel ilimuni3_1 cv wlim ilimuni3_1 cv con0 wcel ilimuni3_1 vex ilimuni3_1 cv cvv limelon mpan syl6com ssrdv flimuni3_1 ssorduni syl adantl flimuni3_1 c0 wne flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral c0 flimuni3_1 cuni wcel flimuni3_1 c0 wne ilimuni3_1 cv flimuni3_1 wcel ilimuni3_1 wex flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral c0 flimuni3_1 cuni wcel wi ilimuni3_1 flimuni3_1 n0 ilimuni3_1 cv flimuni3_1 wcel flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral c0 flimuni3_1 cuni wcel wi ilimuni3_1 ilimuni3_1 cv flimuni3_1 wcel flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_1 cv wlim c0 flimuni3_1 cuni wcel flimuni3_0 cv wlim ilimuni3_1 cv wlim flimuni3_0 ilimuni3_1 cv flimuni3_1 flimuni3_0 cv ilimuni3_1 cv limeq rspcv ilimuni3_1 cv wlim c0 ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel c0 flimuni3_1 cuni wcel ilimuni3_1 cv 0ellim c0 ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel c0 flimuni3_1 cuni wcel c0 ilimuni3_1 cv flimuni3_1 elunii expcom syl5 syld exlimiv sylbi imp flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_0 flimuni3_1 cuni wral flimuni3_1 c0 wne flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_0 flimuni3_1 cuni ilimuni3_0 cv flimuni3_1 cuni wcel ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_1 flimuni3_1 wrex flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_1 ilimuni3_0 cv flimuni3_1 eluni2 flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_1 flimuni3_1 flimuni3_0 cv wlim flimuni3_0 flimuni3_1 wral ilimuni3_1 cv flimuni3_1 wcel ilimuni3_1 cv wlim ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_0 cv csuc flimuni3_1 cuni wcel wi flimuni3_0 cv wlim ilimuni3_1 cv wlim flimuni3_0 ilimuni3_1 cv flimuni3_1 flimuni3_0 cv ilimuni3_1 cv limeq rspccv ilimuni3_1 cv wlim ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_1 cv wlim ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_1 cv wlim ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel wa ilimuni3_0 cv csuc ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel wa ilimuni3_0 cv csuc flimuni3_1 cuni wcel ilimuni3_1 cv wlim ilimuni3_0 cv ilimuni3_1 cv wcel ilimuni3_0 cv csuc ilimuni3_1 cv wcel ilimuni3_1 cv flimuni3_1 wcel ilimuni3_1 cv ilimuni3_0 cv limsuc anbi1d ilimuni3_0 cv csuc ilimuni3_1 cv flimuni3_1 elunii syl6bi exp3a com3r sylcom rexlimdv syl5bi ralrimiv adantl ilimuni3_0 flimuni3_1 cuni dflim4 syl3anbrc $.
$}

