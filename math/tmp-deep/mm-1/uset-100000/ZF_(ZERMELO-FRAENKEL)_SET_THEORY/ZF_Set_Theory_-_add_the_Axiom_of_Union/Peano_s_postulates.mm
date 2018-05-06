$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/The_natural_numbers_(i_e__finite_ordinals).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Peano's postulates

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Zero is a natural number.  One of Peano's 5 postulates for arithmetic.
     Proposition 7.30(1) of [TakeutiZaring] p. 42.  Note:  Unlike most
     textbooks, our proofs of ~ peano1 through ~ peano5 do not use the Axiom of
     Infinity.  Unlike Takeuti and Zaring, they also do not use the Axiom of
     Regularity.  (Contributed by NM, 15-May-1994.) $)
${
	peano1 $p |- (/) e. om $= com wlim c0 com wcel limom com 0ellim ax-mp $.
$}
$( The successor of any natural number is a natural number.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(2) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)
${
	fpeano2_0 $f class A $.
	peano2 $p |- ( A e. om -> suc A e. om ) $= fpeano2_0 com wcel fpeano2_0 csuc com wcel fpeano2_0 peano2b biimpi $.
$}
$( The successor of any natural number is not zero.  One of Peano's 5
     postulates for arithmetic.  Proposition 7.30(3) of [TakeutiZaring] p. 42.
     (Contributed by NM, 3-Sep-2003.) $)
${
	fpeano3_0 $f class A $.
	peano3 $p |- ( A e. om -> suc A =/= (/) ) $= fpeano3_0 csuc c0 wne fpeano3_0 com wcel fpeano3_0 nsuceq0 a1i $.
$}
$( Two natural numbers are equal iff their successors are equal, i.e. the
     successor function is one-to-one.  One of Peano's 5 postulates for
     arithmetic.  Proposition 7.30(4) of [TakeutiZaring] p. 43.  (Contributed
     by NM, 3-Sep-2003.) $)
${
	fpeano4_0 $f class A $.
	fpeano4_1 $f class B $.
	peano4 $p |- ( ( A e. om /\ B e. om ) -> ( suc A = suc B <-> A = B ) ) $= fpeano4_0 com wcel fpeano4_0 con0 wcel fpeano4_1 con0 wcel fpeano4_0 csuc fpeano4_1 csuc wceq fpeano4_0 fpeano4_1 wceq wb fpeano4_1 com wcel fpeano4_0 nnon fpeano4_1 nnon fpeano4_0 fpeano4_1 suc11 syl2an $.
$}
$( The induction postulate: any class containing zero and closed under the
       successor operation contains all natural numbers.  One of Peano's 5
       postulates for arithmetic.  Proposition 7.30(5) of [TakeutiZaring]
       p. 43, except our proof does not require the Axiom of Infinity.  The
       more traditional statement of mathematical induction as a theorem
       schema, with a basis and an induction hypothesis, is derived from this
       theorem as theorem ~ findes .  (Contributed by NM, 18-Feb-2004.) $)
${
	$d x y A $.
	ipeano5_0 $f set y $.
	fpeano5_0 $f set x $.
	fpeano5_1 $f class A $.
	peano5 $p |- ( ( (/) e. A /\ A. x e. om ( x e. A -> suc x e. A ) ) -> om C_ A ) $= c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa com fpeano5_1 cdif c0 wceq com fpeano5_1 wss c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 com fpeano5_1 cdif wrex wn com fpeano5_1 cdif c0 wceq c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 com fpeano5_1 cdif c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa ipeano5_0 sup_set_class com fpeano5_1 cdif wcel wa com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 sup_set_class fpeano5_1 wcel ipeano5_0 sup_set_class com fpeano5_1 cdif wcel ipeano5_0 sup_set_class fpeano5_1 wcel wn c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa ipeano5_0 sup_set_class com fpeano5_1 eldifn adantl c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa ipeano5_0 sup_set_class com fpeano5_1 cdif wcel wa com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex ipeano5_0 sup_set_class fpeano5_1 wcel c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral wa ipeano5_0 sup_set_class com fpeano5_1 cdif wcel wa ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq c0 fpeano5_1 wcel ipeano5_0 sup_set_class com fpeano5_1 cdif wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral c0 fpeano5_1 wcel ipeano5_0 sup_set_class com fpeano5_1 cdif wcel wa ipeano5_0 sup_set_class com wcel ipeano5_0 sup_set_class c0 wne ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex ipeano5_0 sup_set_class com fpeano5_1 cdif wcel ipeano5_0 sup_set_class com wcel c0 fpeano5_1 wcel ipeano5_0 sup_set_class com fpeano5_1 eldifi adantl c0 fpeano5_1 wcel c0 com fpeano5_1 cdif wcel wn ipeano5_0 sup_set_class com fpeano5_1 cdif wcel ipeano5_0 sup_set_class c0 wne c0 fpeano5_1 com elndif ipeano5_0 sup_set_class com fpeano5_1 cdif wcel c0 com fpeano5_1 cdif wcel ipeano5_0 sup_set_class c0 ipeano5_0 sup_set_class c0 wceq ipeano5_0 sup_set_class com fpeano5_1 cdif wcel c0 com fpeano5_1 cdif wcel ipeano5_0 sup_set_class c0 com fpeano5_1 cdif eleq1 biimpcd necon3bd mpan9 fpeano5_0 ipeano5_0 sup_set_class nnsuc syl2anc adantlr adantr c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex ipeano5_0 sup_set_class fpeano5_1 wcel wi fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex ipeano5_0 sup_set_class fpeano5_1 wcel wi wi wi wi c0 fpeano5_1 wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 com wrex ipeano5_0 sup_set_class fpeano5_1 wcel wi fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa wa ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 com fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa fpeano5_0 fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com nfra1 ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa fpeano5_0 nfv nfan ipeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 nfv fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com wral fpeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class fpeano5_1 wcel wi fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi fpeano5_0 com rsp ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel wi ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa ipeano5_0 sup_set_class fpeano5_1 wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 wcel ipeano5_0 sup_set_class fpeano5_1 wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class com fpeano5_1 cdif wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq fpeano5_0 sup_set_class fpeano5_1 wcel ipeano5_0 sup_set_class com fpeano5_1 cdif wcel ipeano5_0 sup_set_class com wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq fpeano5_0 sup_set_class fpeano5_1 wcel wi ipeano5_0 sup_set_class com fpeano5_1 eldifi ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class ipeano5_0 sup_set_class wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq fpeano5_0 sup_set_class fpeano5_1 wcel wi ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq fpeano5_0 sup_set_class ipeano5_0 sup_set_class wcel fpeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wcel fpeano5_0 sup_set_class fpeano5_0 vex sucid ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc fpeano5_0 sup_set_class eleq2 mpbiri ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class ipeano5_0 sup_set_class wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq fpeano5_0 sup_set_class fpeano5_1 wcel wi wi ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class csuc com wcel fpeano5_0 sup_set_class com wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc com eleq1 fpeano5_0 sup_set_class peano2b syl6bbr fpeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class ipeano5_0 sup_set_class wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class ipeano5_0 sup_set_class wcel com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq wa fpeano5_0 sup_set_class com wcel fpeano5_0 sup_set_class com fpeano5_1 cdif wcel wn fpeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class ipeano5_0 sup_set_class com fpeano5_1 cdif minel fpeano5_0 sup_set_class com fpeano5_1 neldif sylan2 exp32 syl6bi mpid syl5 imp3a fpeano5_0 sup_set_class csuc fpeano5_1 wcel ipeano5_0 sup_set_class fpeano5_0 sup_set_class csuc wceq ipeano5_0 sup_set_class fpeano5_1 wcel fpeano5_0 sup_set_class csuc fpeano5_1 ipeano5_0 sup_set_class eleq1a com12 imim12d com13 sylan9 rexlimd exp32 a1i imp41 mpd mtand nrexdv com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 com fpeano5_1 cdif wrex com fpeano5_1 cdif c0 com word com fpeano5_1 cdif com wss com fpeano5_1 cdif c0 wne com fpeano5_1 cdif ipeano5_0 sup_set_class cin c0 wceq ipeano5_0 com fpeano5_1 cdif wrex ordom com fpeano5_1 difss ipeano5_0 com com fpeano5_1 cdif tz7.5 mp3an12 necon1bi syl com fpeano5_1 ssdif0 sylibr $.
$}
$( A natural number is either 0 or a successor.  (Contributed by NM,
       27-May-1998.) $)
${
	$d x A $.
	fnn0suc_0 $f set x $.
	fnn0suc_1 $f class A $.
	nn0suc $p |- ( A e. om -> ( A = (/) \/ E. x e. om A = suc x ) ) $= fnn0suc_1 com wcel fnn0suc_1 c0 wceq fnn0suc_1 fnn0suc_0 sup_set_class csuc wceq fnn0suc_0 com wrex fnn0suc_1 com wcel fnn0suc_1 c0 wceq wn fnn0suc_1 fnn0suc_0 sup_set_class csuc wceq fnn0suc_0 com wrex fnn0suc_1 c0 wceq wn fnn0suc_1 com wcel fnn0suc_1 c0 wne fnn0suc_1 fnn0suc_0 sup_set_class csuc wceq fnn0suc_0 com wrex fnn0suc_1 c0 df-ne fnn0suc_0 fnn0suc_1 nnsuc sylan2br ex orrd $.
$}

