$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Peano_s_postulates.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Finite induction (for finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The Principle of Finite Induction (mathematical induction).  Corollary
       7.31 of [TakeutiZaring] p. 43.  The simpler hypothesis shown here was
       suggested in an email from "Colin" on 1-Oct-2001.  The hypothesis states
       that ` A ` is a set of natural numbers, zero belongs to ` A ` , and
       given any member of ` A ` the member's successor also belongs to
       ` A ` .  The conclusion is that every natural number is in ` A ` .
       (Contributed by NM, 22-Feb-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$d x A $.
	ffind_0 $f set x $.
	ffind_1 $f class A $.
	efind_0 $e |- ( A C_ om /\ (/) e. A /\ A. x e. A suc x e. A ) $.
	find $p |- A = om $= ffind_1 com ffind_1 com wss c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral efind_0 simp1i c0 ffind_1 wcel ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 com wral wa com ffind_1 wss c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral wa c0 ffind_1 wcel ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 com wral wa ffind_1 com wss c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral w3a c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral wa efind_0 ffind_1 com wss c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral 3simpc ax-mp ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 com wral c0 ffind_1 wcel ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 wral ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 wal ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 com wral ffind_0 cv csuc ffind_1 wcel ffind_0 ffind_1 df-ral ffind_0 cv ffind_1 wcel ffind_0 cv csuc ffind_1 wcel wi ffind_0 com alral sylbi anim2i ax-mp ffind_0 ffind_1 peano5 ax-mp eqssi $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis. $)
$( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  Theorem
       Schema 22 of [Suppes] p. 136.  (Contributed by NM, 14-Apr-1995.) $)
${
	$d x y $.
	$d x A $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	$d x ta $.
	$d y ph $.
	ffinds_0 $f wff ph $.
	ffinds_1 $f wff ps $.
	ffinds_2 $f wff ch $.
	ffinds_3 $f wff th $.
	ffinds_4 $f wff ta $.
	ffinds_5 $f set x $.
	ffinds_6 $f set y $.
	ffinds_7 $f class A $.
	efinds_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	efinds_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	efinds_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	efinds_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	efinds_4 $e |- ps $.
	efinds_5 $e |- ( y e. om -> ( ch -> th ) ) $.
	finds $p |- ( A e. om -> ta ) $= ffinds_7 com wcel ffinds_7 ffinds_0 ffinds_5 cab wcel ffinds_4 com ffinds_0 ffinds_5 cab ffinds_7 c0 ffinds_0 ffinds_5 cab wcel ffinds_6 cv ffinds_0 ffinds_5 cab wcel ffinds_6 cv csuc ffinds_0 ffinds_5 cab wcel wi ffinds_6 com wral com ffinds_0 ffinds_5 cab wss c0 ffinds_0 ffinds_5 cab wcel ffinds_1 efinds_4 ffinds_0 ffinds_1 ffinds_5 c0 0ex efinds_0 elab mpbir ffinds_6 cv ffinds_0 ffinds_5 cab wcel ffinds_6 cv csuc ffinds_0 ffinds_5 cab wcel wi ffinds_6 com ffinds_6 cv com wcel ffinds_2 ffinds_3 ffinds_6 cv ffinds_0 ffinds_5 cab wcel ffinds_6 cv csuc ffinds_0 ffinds_5 cab wcel efinds_5 ffinds_0 ffinds_2 ffinds_5 ffinds_6 cv ffinds_6 vex efinds_1 elab ffinds_0 ffinds_3 ffinds_5 ffinds_6 cv csuc ffinds_6 cv ffinds_6 vex sucex efinds_2 elab 3imtr4g rgen ffinds_6 ffinds_0 ffinds_5 cab peano5 mp2an sseli ffinds_0 ffinds_4 ffinds_5 ffinds_7 com efinds_3 elabg mpbid $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis. $)
$( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last two are the basis and the induction hypothesis.  The
       basis of this version is an arbitrary natural number ` B ` instead of
       zero.  (Contributed by NM, 16-Sep-1995.) $)
${
	$d x A $.
	$d x y B $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	$d x ta $.
	$d y ph $.
	ffindsg_0 $f wff ph $.
	ffindsg_1 $f wff ps $.
	ffindsg_2 $f wff ch $.
	ffindsg_3 $f wff th $.
	ffindsg_4 $f wff ta $.
	ffindsg_5 $f set x $.
	ffindsg_6 $f set y $.
	ffindsg_7 $f class A $.
	ffindsg_8 $f class B $.
	efindsg_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	efindsg_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	efindsg_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	efindsg_3 $e |- ( x = A -> ( ph <-> ta ) ) $.
	efindsg_4 $e |- ( B e. om -> ps ) $.
	efindsg_5 $e |- ( ( ( y e. om /\ B e. om ) /\ B C_ y ) -> ( ch -> th ) ) $.
	findsg $p |- ( ( ( A e. om /\ B e. om ) /\ B C_ A ) -> ta ) $= ffindsg_7 com wcel ffindsg_8 com wcel ffindsg_8 ffindsg_7 wss ffindsg_4 ffindsg_8 com wcel ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi wi ffindsg_8 com wcel ffindsg_8 c0 wss ffindsg_1 wi wi ffindsg_8 com wcel ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi wi ffindsg_8 com wcel ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi ffindsg_8 com wcel ffindsg_8 ffindsg_7 wss ffindsg_4 wi wi ffindsg_5 ffindsg_6 ffindsg_7 ffindsg_5 cv c0 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 c0 wss ffindsg_1 wi ffindsg_8 com wcel ffindsg_8 c0 wceq ffindsg_5 cv c0 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 c0 wss ffindsg_1 wi wb ffindsg_8 c0 wceq ffindsg_5 cv c0 wceq wa ffindsg_8 ffindsg_5 cv wss ffindsg_8 c0 wss ffindsg_0 ffindsg_1 ffindsg_5 cv c0 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_8 c0 wss wb ffindsg_8 c0 wceq ffindsg_5 cv c0 ffindsg_8 sseq2 adantl ffindsg_8 c0 wceq ffindsg_5 cv c0 wceq ffindsg_0 ffindsg_1 wb ffindsg_8 c0 wceq ffindsg_5 cv c0 wceq ffindsg_5 cv ffindsg_8 wceq ffindsg_0 ffindsg_1 wb ffindsg_8 c0 ffindsg_5 cv eqeq2 efindsg_0 syl6bir imp imbi12d ffindsg_5 cv c0 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 c0 wss ffindsg_0 wi ffindsg_8 c0 wceq wn ffindsg_8 c0 wss ffindsg_1 wi ffindsg_5 cv c0 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_8 c0 wss ffindsg_0 ffindsg_5 cv c0 ffindsg_8 sseq2 imbi1d ffindsg_8 c0 wceq wn ffindsg_8 c0 wss ffindsg_0 ffindsg_1 ffindsg_8 c0 wceq wn ffindsg_8 c0 wss ffindsg_0 ffindsg_1 wb ffindsg_8 c0 wss ffindsg_8 c0 wceq ffindsg_8 ss0 con3i pm2.21d pm5.74d sylan9bbr pm2.61ian imbi2d ffindsg_5 cv ffindsg_6 cv wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 com wcel ffindsg_5 cv ffindsg_6 cv wceq ffindsg_8 ffindsg_5 cv wss ffindsg_8 ffindsg_6 cv wss ffindsg_0 ffindsg_2 ffindsg_5 cv ffindsg_6 cv ffindsg_8 sseq2 efindsg_1 imbi12d imbi2d ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi ffindsg_8 com wcel ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_8 ffindsg_5 cv wss ffindsg_8 ffindsg_6 cv csuc wss ffindsg_0 ffindsg_3 ffindsg_5 cv ffindsg_6 cv csuc ffindsg_8 sseq2 efindsg_2 imbi12d imbi2d ffindsg_5 cv ffindsg_7 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_0 wi ffindsg_8 ffindsg_7 wss ffindsg_4 wi ffindsg_8 com wcel ffindsg_5 cv ffindsg_7 wceq ffindsg_8 ffindsg_5 cv wss ffindsg_8 ffindsg_7 wss ffindsg_0 ffindsg_4 ffindsg_5 cv ffindsg_7 ffindsg_8 sseq2 efindsg_3 imbi12d imbi2d ffindsg_8 com wcel ffindsg_1 ffindsg_8 c0 wss efindsg_4 a1d ffindsg_6 cv com wcel ffindsg_8 com wcel ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi ffindsg_6 cv com wcel ffindsg_8 com wcel ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi ffindsg_8 com wcel ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi wi ffindsg_6 cv com wcel ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 com wcel ffindsg_3 ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 com wcel ffindsg_3 wi wi ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wceq ffindsg_8 com wcel ffindsg_3 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 com wcel ffindsg_3 wi ffindsg_6 cv csuc ffindsg_8 ffindsg_6 cv csuc ffindsg_8 wceq ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_5 cv ffindsg_8 wceq wa ffindsg_5 wex ffindsg_8 com wcel ffindsg_3 wi ffindsg_5 ffindsg_6 cv csuc ffindsg_8 ffindsg_6 cv ffindsg_6 vex sucex eqvinc ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_5 cv ffindsg_8 wceq wa ffindsg_8 com wcel ffindsg_3 wi ffindsg_5 ffindsg_5 cv ffindsg_8 wceq ffindsg_8 com wcel ffindsg_0 ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_3 ffindsg_8 com wcel ffindsg_0 ffindsg_5 cv ffindsg_8 wceq ffindsg_1 efindsg_4 efindsg_0 syl5ibr ffindsg_5 cv ffindsg_6 cv csuc wceq ffindsg_0 ffindsg_3 efindsg_2 biimpd sylan9r exlimiv sylbi eqcoms imim2i a1d com4r adantl ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi wn ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wn wa ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq wi wn ffindsg_8 ffindsg_6 cv csuc wne ffindsg_8 ffindsg_6 cv csuc wceq wn ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc df-ne anbi2i ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wceq annim bitri ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa ffindsg_8 ffindsg_6 cv wss ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi wi ffindsg_8 com wcel ffindsg_8 con0 wcel ffindsg_6 cv con0 wcel ffindsg_8 ffindsg_6 cv wss ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa wb ffindsg_6 cv com wcel ffindsg_8 nnon ffindsg_6 cv nnon ffindsg_8 con0 wcel ffindsg_6 cv con0 wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_8 ffindsg_6 cv csuc wcel ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa ffindsg_8 ffindsg_6 cv onsssuc ffindsg_6 cv con0 wcel ffindsg_8 con0 wcel ffindsg_6 cv csuc con0 wcel ffindsg_8 ffindsg_6 cv csuc wcel ffindsg_8 ffindsg_6 cv csuc wss ffindsg_8 ffindsg_6 cv csuc wne wa wb ffindsg_6 cv suceloni ffindsg_8 ffindsg_6 cv csuc onelpss sylan2 bitrd syl2anr ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_2 wi ffindsg_8 ffindsg_6 cv wss ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_2 ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_2 ffindsg_3 ffindsg_8 ffindsg_6 cv csuc wss ffindsg_3 wi ffindsg_6 cv com wcel ffindsg_8 com wcel wa ffindsg_8 ffindsg_6 cv wss ffindsg_2 ffindsg_3 wi efindsg_5 ex ffindsg_3 ffindsg_8 ffindsg_6 cv csuc wss ax-1 syl8 a2d com23 sylbird syl5bir pm2.61d ex a2d finds imp31 $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis. $)
$( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       29-Nov-2002.) $)
${
	$d x y ta $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	$d y ph $.
	ffinds2_0 $f wff ph $.
	ffinds2_1 $f wff ps $.
	ffinds2_2 $f wff ch $.
	ffinds2_3 $f wff th $.
	ffinds2_4 $f wff ta $.
	ffinds2_5 $f set x $.
	ffinds2_6 $f set y $.
	efinds2_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	efinds2_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	efinds2_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	efinds2_3 $e |- ( ta -> ps ) $.
	efinds2_4 $e |- ( y e. om -> ( ta -> ( ch -> th ) ) ) $.
	finds2 $p |- ( x e. om -> ( ta -> ph ) ) $= ffinds2_5 cv com wcel ffinds2_5 cv ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_4 ffinds2_0 wi com ffinds2_4 ffinds2_0 wi ffinds2_5 cab ffinds2_5 cv c0 ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_6 cv ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_6 cv csuc ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel wi ffinds2_6 com wral com ffinds2_4 ffinds2_0 wi ffinds2_5 cab wss c0 ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_4 ffinds2_1 wi efinds2_3 ffinds2_4 ffinds2_0 wi ffinds2_4 ffinds2_1 wi ffinds2_5 c0 0ex ffinds2_5 cv c0 wceq ffinds2_0 ffinds2_1 ffinds2_4 efinds2_0 imbi2d elab mpbir ffinds2_6 cv ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_6 cv csuc ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel wi ffinds2_6 com ffinds2_6 cv com wcel ffinds2_4 ffinds2_2 wi ffinds2_4 ffinds2_3 wi ffinds2_6 cv ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_6 cv csuc ffinds2_4 ffinds2_0 wi ffinds2_5 cab wcel ffinds2_6 cv com wcel ffinds2_4 ffinds2_2 ffinds2_3 efinds2_4 a2d ffinds2_4 ffinds2_0 wi ffinds2_4 ffinds2_2 wi ffinds2_5 ffinds2_6 cv ffinds2_6 vex ffinds2_5 cv ffinds2_6 cv wceq ffinds2_0 ffinds2_2 ffinds2_4 efinds2_1 imbi2d elab ffinds2_4 ffinds2_0 wi ffinds2_4 ffinds2_3 wi ffinds2_5 ffinds2_6 cv csuc ffinds2_6 cv ffinds2_6 vex sucex ffinds2_5 cv ffinds2_6 cv csuc wceq ffinds2_0 ffinds2_3 ffinds2_4 efinds2_2 imbi2d elab 3imtr4g rgen ffinds2_6 ffinds2_4 ffinds2_0 wi ffinds2_5 cab peano5 mp2an sseli ffinds2_4 ffinds2_0 wi ffinds2_5 abid sylib $.
$}
$( Substitutions. $)
$( Basis. $)
$( Induction hypothesis. $)
$( Principle of Finite Induction (inference schema), using implicit
       substitutions.  The first three hypotheses establish the substitutions
       we need.  The last two are the basis and the induction hypothesis.
       Theorem Schema 22 of [Suppes] p. 136.  (Contributed by NM,
       22-Mar-2006.) $)
${
	$d x y $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	$d y ph $.
	ffinds1_0 $f wff ph $.
	ffinds1_1 $f wff ps $.
	ffinds1_2 $f wff ch $.
	ffinds1_3 $f wff th $.
	ffinds1_4 $f set x $.
	ffinds1_5 $f set y $.
	efinds1_0 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
	efinds1_1 $e |- ( x = y -> ( ph <-> ch ) ) $.
	efinds1_2 $e |- ( x = suc y -> ( ph <-> th ) ) $.
	efinds1_3 $e |- ps $.
	efinds1_4 $e |- ( y e. om -> ( ch -> th ) ) $.
	finds1 $p |- ( x e. om -> ph ) $= ffinds1_4 cv com wcel c0 c0 wceq ffinds1_0 c0 eqid ffinds1_0 ffinds1_1 ffinds1_2 ffinds1_3 c0 c0 wceq ffinds1_4 ffinds1_5 efinds1_0 efinds1_1 efinds1_2 ffinds1_1 c0 c0 wceq efinds1_3 a1i ffinds1_5 cv com wcel ffinds1_2 ffinds1_3 wi c0 c0 wceq efinds1_4 a1d finds2 mpi $.
$}
$( Finite induction with explicit substitution.  The first hypothesis is
       the basis and the second is the induction hypothesis.  Theorem Schema 22
       of [Suppes] p. 136.  See ~ tfindes for the transfinite version.
       (Contributed by Raph Levien, 9-Jul-2003.) $)
${
	$d x y z $.
	$d y z ph $.
	ifindes_0 $f set y $.
	ifindes_1 $f set z $.
	ffindes_0 $f wff ph $.
	ffindes_1 $f set x $.
	efindes_0 $e |- [. (/) / x ]. ph $.
	efindes_1 $e |- ( x e. om -> ( ph -> [. suc x / x ]. ph ) ) $.
	findes $p |- ( x e. om -> ph ) $= ffindes_0 ffindes_1 ifindes_1 wsb ffindes_0 ffindes_1 c0 wsbc ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc ffindes_0 ifindes_1 ifindes_0 ffindes_1 cv ffindes_0 ffindes_1 ifindes_1 c0 dfsbcq2 ffindes_0 ifindes_1 ifindes_0 ffindes_1 sbequ ffindes_0 ffindes_1 ifindes_1 ifindes_0 cv csuc dfsbcq2 ffindes_0 ifindes_1 ffindes_1 sbequ12r efindes_0 ffindes_1 cv com wcel ffindes_0 ffindes_0 ffindes_1 ffindes_1 cv csuc wsbc wi wi ifindes_0 cv com wcel ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc wi wi ffindes_1 ifindes_0 ifindes_0 cv com wcel ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc wi ffindes_1 ifindes_0 cv com wcel ffindes_1 nfv ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc ffindes_1 ffindes_0 ffindes_1 ifindes_0 nfs1v ffindes_0 ffindes_1 ifindes_0 cv csuc nfsbc1v nfim nfim ffindes_1 ifindes_0 weq ffindes_1 cv com wcel ifindes_0 cv com wcel ffindes_0 ffindes_0 ffindes_1 ffindes_1 cv csuc wsbc wi ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc wi ffindes_1 cv ifindes_0 cv com eleq1 ffindes_1 ifindes_0 weq ffindes_0 ffindes_0 ffindes_1 ifindes_0 wsb ffindes_0 ffindes_1 ffindes_1 cv csuc wsbc ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc ffindes_0 ffindes_1 ifindes_0 sbequ12 ffindes_1 ifindes_0 weq ffindes_1 cv csuc ifindes_0 cv csuc wceq ffindes_0 ffindes_1 ffindes_1 cv csuc wsbc ffindes_0 ffindes_1 ifindes_0 cv csuc wsbc wb ffindes_1 cv ifindes_0 cv suceq ffindes_0 ffindes_1 ffindes_1 cv csuc ifindes_0 cv csuc dfsbcq syl imbi12d imbi12d efindes_1 chvar finds $.
$}

