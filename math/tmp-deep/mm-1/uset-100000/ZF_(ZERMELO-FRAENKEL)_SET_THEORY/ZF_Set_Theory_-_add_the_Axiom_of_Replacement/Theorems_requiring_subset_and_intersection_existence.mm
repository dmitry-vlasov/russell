$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Null_Set_Axiom.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Theorems requiring subset and intersection existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( No set contains all sets.  Theorem 41 of [Suppes] p. 30.  (Contributed
       by NM, 23-Aug-1993.) $)
${
	$d x y z $.
	inalset_0 $f set z $.
	fnalset_0 $f set x $.
	fnalset_1 $f set y $.
	nalset $p |- -. E. x A. y y e. x $= fnalset_1 sup_set_class fnalset_0 sup_set_class wcel wn fnalset_1 wex fnalset_1 sup_set_class fnalset_0 sup_set_class wcel fnalset_1 wal fnalset_0 wex wn fnalset_0 fnalset_1 sup_set_class fnalset_0 sup_set_class wcel fnalset_0 fnalset_1 alexn inalset_0 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn wa wb inalset_0 wal fnalset_1 wex fnalset_1 sup_set_class fnalset_0 sup_set_class wcel wn fnalset_1 wex inalset_0 sup_set_class inalset_0 sup_set_class wcel wn inalset_0 fnalset_1 fnalset_0 ax-sep inalset_0 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn wa wb inalset_0 wal fnalset_1 sup_set_class fnalset_0 sup_set_class wcel wn fnalset_1 inalset_0 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn wa wb inalset_0 wal fnalset_1 sup_set_class fnalset_1 sup_set_class wcel fnalset_1 sup_set_class fnalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel wn wa wb fnalset_1 sup_set_class fnalset_0 sup_set_class wcel wn inalset_0 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn wa wb fnalset_1 sup_set_class fnalset_1 sup_set_class wcel fnalset_1 sup_set_class fnalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel wn wa wb inalset_0 fnalset_1 inalset_0 sup_set_class fnalset_1 sup_set_class wceq inalset_0 sup_set_class fnalset_1 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn wa fnalset_1 sup_set_class fnalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel wn wa inalset_0 fnalset_1 fnalset_1 elequ1 inalset_0 sup_set_class fnalset_1 sup_set_class wceq inalset_0 sup_set_class fnalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_0 sup_set_class wcel inalset_0 sup_set_class inalset_0 sup_set_class wcel wn fnalset_1 sup_set_class fnalset_1 sup_set_class wcel wn inalset_0 fnalset_1 fnalset_0 elequ1 inalset_0 sup_set_class fnalset_1 sup_set_class wceq inalset_0 sup_set_class inalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel inalset_0 sup_set_class fnalset_1 sup_set_class wceq inalset_0 sup_set_class inalset_0 sup_set_class wcel fnalset_1 sup_set_class inalset_0 sup_set_class wcel fnalset_1 sup_set_class fnalset_1 sup_set_class wcel inalset_0 fnalset_1 inalset_0 elequ1 inalset_0 fnalset_1 fnalset_1 elequ2 bitrd notbid anbi12d bibi12d spv fnalset_1 sup_set_class fnalset_1 sup_set_class wcel fnalset_1 sup_set_class fnalset_0 sup_set_class wcel pclem6 syl eximi ax-mp mpgbi $.
$}
$( The universal class is not a member of itself (and thus is not a set).
       Proposition 5.21 of [TakeutiZaring] p. 21; our proof, however, does not
       depend on the Axiom of Regularity.  (Contributed by NM, 23-Aug-1993.) $)
${
	$d x y $.
	ivprc_0 $f set x $.
	ivprc_1 $f set y $.
	vprc $p |- -. _V e. _V $= cvv cvv wcel ivprc_0 sup_set_class cvv wceq ivprc_0 wex ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 wal ivprc_0 wex ivprc_0 sup_set_class cvv wceq ivprc_0 wex ivprc_0 ivprc_1 nalset ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 wal ivprc_0 sup_set_class cvv wceq ivprc_0 ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 wal ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 sup_set_class cvv wcel wb ivprc_1 wal ivprc_0 sup_set_class cvv wceq ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 sup_set_class cvv wcel wb ivprc_1 ivprc_1 sup_set_class cvv wcel ivprc_1 sup_set_class ivprc_0 sup_set_class wcel ivprc_1 vex tbt albii ivprc_1 ivprc_0 sup_set_class cvv dfcleq bitr4i exbii mtbi ivprc_0 cvv isset mtbir $.
$}
$( The universal class doesn't belong to any class.  (Contributed by FL,
     31-Dec-2006.) $)
${
	fnvel_0 $f class A $.
	nvel $p |- -. _V e. A $= cvv fnvel_0 wcel cvv cvv wcel vprc cvv fnvel_0 elex mto $.
$}
$( The universal class does not exist.  (Contributed by NM, 4-Jul-2005.) $)
${
	fvnex_0 $f set x $.
	vnex $p |- -. E. x x = _V $= cvv cvv wcel fvnex_0 sup_set_class cvv wceq fvnex_0 wex vprc fvnex_0 cvv isset mtbi $.
$}
$( Separation Scheme (Aussonderung) using class notation.  Compare Exercise
       4 of [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) $)
${
	$d A x y $.
	$d B x y $.
	iinex1_0 $f set x $.
	iinex1_1 $f set y $.
	finex1_0 $f class A $.
	finex1_1 $f class B $.
	einex1_0 $e |- A e. _V $.
	inex1 $p |- ( A i^i B ) e. _V $= iinex1_0 finex1_0 finex1_1 cin iinex1_0 sup_set_class finex1_0 finex1_1 cin wceq iinex1_0 wex iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 wcel iinex1_1 sup_set_class finex1_1 wcel wa wb iinex1_1 wal iinex1_0 wex iinex1_1 sup_set_class finex1_1 wcel iinex1_1 iinex1_0 finex1_0 einex1_0 zfauscl iinex1_0 sup_set_class finex1_0 finex1_1 cin wceq iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 wcel iinex1_1 sup_set_class finex1_1 wcel wa wb iinex1_1 wal iinex1_0 iinex1_0 sup_set_class finex1_0 finex1_1 cin wceq iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 finex1_1 cin wcel wb iinex1_1 wal iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 wcel iinex1_1 sup_set_class finex1_1 wcel wa wb iinex1_1 wal iinex1_1 iinex1_0 sup_set_class finex1_0 finex1_1 cin dfcleq iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 finex1_1 cin wcel wb iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 wcel iinex1_1 sup_set_class finex1_1 wcel wa wb iinex1_1 iinex1_1 sup_set_class finex1_0 finex1_1 cin wcel iinex1_1 sup_set_class finex1_0 wcel iinex1_1 sup_set_class finex1_1 wcel wa iinex1_1 sup_set_class iinex1_0 sup_set_class wcel iinex1_1 sup_set_class finex1_0 finex1_1 elin bibi2i albii bitri exbii mpbir issetri $.
$}
$( Separation Scheme (Aussonderung) using class notation.  (Contributed by
       NM, 27-Apr-1994.) $)
${
	finex2_0 $f class A $.
	finex2_1 $f class B $.
	einex2_0 $e |- A e. _V $.
	inex2 $p |- ( B i^i A ) e. _V $= finex2_1 finex2_0 cin finex2_0 finex2_1 cin cvv finex2_1 finex2_0 incom finex2_0 finex2_1 einex2_0 inex1 eqeltri $.
$}
$( Closed-form, generalized Separation Scheme.  (Contributed by NM,
       7-Apr-1995.) $)
${
	$d x A $.
	$d x B $.
	iinex1g_0 $f set x $.
	finex1g_0 $f class A $.
	finex1g_1 $f class B $.
	finex1g_2 $f class V $.
	inex1g $p |- ( A e. V -> ( A i^i B ) e. _V ) $= iinex1g_0 sup_set_class finex1g_1 cin cvv wcel finex1g_0 finex1g_1 cin cvv wcel iinex1g_0 finex1g_0 finex1g_2 iinex1g_0 sup_set_class finex1g_0 wceq iinex1g_0 sup_set_class finex1g_1 cin finex1g_0 finex1g_1 cin cvv iinex1g_0 sup_set_class finex1g_0 finex1g_1 ineq1 eleq1d iinex1g_0 sup_set_class finex1g_1 iinex1g_0 vex inex1 vtoclg $.
$}
$( The subset of a set is also a set.  Exercise 3 of [TakeutiZaring]
       p. 22.  This is one way to express the Axiom of Separation ~ ax-sep
       (a.k.a.  Subset Axiom).  (Contributed by NM, 27-Apr-1994.) $)
${
	fssex_0 $f class A $.
	fssex_1 $f class B $.
	essex_0 $e |- B e. _V $.
	ssex $p |- ( A C_ B -> A e. _V ) $= fssex_0 fssex_1 wss fssex_0 fssex_1 cin fssex_0 wceq fssex_0 cvv wcel fssex_0 fssex_1 df-ss fssex_0 fssex_1 cin fssex_0 wceq fssex_0 fssex_1 cin cvv wcel fssex_0 cvv wcel fssex_1 fssex_0 essex_0 inex2 fssex_0 fssex_1 cin fssex_0 cvv eleq1 mpbii sylbi $.
$}
$( The subset of a set is also a set.  (Contributed by NM, 9-Sep-1993.) $)
${
	fssexi_0 $f class A $.
	fssexi_1 $f class B $.
	essexi_0 $e |- B e. _V $.
	essexi_1 $e |- A C_ B $.
	ssexi $p |- A e. _V $= fssexi_0 fssexi_1 wss fssexi_0 cvv wcel essexi_1 fssexi_0 fssexi_1 essexi_0 ssex ax-mp $.
$}
$( The subset of a set is also a set.  Exercise 3 of [TakeutiZaring] p. 22
       (generalized).  (Contributed by NM, 14-Aug-1994.) $)
${
	$d x A $.
	$d x B $.
	issexg_0 $f set x $.
	fssexg_0 $f class A $.
	fssexg_1 $f class B $.
	fssexg_2 $f class C $.
	ssexg $p |- ( ( A C_ B /\ B e. C ) -> A e. _V ) $= fssexg_1 fssexg_2 wcel fssexg_0 fssexg_1 wss fssexg_0 cvv wcel fssexg_0 issexg_0 sup_set_class wss fssexg_0 cvv wcel wi fssexg_0 fssexg_1 wss fssexg_0 cvv wcel wi issexg_0 fssexg_1 fssexg_2 issexg_0 sup_set_class fssexg_1 wceq fssexg_0 issexg_0 sup_set_class wss fssexg_0 fssexg_1 wss fssexg_0 cvv wcel issexg_0 sup_set_class fssexg_1 fssexg_0 sseq2 imbi1d fssexg_0 issexg_0 sup_set_class issexg_0 vex ssex vtoclg impcom $.
$}
$( A subclass of a set is a set.  Deduction form of ~ ssexg .  (Contributed
       by David Moews, 1-May-2017.) $)
${
	fssexd_0 $f wff ph $.
	fssexd_1 $f class A $.
	fssexd_2 $f class B $.
	fssexd_3 $f class C $.
	essexd_0 $e |- ( ph -> B e. C ) $.
	essexd_1 $e |- ( ph -> A C_ B ) $.
	ssexd $p |- ( ph -> A e. _V ) $= fssexd_0 fssexd_1 fssexd_2 wss fssexd_2 fssexd_3 wcel fssexd_1 cvv wcel essexd_1 essexd_0 fssexd_1 fssexd_2 fssexd_3 ssexg syl2anc $.
$}
$( Existence of a difference.  (Contributed by NM, 26-May-1998.) $)
${
	fdifexg_0 $f class A $.
	fdifexg_1 $f class B $.
	fdifexg_2 $f class V $.
	difexg $p |- ( A e. V -> ( A \ B ) e. _V ) $= fdifexg_0 fdifexg_1 cdif fdifexg_0 wss fdifexg_0 fdifexg_2 wcel fdifexg_0 fdifexg_1 cdif cvv wcel fdifexg_0 fdifexg_1 difss fdifexg_0 fdifexg_1 cdif fdifexg_0 fdifexg_2 ssexg mpan $.
$}
$( Separation Scheme (Aussonderung) in terms of a class abstraction.
       (Contributed by NM, 8-Jun-1994.) $)
${
	$d x A $.
	fzfausab_0 $f wff ph $.
	fzfausab_1 $f set x $.
	fzfausab_2 $f class A $.
	ezfausab_0 $e |- A e. _V $.
	zfausab $p |- { x | ( x e. A /\ ph ) } e. _V $= fzfausab_1 sup_set_class fzfausab_2 wcel fzfausab_0 wa fzfausab_1 cab fzfausab_2 ezfausab_0 fzfausab_0 fzfausab_1 fzfausab_2 ssab2 ssexi $.
$}
$( Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 23-Oct-1999.) $)
${
	$d x A $.
	frabexg_0 $f wff ph $.
	frabexg_1 $f set x $.
	frabexg_2 $f class A $.
	frabexg_3 $f class V $.
	rabexg $p |- ( A e. V -> { x e. A | ph } e. _V ) $= frabexg_0 frabexg_1 frabexg_2 crab frabexg_2 wss frabexg_2 frabexg_3 wcel frabexg_0 frabexg_1 frabexg_2 crab cvv wcel frabexg_0 frabexg_1 frabexg_2 ssrab2 frabexg_0 frabexg_1 frabexg_2 crab frabexg_2 frabexg_3 ssexg mpan $.
$}
$( Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 19-Jul-1996.) $)
${
	$d x A $.
	frabex_0 $f wff ph $.
	frabex_1 $f set x $.
	frabex_2 $f class A $.
	erabex_0 $e |- A e. _V $.
	rabex $p |- { x e. A | ph } e. _V $= frabex_2 cvv wcel frabex_0 frabex_1 frabex_2 crab cvv wcel erabex_0 frabex_0 frabex_1 frabex_2 cvv rabexg ax-mp $.
$}
$( Membership in a class abstraction involving a subset.  Unlike ~ elabg ,
       ` A ` does not have to be a set.  (Contributed by NM, 29-Aug-2006.) $)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	felssabg_0 $f wff ph $.
	felssabg_1 $f wff ps $.
	felssabg_2 $f set x $.
	felssabg_3 $f class A $.
	felssabg_4 $f class B $.
	felssabg_5 $f class V $.
	eelssabg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	elssabg $p |- ( B e. V -> ( A e. { x | ( x C_ B /\ ph ) } <-> ( A C_ B /\ ps ) ) ) $= felssabg_4 felssabg_5 wcel felssabg_3 felssabg_4 wss felssabg_1 wa felssabg_3 cvv wcel wi felssabg_3 felssabg_2 sup_set_class felssabg_4 wss felssabg_0 wa felssabg_2 cab wcel felssabg_3 felssabg_4 wss felssabg_1 wa wb felssabg_4 felssabg_5 wcel felssabg_3 felssabg_4 wss felssabg_3 cvv wcel felssabg_1 felssabg_3 felssabg_4 wss felssabg_4 felssabg_5 wcel felssabg_3 cvv wcel felssabg_3 felssabg_4 felssabg_5 ssexg expcom adantrd felssabg_2 sup_set_class felssabg_4 wss felssabg_0 wa felssabg_3 felssabg_4 wss felssabg_1 wa felssabg_2 felssabg_3 cvv felssabg_2 sup_set_class felssabg_3 wceq felssabg_2 sup_set_class felssabg_4 wss felssabg_3 felssabg_4 wss felssabg_0 felssabg_1 felssabg_2 sup_set_class felssabg_3 felssabg_4 sseq1 eelssabg_0 anbi12d elab3g syl $.
$}
$( The intersection of a non-empty class exists.  Exercise 5 of
       [TakeutiZaring] p. 44 and its converse.  (Contributed by NM,
       13-Aug-2002.) $)
${
	$d x A $.
	iintex_0 $f set x $.
	fintex_0 $f class A $.
	intex $p |- ( A =/= (/) <-> |^| A e. _V ) $= fintex_0 c0 wne fintex_0 cint cvv wcel fintex_0 c0 wne iintex_0 sup_set_class fintex_0 wcel iintex_0 wex fintex_0 cint cvv wcel iintex_0 fintex_0 n0 iintex_0 sup_set_class fintex_0 wcel fintex_0 cint cvv wcel iintex_0 iintex_0 sup_set_class fintex_0 wcel fintex_0 cint iintex_0 sup_set_class wss fintex_0 cint cvv wcel iintex_0 sup_set_class fintex_0 intss1 fintex_0 cint iintex_0 sup_set_class iintex_0 vex ssex syl exlimiv sylbi fintex_0 cint cvv wcel fintex_0 c0 fintex_0 c0 wceq fintex_0 cint cvv wcel cvv cvv wcel vprc fintex_0 c0 wceq fintex_0 cint cvv cvv fintex_0 c0 wceq fintex_0 cint c0 cint cvv fintex_0 c0 inteq int0 syl6eq eleq1d mtbiri necon2ai impbii $.
$}
$( If a class intersection is not a set, it must be the universe.
     (Contributed by NM, 3-Jul-2005.) $)
${
	fintnex_0 $f class A $.
	intnex $p |- ( -. |^| A e. _V <-> |^| A = _V ) $= fintnex_0 cint cvv wcel wn fintnex_0 cint cvv wceq fintnex_0 cint cvv wcel wn fintnex_0 c0 wceq fintnex_0 cint cvv wceq fintnex_0 cint cvv wcel fintnex_0 c0 fintnex_0 intex necon1bbii fintnex_0 c0 wceq fintnex_0 cint c0 cint cvv fintnex_0 c0 inteq int0 syl6eq sylbi fintnex_0 cint cvv wceq fintnex_0 cint cvv wcel cvv cvv wcel vprc fintnex_0 cint cvv cvv eleq1 mtbiri impbii $.
$}
$( The intersection of a non-empty class abstraction exists.  (Contributed
       by NM, 21-Oct-2003.) $)
${
	fintexab_0 $f wff ph $.
	fintexab_1 $f set x $.
	intexab $p |- ( E. x ph <-> |^| { x | ph } e. _V ) $= fintexab_0 fintexab_1 wex fintexab_0 fintexab_1 cab c0 wne fintexab_0 fintexab_1 cab cint cvv wcel fintexab_0 fintexab_1 abn0 fintexab_0 fintexab_1 cab intex bitr3i $.
$}
$( The intersection of a non-empty restricted class abstraction exists.
     (Contributed by NM, 21-Oct-2003.) $)
${
	fintexrab_0 $f wff ph $.
	fintexrab_1 $f set x $.
	fintexrab_2 $f class A $.
	intexrab $p |- ( E. x e. A ph <-> |^| { x e. A | ph } e. _V ) $= fintexrab_1 sup_set_class fintexrab_2 wcel fintexrab_0 wa fintexrab_1 wex fintexrab_1 sup_set_class fintexrab_2 wcel fintexrab_0 wa fintexrab_1 cab cint cvv wcel fintexrab_0 fintexrab_1 fintexrab_2 wrex fintexrab_0 fintexrab_1 fintexrab_2 crab cint cvv wcel fintexrab_1 sup_set_class fintexrab_2 wcel fintexrab_0 wa fintexrab_1 intexab fintexrab_0 fintexrab_1 fintexrab_2 df-rex fintexrab_0 fintexrab_1 fintexrab_2 crab cint fintexrab_1 sup_set_class fintexrab_2 wcel fintexrab_0 wa fintexrab_1 cab cint cvv fintexrab_0 fintexrab_1 fintexrab_2 crab fintexrab_1 sup_set_class fintexrab_2 wcel fintexrab_0 wa fintexrab_1 cab fintexrab_0 fintexrab_1 fintexrab_2 df-rab inteqi eleq1i 3bitr4i $.
$}
$( The existence of an indexed union. ` x ` is normally a free-variable
       parameter in ` B ` , which should be read ` B ( x ) ` .  (Contributed by
       FL, 19-Sep-2011.) $)
${
	$d A x y $.
	$d B y $.
	iiinexg_0 $f set y $.
	fiinexg_0 $f set x $.
	fiinexg_1 $f class A $.
	fiinexg_2 $f class B $.
	fiinexg_3 $f class C $.
	iinexg $p |- ( ( A =/= (/) /\ A. x e. A B e. C ) -> |^|_ x e. A B e. _V ) $= fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral wa fiinexg_0 fiinexg_1 fiinexg_2 ciin iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab cint cvv fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral fiinexg_0 fiinexg_1 fiinexg_2 ciin iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab cint wceq fiinexg_1 c0 wne fiinexg_0 iiinexg_0 fiinexg_1 fiinexg_2 fiinexg_3 dfiin2g adantl fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral wa iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab c0 wne iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab cint cvv wcel fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral wa iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 wex iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab c0 wne fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral wa iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex fiinexg_0 fiinexg_1 wrex iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 wex fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex fiinexg_0 fiinexg_1 wrex fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex wi fiinexg_0 fiinexg_1 wrex fiinexg_2 fiinexg_3 wcel fiinexg_0 fiinexg_1 wral iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex fiinexg_0 fiinexg_1 wrex wi fiinexg_1 c0 wne fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex wi fiinexg_0 fiinexg_1 wral fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex wi fiinexg_0 fiinexg_1 wrex fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex wi fiinexg_0 fiinexg_1 iiinexg_0 fiinexg_2 fiinexg_3 elisset rgenw fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex wi fiinexg_0 fiinexg_1 r19.2z mpan2 fiinexg_2 fiinexg_3 wcel iiinexg_0 sup_set_class fiinexg_2 wceq iiinexg_0 wex fiinexg_0 fiinexg_1 r19.35 sylib imp iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 iiinexg_0 fiinexg_1 rexcom4 sylib iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 abn0 sylibr iiinexg_0 sup_set_class fiinexg_2 wceq fiinexg_0 fiinexg_1 wrex iiinexg_0 cab intex sylib eqeltrd $.
$}
$( Absorption of a redundant conjunct in the intersection of a class
       abstraction.  (Contributed by NM, 3-Jul-2005.) $)
${
	$d x y $.
	$d x A $.
	$d y ph $.
	$d x ps $.
	$d x ch $.
	fintabs_0 $f wff ph $.
	fintabs_1 $f wff ps $.
	fintabs_2 $f wff ch $.
	fintabs_3 $f set x $.
	fintabs_4 $f set y $.
	fintabs_5 $f class A $.
	eintabs_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	eintabs_1 $e |- ( x = |^| { y | ps } -> ( ph <-> ch ) ) $.
	eintabs_2 $e |- ( |^| { y | ps } C_ A /\ ch ) $.
	intabs $p |- |^| { x | ( x C_ A /\ ph ) } = |^| { x | ph } $= fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint fintabs_0 fintabs_3 cab cint fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint fintabs_1 fintabs_4 cab cint fintabs_0 fintabs_3 cab cint fintabs_1 fintabs_4 cab cint cvv wcel fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint fintabs_1 fintabs_4 cab cint wss fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_1 fintabs_4 cab cint fintabs_5 wss fintabs_2 wa fintabs_3 fintabs_1 fintabs_4 cab cint cvv fintabs_3 sup_set_class fintabs_1 fintabs_4 cab cint wceq fintabs_3 sup_set_class fintabs_5 wss fintabs_1 fintabs_4 cab cint fintabs_5 wss fintabs_0 fintabs_2 fintabs_3 sup_set_class fintabs_1 fintabs_4 cab cint fintabs_5 sseq1 eintabs_1 anbi12d eintabs_2 intmin3 fintabs_1 fintabs_4 cab cint cvv wcel wn fintabs_1 fintabs_4 cab cint cvv wceq fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint fintabs_1 fintabs_4 cab cint wss fintabs_1 fintabs_4 cab intnex fintabs_1 fintabs_4 cab cint cvv wceq fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint fintabs_1 fintabs_4 cab cint wss fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint cvv wss fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint ssv fintabs_1 fintabs_4 cab cint cvv fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint sseq2 mpbiri sylbi pm2.61i fintabs_0 fintabs_3 cab fintabs_1 fintabs_4 cab fintabs_0 fintabs_1 fintabs_3 fintabs_4 eintabs_0 cbvabv inteqi sseqtr4i fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab fintabs_0 fintabs_3 cab wss fintabs_0 fintabs_3 cab cint fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab cint wss fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_0 fintabs_3 fintabs_3 sup_set_class fintabs_5 wss fintabs_0 simpr ss2abi fintabs_3 sup_set_class fintabs_5 wss fintabs_0 wa fintabs_3 cab fintabs_0 fintabs_3 cab intss ax-mp eqssi $.
$}
$( The intersection of a union ` U. A ` with a class ` B ` is equal to the
       union of the intersections of each element of ` A ` with ` B ` .
       (Contributed by FL, 24-Mar-2007.) $)
${
	$d A x y z $.
	$d B x y z $.
	iinuni_0 $f set z $.
	finuni_0 $f set x $.
	finuni_1 $f set y $.
	finuni_2 $f class A $.
	finuni_3 $f class B $.
	inuni $p |- ( U. A i^i B ) = U. { x | E. y e. A x = ( y i^i B ) } $= iinuni_0 finuni_2 cuni finuni_3 cin finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex finuni_0 cab cuni iinuni_0 sup_set_class finuni_2 cuni finuni_3 cin wcel iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 wex iinuni_0 sup_set_class finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex finuni_0 cab cuni wcel iinuni_0 sup_set_class finuni_2 cuni wcel iinuni_0 sup_set_class finuni_3 wcel wa iinuni_0 sup_set_class finuni_1 sup_set_class wcel finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_3 wcel wa iinuni_0 sup_set_class finuni_2 cuni finuni_3 cin wcel iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 wex iinuni_0 sup_set_class finuni_2 cuni wcel iinuni_0 sup_set_class finuni_1 sup_set_class wcel finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_3 wcel finuni_1 iinuni_0 sup_set_class finuni_2 eluni2 anbi1i iinuni_0 sup_set_class finuni_2 cuni finuni_3 elin iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 wex finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 wex finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_1 sup_set_class wcel finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_3 wcel wa iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 wex finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_1 finuni_2 wrex finuni_0 wex finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 wex finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_1 finuni_2 wrex finuni_0 iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex wa finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex ancom finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel finuni_1 finuni_2 r19.41v bitr4i exbii finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_1 finuni_0 finuni_2 rexcom4 bitr4i finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 wex finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_1 sup_set_class wcel iinuni_0 sup_set_class finuni_3 wcel wa finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_1 sup_set_class wcel finuni_1 finuni_2 wrex iinuni_0 sup_set_class finuni_3 wcel wa finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 wex iinuni_0 sup_set_class finuni_1 sup_set_class wcel iinuni_0 sup_set_class finuni_3 wcel wa finuni_1 finuni_2 finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq iinuni_0 sup_set_class finuni_0 sup_set_class wcel wa finuni_0 wex iinuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wcel iinuni_0 sup_set_class finuni_1 sup_set_class wcel iinuni_0 sup_set_class finuni_3 wcel wa iinuni_0 sup_set_class finuni_0 sup_set_class wcel iinuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wcel finuni_0 finuni_1 sup_set_class finuni_3 cin finuni_1 sup_set_class finuni_3 finuni_1 vex inex1 finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin iinuni_0 sup_set_class eleq2 ceqsexv iinuni_0 sup_set_class finuni_1 sup_set_class finuni_3 elin bitri rexbii iinuni_0 sup_set_class finuni_1 sup_set_class wcel iinuni_0 sup_set_class finuni_3 wcel finuni_1 finuni_2 r19.41v bitri bitri 3bitr4i finuni_0 sup_set_class finuni_1 sup_set_class finuni_3 cin wceq finuni_1 finuni_2 wrex finuni_0 iinuni_0 sup_set_class eluniab bitr4i eqriv $.
$}
$( Membership in a power class.  Theorem 86 of [Suppes] p. 47.  (Contributed
     by NM, 7-Aug-2000.) $)
${
	felpw2g_0 $f class A $.
	felpw2g_1 $f class B $.
	felpw2g_2 $f class V $.
	elpw2g $p |- ( B e. V -> ( A e. ~P B <-> A C_ B ) ) $= felpw2g_1 felpw2g_2 wcel felpw2g_0 felpw2g_1 cpw wcel felpw2g_0 felpw2g_1 wss felpw2g_0 felpw2g_1 elpwi felpw2g_0 felpw2g_1 wss felpw2g_1 felpw2g_2 wcel felpw2g_0 felpw2g_1 cpw wcel felpw2g_0 felpw2g_1 wss felpw2g_1 felpw2g_2 wcel felpw2g_0 cvv wcel felpw2g_0 felpw2g_1 cpw wcel felpw2g_0 felpw2g_1 felpw2g_2 ssexg felpw2g_0 cvv wcel felpw2g_0 felpw2g_1 cpw wcel felpw2g_0 felpw2g_1 wss felpw2g_0 felpw2g_1 cvv elpwg biimparc syldan expcom impbid2 $.
$}
$( Membership in a power class.  Theorem 86 of [Suppes] p. 47.
       (Contributed by NM, 11-Oct-2007.) $)
${
	felpw2_0 $f class A $.
	felpw2_1 $f class B $.
	eelpw2_0 $e |- B e. _V $.
	elpw2 $p |- ( A e. ~P B <-> A C_ B ) $= felpw2_1 cvv wcel felpw2_0 felpw2_1 cpw wcel felpw2_0 felpw2_1 wss wb eelpw2_0 felpw2_0 felpw2_1 cvv elpw2g ax-mp $.
$}
$( The power set of a set is never a subset.  (Contributed by Stefan
       O'Rear, 22-Feb-2015.) $)
${
	$d A x y $.
	$d V x y $.
	ipwnss_0 $f set x $.
	ipwnss_1 $f set y $.
	fpwnss_0 $f class A $.
	fpwnss_1 $f class V $.
	pwnss $p |- ( A e. V -> -. ~P A C_ A ) $= fpwnss_0 cpw fpwnss_0 wss ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 cpw wcel fpwnss_0 fpwnss_1 wcel fpwnss_0 cpw fpwnss_0 wss ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 cpw wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel wn wa wb ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 wcel wn ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel wn ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel wn ipwnss_1 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_1 sup_set_class ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wceq ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel ipwnss_1 sup_set_class ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wceq ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel wb ipwnss_1 sup_set_class ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_1 sup_set_class ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab eleq12 anidms notbid ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel wn ipwnss_0 ipwnss_1 fpwnss_0 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wcel wn ipwnss_0 sup_set_class ipwnss_1 sup_set_class wceq ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel wn ipwnss_0 sup_set_class ipwnss_0 sup_set_class df-nel ipwnss_0 sup_set_class ipwnss_1 sup_set_class wceq ipwnss_0 sup_set_class ipwnss_0 sup_set_class wcel ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel ipwnss_0 sup_set_class ipwnss_1 sup_set_class wceq ipwnss_0 sup_set_class ipwnss_0 sup_set_class wcel ipwnss_1 sup_set_class ipwnss_1 sup_set_class wcel wb ipwnss_0 sup_set_class ipwnss_1 sup_set_class ipwnss_0 sup_set_class ipwnss_1 sup_set_class eleq12 anidms notbid syl5bb cbvrabv elrab2 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 wcel pclem6 ax-mp fpwnss_0 cpw fpwnss_0 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab ssel mtoi fpwnss_0 fpwnss_1 wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 cpw wcel ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 wss ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 ssrab2 ipwnss_0 sup_set_class ipwnss_0 sup_set_class wnel ipwnss_0 fpwnss_0 crab fpwnss_0 fpwnss_1 elpw2g mpbiri nsyl3 $.
$}
$( No set equals its power set.  The sethood antecedent is necessary; compare
     ~ pwv .  (Contributed by NM, 17-Nov-2008.)  (Proof shortened by Mario
     Carneiro, 23-Dec-2016.) $)
${
	fpwne_0 $f class A $.
	fpwne_1 $f class V $.
	pwne $p |- ( A e. V -> ~P A =/= A ) $= fpwne_0 fpwne_1 wcel fpwne_0 cpw fpwne_0 wss wn fpwne_0 cpw fpwne_0 wne fpwne_0 fpwne_1 pwnss fpwne_0 cpw fpwne_0 wss fpwne_0 cpw fpwne_0 fpwne_0 cpw fpwne_0 eqimss necon3bi syl $.
$}

