$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/_Maps_to__notation.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             Function operation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c oF  $.
$c oR  $.
$( Extend class notation to include mapping of an operation to a function
     operation. $)
${
	$v R $.
	fcof_0 $f class R $.
	cof $a class oF R $.
$}
$( Extend class notation to include mapping of a binary relation to a
     function relation. $)
${
	$v R $.
	fcofr_0 $f class R $.
	cofr $a class oR R $.
$}
$( Define the function operation map.  The definition is designed so that
       if ` R ` is a binary operation, then ` oF R ` is the analogous operation
       on functions which corresponds to applying ` R ` pointwise to the values
       of the functions.  (Contributed by Mario Carneiro, 20-Jul-2014.) $)
${
	$v x $.
	$v R $.
	$v f $.
	$v g $.
	$d f g x R $.
	fdf-of_0 $f set x $.
	fdf-of_1 $f class R $.
	fdf-of_2 $f set f $.
	fdf-of_3 $f set g $.
	df-of $a |- oF R = ( f e. _V , g e. _V |-> ( x e. ( dom f i^i dom g ) |-> ( ( f ` x ) R ( g ` x ) ) ) ) $.
$}
$( Define the function relation map.  The definition is designed so that if
       ` R ` is a binary relation, then ` oF R ` is the analogous relation on
       functions which is true when each element of the left function relates
       to the corresponding element of the right function.  (Contributed by
       Mario Carneiro, 28-Jul-2014.) $)
${
	$v x $.
	$v R $.
	$v f $.
	$v g $.
	$d f g x R $.
	fdf-ofr_0 $f set x $.
	fdf-ofr_1 $f class R $.
	fdf-ofr_2 $f set f $.
	fdf-ofr_3 $f set g $.
	df-ofr $a |- oR R = { <. f , g >. | A. x e. ( dom f i^i dom g ) ( f ` x ) R ( g ` x ) } $.
$}
$( Equality theorem for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
${
	$v R $.
	$v S $.
	$v x $.
	$v f $.
	$v g $.
	$d f g x R $.
	$d f g x S $.
	iofeq_0 $f set x $.
	iofeq_1 $f set f $.
	iofeq_2 $f set g $.
	fofeq_0 $f class R $.
	fofeq_1 $f class S $.
	ofeq $p |- ( R = S -> oF R = oF S ) $= fofeq_0 fofeq_1 wceq iofeq_1 iofeq_2 cvv cvv iofeq_0 iofeq_1 sup_set_class cdm iofeq_2 sup_set_class cdm cin iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_0 co cmpt cmpt2 iofeq_1 iofeq_2 cvv cvv iofeq_0 iofeq_1 sup_set_class cdm iofeq_2 sup_set_class cdm cin iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_1 co cmpt cmpt2 fofeq_0 cof fofeq_1 cof fofeq_0 fofeq_1 wceq iofeq_1 iofeq_2 cvv cvv iofeq_0 iofeq_1 sup_set_class cdm iofeq_2 sup_set_class cdm cin iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_0 co cmpt iofeq_0 iofeq_1 sup_set_class cdm iofeq_2 sup_set_class cdm cin iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_1 co cmpt fofeq_0 fofeq_1 wceq iofeq_1 sup_set_class cvv wcel iofeq_2 sup_set_class cvv wcel w3a iofeq_0 iofeq_1 sup_set_class cdm iofeq_2 sup_set_class cdm cin iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_0 co iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_1 co fofeq_0 fofeq_1 wceq iofeq_1 sup_set_class cvv wcel iofeq_2 sup_set_class cvv wcel w3a fofeq_0 fofeq_1 iofeq_0 sup_set_class iofeq_1 sup_set_class cfv iofeq_0 sup_set_class iofeq_2 sup_set_class cfv fofeq_0 fofeq_1 wceq iofeq_1 sup_set_class cvv wcel iofeq_2 sup_set_class cvv wcel simp1 oveqd mpteq2dv mpt2eq3dva iofeq_0 fofeq_0 iofeq_1 iofeq_2 df-of iofeq_0 fofeq_1 iofeq_1 iofeq_2 df-of 3eqtr4g $.
$}
$( Equality theorem for function relation.  (Contributed by Mario Carneiro,
       28-Jul-2014.) $)
${
	$v R $.
	$v S $.
	$v x $.
	$v f $.
	$v g $.
	$d f g x R $.
	$d f g x S $.
	iofreq_0 $f set x $.
	iofreq_1 $f set f $.
	iofreq_2 $f set g $.
	fofreq_0 $f class R $.
	fofreq_1 $f class S $.
	ofreq $p |- ( R = S -> oR R = oR S ) $= fofreq_0 fofreq_1 wceq iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_0 wbr iofreq_0 iofreq_1 sup_set_class cdm iofreq_2 sup_set_class cdm cin wral iofreq_1 iofreq_2 copab iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_1 wbr iofreq_0 iofreq_1 sup_set_class cdm iofreq_2 sup_set_class cdm cin wral iofreq_1 iofreq_2 copab fofreq_0 cofr fofreq_1 cofr fofreq_0 fofreq_1 wceq iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_0 wbr iofreq_0 iofreq_1 sup_set_class cdm iofreq_2 sup_set_class cdm cin wral iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_1 wbr iofreq_0 iofreq_1 sup_set_class cdm iofreq_2 sup_set_class cdm cin wral iofreq_1 iofreq_2 fofreq_0 fofreq_1 wceq iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_0 wbr iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_1 wbr iofreq_0 iofreq_1 sup_set_class cdm iofreq_2 sup_set_class cdm cin iofreq_0 sup_set_class iofreq_1 sup_set_class cfv iofreq_0 sup_set_class iofreq_2 sup_set_class cfv fofreq_0 fofreq_1 breq ralbidv opabbidv iofreq_0 fofreq_0 iofreq_1 iofreq_2 df-ofr iofreq_0 fofreq_1 iofreq_1 iofreq_2 df-ofr 3eqtr4g $.
$}
$( A function operation restricted to a set is a set.  (Contributed by NM,
       28-Jul-2014.) $)
${
	$v A $.
	$v R $.
	$v V $.
	$v x $.
	$v f $.
	$v g $.
	$d f g x R $.
	$d f g x $.
	iofexg_0 $f set x $.
	iofexg_1 $f set f $.
	iofexg_2 $f set g $.
	fofexg_0 $f class A $.
	fofexg_1 $f class R $.
	fofexg_2 $f class V $.
	ofexg $p |- ( A e. V -> ( oF R |` A ) e. _V ) $= fofexg_1 cof wfun fofexg_0 fofexg_2 wcel fofexg_1 cof fofexg_0 cres cvv wcel iofexg_1 iofexg_2 cvv cvv iofexg_0 iofexg_1 sup_set_class cdm iofexg_2 sup_set_class cdm cin iofexg_0 sup_set_class iofexg_1 sup_set_class cfv iofexg_0 sup_set_class iofexg_2 sup_set_class cfv fofexg_1 co cmpt fofexg_1 cof iofexg_0 fofexg_1 iofexg_1 iofexg_2 df-of mpt2fun fofexg_1 cof fofexg_0 fofexg_2 resfunexg mpan $.
$}
$( Hypothesis builder for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
${
	$v x $.
	$v R $.
	$v y $.
	$v f $.
	$v g $.
	$d f g x y R $.
	$d f g x y $.
	infof_0 $f set y $.
	infof_1 $f set f $.
	infof_2 $f set g $.
	fnfof_0 $f set x $.
	fnfof_1 $f class R $.
	enfof_0 $e |- F/_ x R $.
	nfof $p |- F/_ x oF R $= fnfof_0 fnfof_1 cof infof_1 infof_2 cvv cvv infof_0 infof_1 sup_set_class cdm infof_2 sup_set_class cdm cin infof_0 sup_set_class infof_1 sup_set_class cfv infof_0 sup_set_class infof_2 sup_set_class cfv fnfof_1 co cmpt cmpt2 infof_0 fnfof_1 infof_1 infof_2 df-of infof_1 infof_2 fnfof_0 cvv cvv infof_0 infof_1 sup_set_class cdm infof_2 sup_set_class cdm cin infof_0 sup_set_class infof_1 sup_set_class cfv infof_0 sup_set_class infof_2 sup_set_class cfv fnfof_1 co cmpt fnfof_0 cvv nfcv fnfof_0 cvv nfcv fnfof_0 infof_0 infof_1 sup_set_class cdm infof_2 sup_set_class cdm cin infof_0 sup_set_class infof_1 sup_set_class cfv infof_0 sup_set_class infof_2 sup_set_class cfv fnfof_1 co fnfof_0 infof_1 sup_set_class cdm infof_2 sup_set_class cdm cin nfcv fnfof_0 infof_0 sup_set_class infof_1 sup_set_class cfv infof_0 sup_set_class infof_2 sup_set_class cfv fnfof_1 fnfof_0 infof_0 sup_set_class infof_1 sup_set_class cfv nfcv enfof_0 fnfof_0 infof_0 sup_set_class infof_2 sup_set_class cfv nfcv nfov nfmpt nfmpt2 nfcxfr $.
$}
$( Hypothesis builder for function relation.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)
${
	$v x $.
	$v R $.
	$v y $.
	$v f $.
	$v g $.
	$d f g x y R $.
	$d f g x y $.
	infofr_0 $f set y $.
	infofr_1 $f set f $.
	infofr_2 $f set g $.
	fnfofr_0 $f set x $.
	fnfofr_1 $f class R $.
	enfofr_0 $e |- F/_ x R $.
	nfofr $p |- F/_ x oR R $= fnfofr_0 fnfofr_1 cofr infofr_0 sup_set_class infofr_1 sup_set_class cfv infofr_0 sup_set_class infofr_2 sup_set_class cfv fnfofr_1 wbr infofr_0 infofr_1 sup_set_class cdm infofr_2 sup_set_class cdm cin wral infofr_1 infofr_2 copab infofr_0 fnfofr_1 infofr_1 infofr_2 df-ofr infofr_0 sup_set_class infofr_1 sup_set_class cfv infofr_0 sup_set_class infofr_2 sup_set_class cfv fnfofr_1 wbr infofr_0 infofr_1 sup_set_class cdm infofr_2 sup_set_class cdm cin wral infofr_1 infofr_2 fnfofr_0 infofr_0 sup_set_class infofr_1 sup_set_class cfv infofr_0 sup_set_class infofr_2 sup_set_class cfv fnfofr_1 wbr fnfofr_0 infofr_0 infofr_1 sup_set_class cdm infofr_2 sup_set_class cdm cin fnfofr_0 infofr_1 sup_set_class cdm infofr_2 sup_set_class cdm cin nfcv fnfofr_0 infofr_0 sup_set_class infofr_1 sup_set_class cfv infofr_0 sup_set_class infofr_2 sup_set_class cfv fnfofr_1 fnfofr_0 infofr_0 sup_set_class infofr_1 sup_set_class cfv nfcv enfofr_0 fnfofr_0 infofr_0 sup_set_class infofr_2 sup_set_class cfv nfcv nfbr nfral nfopab nfcxfr $.
$}
$( Value of an operation applied to two functions.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v f $.
	$v g $.
	$d x A $.
	$d f g x F $.
	$d f g x G $.
	$d x ph $.
	$d x S $.
	$d f g x R $.
	ioffval_0 $f set f $.
	ioffval_1 $f set g $.
	foffval_0 $f wff ph $.
	foffval_1 $f set x $.
	foffval_2 $f class A $.
	foffval_3 $f class B $.
	foffval_4 $f class C $.
	foffval_5 $f class D $.
	foffval_6 $f class R $.
	foffval_7 $f class S $.
	foffval_8 $f class F $.
	foffval_9 $f class G $.
	foffval_10 $f class V $.
	foffval_11 $f class W $.
	eoffval_0 $e |- ( ph -> F Fn A ) $.
	eoffval_1 $e |- ( ph -> G Fn B ) $.
	eoffval_2 $e |- ( ph -> A e. V ) $.
	eoffval_3 $e |- ( ph -> B e. W ) $.
	eoffval_4 $e |- ( A i^i B ) = S $.
	eoffval_5 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = C ) $.
	eoffval_6 $e |- ( ( ph /\ x e. B ) -> ( G ` x ) = D ) $.
	offval $p |- ( ph -> ( F oF R G ) = ( x e. S |-> ( C R D ) ) ) $= foffval_0 foffval_8 foffval_9 foffval_6 cof co foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_1 foffval_7 foffval_4 foffval_5 foffval_6 co cmpt foffval_0 foffval_8 cvv wcel foffval_9 cvv wcel foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt cvv wcel foffval_8 foffval_9 foffval_6 cof co foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt wceq foffval_0 foffval_8 foffval_2 wfn foffval_2 foffval_10 wcel foffval_8 cvv wcel eoffval_0 eoffval_2 foffval_2 foffval_10 foffval_8 fnex syl2anc foffval_0 foffval_9 foffval_3 wfn foffval_3 foffval_11 wcel foffval_9 cvv wcel eoffval_1 eoffval_3 foffval_3 foffval_11 foffval_9 fnex syl2anc foffval_0 foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt cvv foffval_0 foffval_8 cdm foffval_9 cdm cin foffval_7 wceq foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt wceq foffval_0 foffval_8 cdm foffval_9 cdm cin foffval_2 foffval_3 cin foffval_7 foffval_0 foffval_8 cdm foffval_2 foffval_9 cdm foffval_3 foffval_0 foffval_8 foffval_2 wfn foffval_8 cdm foffval_2 wceq eoffval_0 foffval_2 foffval_8 fndm syl foffval_0 foffval_9 foffval_3 wfn foffval_9 cdm foffval_3 wceq eoffval_1 foffval_3 foffval_9 fndm syl ineq12d eoffval_4 syl6eq foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co mpteq1 syl foffval_0 foffval_2 foffval_10 wcel foffval_7 cvv wcel foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt cvv wcel eoffval_2 foffval_2 foffval_10 wcel foffval_7 foffval_2 foffval_3 cin cvv eoffval_4 foffval_2 foffval_3 foffval_10 inex1g syl5eqelr foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cvv mptexg 3syl eqeltrd ioffval_0 ioffval_1 foffval_8 foffval_9 cvv cvv foffval_1 ioffval_0 sup_set_class cdm ioffval_1 sup_set_class cdm cin foffval_1 sup_set_class ioffval_0 sup_set_class cfv foffval_1 sup_set_class ioffval_1 sup_set_class cfv foffval_6 co cmpt foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_6 cof cvv ioffval_0 sup_set_class foffval_8 wceq ioffval_1 sup_set_class foffval_9 wceq wa foffval_1 ioffval_0 sup_set_class cdm ioffval_1 sup_set_class cdm cin foffval_1 sup_set_class ioffval_0 sup_set_class cfv foffval_1 sup_set_class ioffval_1 sup_set_class cfv foffval_6 co foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co ioffval_0 sup_set_class foffval_8 wceq ioffval_1 sup_set_class foffval_9 wceq ioffval_0 sup_set_class cdm foffval_8 cdm ioffval_1 sup_set_class cdm foffval_9 cdm ioffval_0 sup_set_class foffval_8 dmeq ioffval_1 sup_set_class foffval_9 dmeq ineqan12d ioffval_0 sup_set_class foffval_8 wceq ioffval_1 sup_set_class foffval_9 wceq foffval_1 sup_set_class ioffval_0 sup_set_class cfv foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class ioffval_1 sup_set_class cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 foffval_1 sup_set_class ioffval_0 sup_set_class foffval_8 fveq1 foffval_1 sup_set_class ioffval_1 sup_set_class foffval_9 fveq1 oveqan12d mpteq12dv foffval_1 foffval_6 ioffval_0 ioffval_1 df-of ovmpt2ga syl3anc foffval_0 foffval_8 cdm foffval_9 cdm cin foffval_7 wceq foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co cmpt wceq foffval_0 foffval_8 cdm foffval_9 cdm cin foffval_2 foffval_3 cin foffval_7 foffval_0 foffval_8 cdm foffval_2 foffval_9 cdm foffval_3 foffval_0 foffval_8 foffval_2 wfn foffval_8 cdm foffval_2 wceq eoffval_0 foffval_2 foffval_8 fndm syl foffval_0 foffval_9 foffval_3 wfn foffval_9 cdm foffval_3 wceq eoffval_1 foffval_3 foffval_9 fndm syl ineq12d eoffval_4 syl6eq foffval_1 foffval_8 cdm foffval_9 cdm cin foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co mpteq1 syl foffval_0 foffval_1 foffval_7 foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co foffval_4 foffval_5 foffval_6 co foffval_1 sup_set_class foffval_7 wcel foffval_0 foffval_1 sup_set_class foffval_2 wcel foffval_1 sup_set_class foffval_3 wcel wa foffval_1 sup_set_class foffval_8 cfv foffval_1 sup_set_class foffval_9 cfv foffval_6 co foffval_4 foffval_5 foffval_6 co wceq foffval_1 sup_set_class foffval_7 wcel foffval_1 sup_set_class foffval_2 foffval_3 cin wcel foffval_1 sup_set_class foffval_2 wcel foffval_1 sup_set_class foffval_3 wcel wa foffval_2 foffval_3 cin foffval_7 foffval_1 sup_set_class eoffval_4 eleq2i foffval_1 sup_set_class foffval_2 foffval_3 elin bitr3i foffval_0 foffval_1 sup_set_class foffval_2 wcel foffval_1 sup_set_class foffval_3 wcel wa wa foffval_1 sup_set_class foffval_8 cfv foffval_4 foffval_1 sup_set_class foffval_9 cfv foffval_5 foffval_6 foffval_0 foffval_1 sup_set_class foffval_2 wcel foffval_1 sup_set_class foffval_8 cfv foffval_4 wceq foffval_1 sup_set_class foffval_3 wcel eoffval_5 adantrr foffval_0 foffval_1 sup_set_class foffval_3 wcel foffval_1 sup_set_class foffval_9 cfv foffval_5 wceq foffval_1 sup_set_class foffval_2 wcel eoffval_6 adantrl oveq12d sylan2b mpteq2dva 3eqtrd $.
$}
$( Value of a relation applied to two functions.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v f $.
	$v g $.
	$d x A $.
	$d f g x F $.
	$d f g x G $.
	$d x ph $.
	$d x S $.
	$d f g x R $.
	iofrfval_0 $f set f $.
	iofrfval_1 $f set g $.
	fofrfval_0 $f wff ph $.
	fofrfval_1 $f set x $.
	fofrfval_2 $f class A $.
	fofrfval_3 $f class B $.
	fofrfval_4 $f class C $.
	fofrfval_5 $f class D $.
	fofrfval_6 $f class R $.
	fofrfval_7 $f class S $.
	fofrfval_8 $f class F $.
	fofrfval_9 $f class G $.
	fofrfval_10 $f class V $.
	fofrfval_11 $f class W $.
	eofrfval_0 $e |- ( ph -> F Fn A ) $.
	eofrfval_1 $e |- ( ph -> G Fn B ) $.
	eofrfval_2 $e |- ( ph -> A e. V ) $.
	eofrfval_3 $e |- ( ph -> B e. W ) $.
	eofrfval_4 $e |- ( A i^i B ) = S $.
	eofrfval_5 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = C ) $.
	eofrfval_6 $e |- ( ( ph /\ x e. B ) -> ( G ` x ) = D ) $.
	ofrfval $p |- ( ph -> ( F oR R G <-> A. x e. S C R D ) ) $= fofrfval_0 fofrfval_8 fofrfval_9 fofrfval_6 cofr wbr fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 fofrfval_8 cdm fofrfval_9 cdm cin wral fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 fofrfval_7 wral fofrfval_4 fofrfval_5 fofrfval_6 wbr fofrfval_1 fofrfval_7 wral fofrfval_0 fofrfval_8 cvv wcel fofrfval_9 cvv wcel fofrfval_8 fofrfval_9 fofrfval_6 cofr wbr fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 fofrfval_8 cdm fofrfval_9 cdm cin wral wb fofrfval_0 fofrfval_8 fofrfval_2 wfn fofrfval_2 fofrfval_10 wcel fofrfval_8 cvv wcel eofrfval_0 eofrfval_2 fofrfval_2 fofrfval_10 fofrfval_8 fnex syl2anc fofrfval_0 fofrfval_9 fofrfval_3 wfn fofrfval_3 fofrfval_11 wcel fofrfval_9 cvv wcel eofrfval_1 eofrfval_3 fofrfval_3 fofrfval_11 fofrfval_9 fnex syl2anc fofrfval_1 sup_set_class iofrfval_0 sup_set_class cfv fofrfval_1 sup_set_class iofrfval_1 sup_set_class cfv fofrfval_6 wbr fofrfval_1 iofrfval_0 sup_set_class cdm iofrfval_1 sup_set_class cdm cin wral fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 fofrfval_8 cdm fofrfval_9 cdm cin wral iofrfval_0 iofrfval_1 fofrfval_8 fofrfval_9 fofrfval_6 cofr cvv cvv iofrfval_0 sup_set_class fofrfval_8 wceq iofrfval_1 sup_set_class fofrfval_9 wceq wa fofrfval_1 sup_set_class iofrfval_0 sup_set_class cfv fofrfval_1 sup_set_class iofrfval_1 sup_set_class cfv fofrfval_6 wbr fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 iofrfval_0 sup_set_class cdm iofrfval_1 sup_set_class cdm cin fofrfval_8 cdm fofrfval_9 cdm cin iofrfval_0 sup_set_class fofrfval_8 wceq iofrfval_1 sup_set_class fofrfval_9 wceq iofrfval_0 sup_set_class cdm fofrfval_8 cdm iofrfval_1 sup_set_class cdm fofrfval_9 cdm iofrfval_0 sup_set_class fofrfval_8 dmeq iofrfval_1 sup_set_class fofrfval_9 dmeq ineqan12d iofrfval_0 sup_set_class fofrfval_8 wceq iofrfval_1 sup_set_class fofrfval_9 wceq fofrfval_1 sup_set_class iofrfval_0 sup_set_class cfv fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class iofrfval_1 sup_set_class cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 fofrfval_1 sup_set_class iofrfval_0 sup_set_class fofrfval_8 fveq1 fofrfval_1 sup_set_class iofrfval_1 sup_set_class fofrfval_9 fveq1 breqan12d raleqbidv fofrfval_1 fofrfval_6 iofrfval_0 iofrfval_1 df-ofr brabga syl2anc fofrfval_0 fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_1 fofrfval_8 cdm fofrfval_9 cdm cin fofrfval_7 fofrfval_0 fofrfval_8 cdm fofrfval_9 cdm cin fofrfval_2 fofrfval_3 cin fofrfval_7 fofrfval_0 fofrfval_8 cdm fofrfval_2 fofrfval_9 cdm fofrfval_3 fofrfval_0 fofrfval_8 fofrfval_2 wfn fofrfval_8 cdm fofrfval_2 wceq eofrfval_0 fofrfval_2 fofrfval_8 fndm syl fofrfval_0 fofrfval_9 fofrfval_3 wfn fofrfval_9 cdm fofrfval_3 wceq eofrfval_1 fofrfval_3 fofrfval_9 fndm syl ineq12d eofrfval_4 syl6eq raleqdv fofrfval_0 fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_6 wbr fofrfval_4 fofrfval_5 fofrfval_6 wbr fofrfval_1 fofrfval_7 fofrfval_0 fofrfval_1 sup_set_class fofrfval_7 wcel wa fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_4 fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_5 fofrfval_6 fofrfval_1 sup_set_class fofrfval_7 wcel fofrfval_0 fofrfval_1 sup_set_class fofrfval_2 wcel fofrfval_1 sup_set_class fofrfval_8 cfv fofrfval_4 wceq fofrfval_7 fofrfval_2 fofrfval_1 sup_set_class fofrfval_7 fofrfval_2 fofrfval_3 cin fofrfval_2 eofrfval_4 fofrfval_2 fofrfval_3 inss1 eqsstr3i sseli eofrfval_5 sylan2 fofrfval_1 sup_set_class fofrfval_7 wcel fofrfval_0 fofrfval_1 sup_set_class fofrfval_3 wcel fofrfval_1 sup_set_class fofrfval_9 cfv fofrfval_5 wceq fofrfval_7 fofrfval_3 fofrfval_1 sup_set_class fofrfval_7 fofrfval_2 fofrfval_3 cin fofrfval_3 eofrfval_4 fofrfval_2 fofrfval_3 inss2 eqsstr3i sseli eofrfval_6 sylan2 breq12d ralbidva 3bitrd $.
$}
$( Evaluate a function operation at a point.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v X $.
	$v x $.
	$d x A $.
	$d x F $.
	$d x G $.
	$d x ph $.
	$d x S $.
	$d x X $.
	$d x R $.
	iofval_0 $f set x $.
	fofval_0 $f wff ph $.
	fofval_1 $f class A $.
	fofval_2 $f class B $.
	fofval_3 $f class C $.
	fofval_4 $f class D $.
	fofval_5 $f class R $.
	fofval_6 $f class S $.
	fofval_7 $f class F $.
	fofval_8 $f class G $.
	fofval_9 $f class V $.
	fofval_10 $f class W $.
	fofval_11 $f class X $.
	eofval_0 $e |- ( ph -> F Fn A ) $.
	eofval_1 $e |- ( ph -> G Fn B ) $.
	eofval_2 $e |- ( ph -> A e. V ) $.
	eofval_3 $e |- ( ph -> B e. W ) $.
	eofval_4 $e |- ( A i^i B ) = S $.
	eofval_5 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	eofval_6 $e |- ( ( ph /\ X e. B ) -> ( G ` X ) = D ) $.
	ofval $p |- ( ( ph /\ X e. S ) -> ( ( F oF R G ) ` X ) = ( C R D ) ) $= fofval_0 fofval_11 fofval_6 wcel wa fofval_11 fofval_7 fofval_8 fofval_5 cof co cfv fofval_11 iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt cfv fofval_11 fofval_7 cfv fofval_11 fofval_8 cfv fofval_5 co fofval_3 fofval_4 fofval_5 co fofval_0 fofval_11 fofval_7 fofval_8 fofval_5 cof co cfv fofval_11 iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt cfv wceq fofval_11 fofval_6 wcel fofval_0 fofval_11 fofval_7 fofval_8 fofval_5 cof co iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt fofval_0 iofval_0 fofval_1 fofval_2 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 fofval_6 fofval_7 fofval_8 fofval_9 fofval_10 eofval_0 eofval_1 eofval_2 eofval_3 eofval_4 fofval_0 iofval_0 sup_set_class fofval_1 wcel wa iofval_0 sup_set_class fofval_7 cfv eqidd fofval_0 iofval_0 sup_set_class fofval_2 wcel wa iofval_0 sup_set_class fofval_8 cfv eqidd offval fveq1d adantr fofval_11 fofval_6 wcel fofval_11 iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt cfv fofval_11 fofval_7 cfv fofval_11 fofval_8 cfv fofval_5 co wceq fofval_0 iofval_0 fofval_11 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co fofval_11 fofval_7 cfv fofval_11 fofval_8 cfv fofval_5 co fofval_6 iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt iofval_0 sup_set_class fofval_11 wceq iofval_0 sup_set_class fofval_7 cfv fofval_11 fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_11 fofval_8 cfv fofval_5 iofval_0 sup_set_class fofval_11 fofval_7 fveq2 iofval_0 sup_set_class fofval_11 fofval_8 fveq2 oveq12d iofval_0 fofval_6 iofval_0 sup_set_class fofval_7 cfv iofval_0 sup_set_class fofval_8 cfv fofval_5 co cmpt eqid fofval_11 fofval_7 cfv fofval_11 fofval_8 cfv fofval_5 ovex fvmpt adantl fofval_0 fofval_11 fofval_6 wcel wa fofval_11 fofval_7 cfv fofval_3 fofval_11 fofval_8 cfv fofval_4 fofval_5 fofval_11 fofval_6 wcel fofval_0 fofval_11 fofval_1 wcel fofval_11 fofval_7 cfv fofval_3 wceq fofval_6 fofval_1 fofval_11 fofval_6 fofval_1 fofval_2 cin fofval_1 eofval_4 fofval_1 fofval_2 inss1 eqsstr3i sseli eofval_5 sylan2 fofval_11 fofval_6 wcel fofval_0 fofval_11 fofval_2 wcel fofval_11 fofval_8 cfv fofval_4 wceq fofval_6 fofval_2 fofval_11 fofval_6 fofval_1 fofval_2 cin fofval_2 eofval_4 fofval_1 fofval_2 inss2 eqsstr3i sseli eofval_6 sylan2 oveq12d 3eqtrd $.
$}
$( Exhibit a function relation at a point.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v X $.
	$v x $.
	$d x A $.
	$d x F $.
	$d x G $.
	$d x ph $.
	$d x S $.
	$d x X $.
	$d x R $.
	iofrval_0 $f set x $.
	fofrval_0 $f wff ph $.
	fofrval_1 $f class A $.
	fofrval_2 $f class B $.
	fofrval_3 $f class C $.
	fofrval_4 $f class D $.
	fofrval_5 $f class R $.
	fofrval_6 $f class S $.
	fofrval_7 $f class F $.
	fofrval_8 $f class G $.
	fofrval_9 $f class V $.
	fofrval_10 $f class W $.
	fofrval_11 $f class X $.
	eofrval_0 $e |- ( ph -> F Fn A ) $.
	eofrval_1 $e |- ( ph -> G Fn B ) $.
	eofrval_2 $e |- ( ph -> A e. V ) $.
	eofrval_3 $e |- ( ph -> B e. W ) $.
	eofrval_4 $e |- ( A i^i B ) = S $.
	eofrval_5 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	eofrval_6 $e |- ( ( ph /\ X e. B ) -> ( G ` X ) = D ) $.
	ofrval $p |- ( ( ph /\ F oR R G /\ X e. S ) -> C R D ) $= fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel w3a fofrval_11 fofrval_7 cfv fofrval_11 fofrval_8 cfv fofrval_3 fofrval_4 fofrval_5 fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel fofrval_11 fofrval_7 cfv fofrval_11 fofrval_8 cfv fofrval_5 wbr fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr wa iofrval_0 sup_set_class fofrval_7 cfv iofrval_0 sup_set_class fofrval_8 cfv fofrval_5 wbr iofrval_0 fofrval_6 wral fofrval_11 fofrval_6 wcel fofrval_11 fofrval_7 cfv fofrval_11 fofrval_8 cfv fofrval_5 wbr wi fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr iofrval_0 sup_set_class fofrval_7 cfv iofrval_0 sup_set_class fofrval_8 cfv fofrval_5 wbr iofrval_0 fofrval_6 wral fofrval_0 iofrval_0 fofrval_1 fofrval_2 iofrval_0 sup_set_class fofrval_7 cfv iofrval_0 sup_set_class fofrval_8 cfv fofrval_5 fofrval_6 fofrval_7 fofrval_8 fofrval_9 fofrval_10 eofrval_0 eofrval_1 eofrval_2 eofrval_3 eofrval_4 fofrval_0 iofrval_0 sup_set_class fofrval_1 wcel wa iofrval_0 sup_set_class fofrval_7 cfv eqidd fofrval_0 iofrval_0 sup_set_class fofrval_2 wcel wa iofrval_0 sup_set_class fofrval_8 cfv eqidd ofrfval biimpa iofrval_0 sup_set_class fofrval_7 cfv iofrval_0 sup_set_class fofrval_8 cfv fofrval_5 wbr fofrval_11 fofrval_7 cfv fofrval_11 fofrval_8 cfv fofrval_5 wbr iofrval_0 fofrval_11 fofrval_6 iofrval_0 sup_set_class fofrval_11 wceq iofrval_0 sup_set_class fofrval_7 cfv fofrval_11 fofrval_7 cfv iofrval_0 sup_set_class fofrval_8 cfv fofrval_11 fofrval_8 cfv fofrval_5 iofrval_0 sup_set_class fofrval_11 fofrval_7 fveq2 iofrval_0 sup_set_class fofrval_11 fofrval_8 fveq2 breq12d rspccv syl 3impia fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel w3a fofrval_0 fofrval_11 fofrval_1 wcel fofrval_11 fofrval_7 cfv fofrval_3 wceq fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel simp1 fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel w3a fofrval_6 fofrval_1 fofrval_11 fofrval_6 fofrval_1 fofrval_2 cin fofrval_1 eofrval_4 fofrval_1 fofrval_2 inss1 eqsstr3i fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel simp3 sseldi eofrval_5 syl2anc fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel w3a fofrval_0 fofrval_11 fofrval_2 wcel fofrval_11 fofrval_8 cfv fofrval_4 wceq fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel simp1 fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel w3a fofrval_6 fofrval_2 fofrval_11 fofrval_6 fofrval_1 fofrval_2 cin fofrval_2 eofrval_4 fofrval_1 fofrval_2 inss2 eqsstr3i fofrval_0 fofrval_7 fofrval_8 fofrval_5 cofr wbr fofrval_11 fofrval_6 wcel simp3 sseldi eofrval_6 syl2anc 3brtr3d $.
$}
$( The function operation produces a function.  (Contributed by Mario
       Carneiro, 22-Jul-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v x $.
	$d x A $.
	$d x F $.
	$d x G $.
	$d x ph $.
	$d x S $.
	$d x R $.
	ioffn_0 $f set x $.
	foffn_0 $f wff ph $.
	foffn_1 $f class A $.
	foffn_2 $f class B $.
	foffn_3 $f class R $.
	foffn_4 $f class S $.
	foffn_5 $f class F $.
	foffn_6 $f class G $.
	foffn_7 $f class V $.
	foffn_8 $f class W $.
	eoffn_0 $e |- ( ph -> F Fn A ) $.
	eoffn_1 $e |- ( ph -> G Fn B ) $.
	eoffn_2 $e |- ( ph -> A e. V ) $.
	eoffn_3 $e |- ( ph -> B e. W ) $.
	eoffn_4 $e |- ( A i^i B ) = S $.
	offn $p |- ( ph -> ( F oF R G ) Fn S ) $= foffn_0 foffn_5 foffn_6 foffn_3 cof co foffn_4 wfn ioffn_0 foffn_4 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 co cmpt foffn_4 wfn ioffn_0 foffn_4 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 co ioffn_0 foffn_4 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 co cmpt ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 ovex ioffn_0 foffn_4 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 co cmpt eqid fnmpti foffn_0 foffn_4 foffn_5 foffn_6 foffn_3 cof co ioffn_0 foffn_4 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 co cmpt foffn_0 ioffn_0 foffn_1 foffn_2 ioffn_0 sup_set_class foffn_5 cfv ioffn_0 sup_set_class foffn_6 cfv foffn_3 foffn_4 foffn_5 foffn_6 foffn_7 foffn_8 eoffn_0 eoffn_1 eoffn_2 eoffn_3 eoffn_4 foffn_0 ioffn_0 sup_set_class foffn_1 wcel wa ioffn_0 sup_set_class foffn_5 cfv eqidd foffn_0 ioffn_0 sup_set_class foffn_2 wcel wa ioffn_0 sup_set_class foffn_6 cfv eqidd offval fneq1d mpbiri $.
$}
$( Function value of a pointwise composition.  (Contributed by Stefan O'Rear,
     5-Oct-2014.)  (Proof shortened by Mario Carneiro, 5-Jun-2015.) $)
${
	$v A $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v X $.
	ffnfvof_0 $f class A $.
	ffnfvof_1 $f class R $.
	ffnfvof_2 $f class F $.
	ffnfvof_3 $f class G $.
	ffnfvof_4 $f class V $.
	ffnfvof_5 $f class X $.
	fnfvof $p |- ( ( ( F Fn A /\ G Fn A ) /\ ( A e. V /\ X e. A ) ) -> ( ( F oF R G ) ` X ) = ( ( F ` X ) R ( G ` X ) ) ) $= ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel ffnfvof_5 ffnfvof_0 wcel ffnfvof_5 ffnfvof_2 ffnfvof_3 ffnfvof_1 cof co cfv ffnfvof_5 ffnfvof_2 cfv ffnfvof_5 ffnfvof_3 cfv ffnfvof_1 co wceq ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel wa ffnfvof_0 ffnfvof_0 ffnfvof_5 ffnfvof_2 cfv ffnfvof_5 ffnfvof_3 cfv ffnfvof_1 ffnfvof_0 ffnfvof_2 ffnfvof_3 ffnfvof_4 ffnfvof_4 ffnfvof_5 ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn ffnfvof_0 ffnfvof_4 wcel simpll ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn ffnfvof_0 ffnfvof_4 wcel simplr ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel simpr ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel simpr ffnfvof_0 inidm ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel wa ffnfvof_5 ffnfvof_0 wcel wa ffnfvof_5 ffnfvof_2 cfv eqidd ffnfvof_2 ffnfvof_0 wfn ffnfvof_3 ffnfvof_0 wfn wa ffnfvof_0 ffnfvof_4 wcel wa ffnfvof_5 ffnfvof_0 wcel wa ffnfvof_5 ffnfvof_3 cfv eqidd ofval anasss $.
$}
$( General value of ` ( F oF R G ) ` with no assumptions on functionality
       of ` F ` and ` G ` .  (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
${
	$v x $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v a $.
	$v b $.
	$d F x a b $.
	$d G x a b $.
	$d V x $.
	$d W x $.
	$d R x a b $.
	ioffval3_0 $f set a $.
	ioffval3_1 $f set b $.
	foffval3_0 $f set x $.
	foffval3_1 $f class R $.
	foffval3_2 $f class F $.
	foffval3_3 $f class G $.
	foffval3_4 $f class V $.
	foffval3_5 $f class W $.
	offval3 $p |- ( ( F e. V /\ G e. W ) -> ( F oF R G ) = ( x e. ( dom F i^i dom G ) |-> ( ( F ` x ) R ( G ` x ) ) ) ) $= foffval3_2 foffval3_4 wcel foffval3_3 foffval3_5 wcel wa foffval3_2 cvv wcel foffval3_3 cvv wcel foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cmpt cvv wcel foffval3_2 foffval3_3 foffval3_1 cof co foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cmpt wceq foffval3_2 foffval3_4 wcel foffval3_2 cvv wcel foffval3_3 foffval3_5 wcel foffval3_2 foffval3_4 elex adantr foffval3_3 foffval3_5 wcel foffval3_3 cvv wcel foffval3_2 foffval3_4 wcel foffval3_3 foffval3_5 elex adantl foffval3_2 foffval3_4 wcel foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cmpt cvv wcel foffval3_3 foffval3_5 wcel foffval3_2 foffval3_4 wcel foffval3_2 cdm cvv wcel foffval3_2 cdm foffval3_3 cdm cin cvv wcel foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cmpt cvv wcel foffval3_2 foffval3_4 dmexg foffval3_2 cdm foffval3_3 cdm cvv inex1g foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cvv mptexg 3syl adantr ioffval3_0 ioffval3_1 foffval3_2 foffval3_3 cvv cvv foffval3_0 ioffval3_0 sup_set_class cdm ioffval3_1 sup_set_class cdm cin foffval3_0 sup_set_class ioffval3_0 sup_set_class cfv foffval3_0 sup_set_class ioffval3_1 sup_set_class cfv foffval3_1 co cmpt foffval3_0 foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co cmpt foffval3_1 cof cvv ioffval3_0 sup_set_class foffval3_2 wceq ioffval3_1 sup_set_class foffval3_3 wceq wa foffval3_0 ioffval3_0 sup_set_class cdm ioffval3_1 sup_set_class cdm cin foffval3_0 sup_set_class ioffval3_0 sup_set_class cfv foffval3_0 sup_set_class ioffval3_1 sup_set_class cfv foffval3_1 co foffval3_2 cdm foffval3_3 cdm cin foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 co ioffval3_0 sup_set_class foffval3_2 wceq ioffval3_1 sup_set_class foffval3_3 wceq ioffval3_0 sup_set_class cdm foffval3_2 cdm ioffval3_1 sup_set_class cdm foffval3_3 cdm ioffval3_0 sup_set_class foffval3_2 dmeq ioffval3_1 sup_set_class foffval3_3 dmeq ineqan12d ioffval3_0 sup_set_class foffval3_2 wceq ioffval3_1 sup_set_class foffval3_3 wceq foffval3_0 sup_set_class ioffval3_0 sup_set_class cfv foffval3_0 sup_set_class foffval3_2 cfv foffval3_0 sup_set_class ioffval3_1 sup_set_class cfv foffval3_0 sup_set_class foffval3_3 cfv foffval3_1 foffval3_0 sup_set_class ioffval3_0 sup_set_class foffval3_2 fveq1 foffval3_0 sup_set_class ioffval3_1 sup_set_class foffval3_3 fveq1 oveqan12d mpteq12dv foffval3_0 foffval3_1 ioffval3_0 ioffval3_1 df-of ovmpt2ga syl3anc $.
$}
$( Pointwise combination commutes with restriction.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)
${
	$v D $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v x $.
	$d F x $.
	$d G x $.
	$d V x $.
	$d W x $.
	$d R x $.
	$d D x $.
	ioffres_0 $f set x $.
	foffres_0 $f class D $.
	foffres_1 $f class R $.
	foffres_2 $f class F $.
	foffres_3 $f class G $.
	foffres_4 $f class V $.
	foffres_5 $f class W $.
	offres $p |- ( ( F e. V /\ G e. W ) -> ( ( F oF R G ) |` D ) = ( ( F |` D ) oF R ( G |` D ) ) ) $= foffres_2 foffres_4 wcel foffres_3 foffres_5 wcel wa ioffres_0 foffres_2 cdm foffres_3 cdm cin ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co cmpt foffres_0 cres ioffres_0 foffres_2 foffres_0 cres cdm foffres_3 foffres_0 cres cdm cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co cmpt foffres_2 foffres_3 foffres_1 cof co foffres_0 cres foffres_2 foffres_0 cres foffres_3 foffres_0 cres foffres_1 cof co ioffres_0 foffres_2 cdm foffres_3 cdm cin foffres_0 cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co cmpt ioffres_0 foffres_2 cdm foffres_3 cdm cin foffres_0 cin ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co cmpt ioffres_0 foffres_2 foffres_0 cres cdm foffres_3 foffres_0 cres cdm cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co cmpt ioffres_0 foffres_2 cdm foffres_3 cdm cin ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co cmpt foffres_0 cres ioffres_0 foffres_2 cdm foffres_3 cdm cin foffres_0 cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co ioffres_0 sup_set_class foffres_2 cdm foffres_3 cdm cin foffres_0 cin wcel ioffres_0 sup_set_class foffres_0 wcel ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co wceq foffres_2 cdm foffres_3 cdm cin foffres_0 cin foffres_0 ioffres_0 sup_set_class foffres_2 cdm foffres_3 cdm cin foffres_0 inss2 sseli ioffres_0 sup_set_class foffres_0 wcel ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 ioffres_0 sup_set_class foffres_0 foffres_2 fvres ioffres_0 sup_set_class foffres_0 foffres_3 fvres oveq12d syl mpteq2ia ioffres_0 foffres_2 foffres_0 cres cdm foffres_3 foffres_0 cres cdm cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co foffres_2 cdm foffres_3 cdm cin foffres_0 cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co foffres_0 foffres_2 cdm foffres_3 cdm cin cin foffres_0 foffres_2 cdm cin foffres_0 foffres_3 cdm cin cin foffres_2 cdm foffres_3 cdm cin foffres_0 cin foffres_2 foffres_0 cres cdm foffres_3 foffres_0 cres cdm cin foffres_0 foffres_2 cdm foffres_3 cdm inindi foffres_2 cdm foffres_3 cdm cin foffres_0 incom foffres_2 foffres_0 cres cdm foffres_0 foffres_2 cdm cin foffres_3 foffres_0 cres cdm foffres_0 foffres_3 cdm cin foffres_2 foffres_0 dmres foffres_3 foffres_0 dmres ineq12i 3eqtr4ri ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co eqid mpteq12i ioffres_0 foffres_2 cdm foffres_3 cdm cin foffres_0 ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co resmpt3 3eqtr4ri foffres_2 foffres_4 wcel foffres_3 foffres_5 wcel wa foffres_2 foffres_3 foffres_1 cof co ioffres_0 foffres_2 cdm foffres_3 cdm cin ioffres_0 sup_set_class foffres_2 cfv ioffres_0 sup_set_class foffres_3 cfv foffres_1 co cmpt foffres_0 ioffres_0 foffres_1 foffres_2 foffres_3 foffres_4 foffres_5 offval3 reseq1d foffres_2 foffres_4 wcel foffres_2 foffres_0 cres cvv wcel foffres_3 foffres_0 cres cvv wcel foffres_2 foffres_0 cres foffres_3 foffres_0 cres foffres_1 cof co ioffres_0 foffres_2 foffres_0 cres cdm foffres_3 foffres_0 cres cdm cin ioffres_0 sup_set_class foffres_2 foffres_0 cres cfv ioffres_0 sup_set_class foffres_3 foffres_0 cres cfv foffres_1 co cmpt wceq foffres_3 foffres_5 wcel foffres_2 foffres_0 foffres_4 resexg foffres_3 foffres_0 foffres_5 resexg ioffres_0 foffres_1 foffres_2 foffres_0 cres foffres_3 foffres_0 cres cvv cvv offval3 syl2an 3eqtr4a $.
$}
$( The function operation produces a function.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v T $.
	$v U $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v z $.
	$d z A $.
	$d z C $.
	$d y z G $.
	$d x y z ph $.
	$d x y S $.
	$d x y T $.
	$d x y z F $.
	$d x y z R $.
	$d x y z U $.
	ioff_0 $f set z $.
	foff_0 $f wff ph $.
	foff_1 $f set x $.
	foff_2 $f set y $.
	foff_3 $f class A $.
	foff_4 $f class B $.
	foff_5 $f class C $.
	foff_6 $f class R $.
	foff_7 $f class S $.
	foff_8 $f class T $.
	foff_9 $f class U $.
	foff_10 $f class F $.
	foff_11 $f class G $.
	foff_12 $f class V $.
	foff_13 $f class W $.
	eoff_0 $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
	eoff_1 $e |- ( ph -> F : A --> S ) $.
	eoff_2 $e |- ( ph -> G : B --> T ) $.
	eoff_3 $e |- ( ph -> A e. V ) $.
	eoff_4 $e |- ( ph -> B e. W ) $.
	eoff_5 $e |- ( A i^i B ) = C $.
	off $p |- ( ph -> ( F oF R G ) : C --> U ) $= foff_0 foff_5 foff_9 foff_10 foff_11 foff_6 cof co wf foff_5 foff_9 ioff_0 foff_5 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co cmpt wf foff_0 ioff_0 foff_5 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co foff_9 ioff_0 foff_5 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co cmpt foff_0 ioff_0 sup_set_class foff_5 wcel wa ioff_0 sup_set_class foff_10 cfv foff_7 wcel ioff_0 sup_set_class foff_11 cfv foff_8 wcel foff_1 sup_set_class foff_2 sup_set_class foff_6 co foff_9 wcel foff_2 foff_8 wral foff_1 foff_7 wral ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co foff_9 wcel foff_0 foff_3 foff_7 foff_10 wf ioff_0 sup_set_class foff_3 wcel ioff_0 sup_set_class foff_10 cfv foff_7 wcel ioff_0 sup_set_class foff_5 wcel eoff_1 foff_5 foff_3 ioff_0 sup_set_class foff_5 foff_3 foff_4 cin foff_3 eoff_5 foff_3 foff_4 inss1 eqsstr3i sseli foff_3 foff_7 ioff_0 sup_set_class foff_10 ffvelrn syl2an foff_0 foff_4 foff_8 foff_11 wf ioff_0 sup_set_class foff_4 wcel ioff_0 sup_set_class foff_11 cfv foff_8 wcel ioff_0 sup_set_class foff_5 wcel eoff_2 foff_5 foff_4 ioff_0 sup_set_class foff_5 foff_3 foff_4 cin foff_4 eoff_5 foff_3 foff_4 inss2 eqsstr3i sseli foff_4 foff_8 ioff_0 sup_set_class foff_11 ffvelrn syl2an foff_0 foff_1 sup_set_class foff_2 sup_set_class foff_6 co foff_9 wcel foff_2 foff_8 wral foff_1 foff_7 wral ioff_0 sup_set_class foff_5 wcel foff_0 foff_1 sup_set_class foff_2 sup_set_class foff_6 co foff_9 wcel foff_1 foff_2 foff_7 foff_8 eoff_0 ralrimivva adantr foff_1 sup_set_class foff_2 sup_set_class foff_6 co foff_9 wcel ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co foff_9 wcel ioff_0 sup_set_class foff_10 cfv foff_2 sup_set_class foff_6 co foff_9 wcel foff_1 foff_2 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_7 foff_8 foff_1 sup_set_class ioff_0 sup_set_class foff_10 cfv wceq foff_1 sup_set_class foff_2 sup_set_class foff_6 co ioff_0 sup_set_class foff_10 cfv foff_2 sup_set_class foff_6 co foff_9 foff_1 sup_set_class ioff_0 sup_set_class foff_10 cfv foff_2 sup_set_class foff_6 oveq1 eleq1d foff_2 sup_set_class ioff_0 sup_set_class foff_11 cfv wceq ioff_0 sup_set_class foff_10 cfv foff_2 sup_set_class foff_6 co ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co foff_9 foff_2 sup_set_class ioff_0 sup_set_class foff_11 cfv ioff_0 sup_set_class foff_10 cfv foff_6 oveq2 eleq1d rspc2va syl21anc ioff_0 foff_5 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co cmpt eqid fmptd foff_0 foff_5 foff_9 foff_10 foff_11 foff_6 cof co ioff_0 foff_5 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 co cmpt foff_0 ioff_0 foff_3 foff_4 ioff_0 sup_set_class foff_10 cfv ioff_0 sup_set_class foff_11 cfv foff_6 foff_5 foff_10 foff_11 foff_12 foff_13 foff_0 foff_3 foff_7 foff_10 wf foff_10 foff_3 wfn eoff_1 foff_3 foff_7 foff_10 ffn syl foff_0 foff_4 foff_8 foff_11 wf foff_11 foff_4 wfn eoff_2 foff_4 foff_8 foff_11 ffn syl eoff_3 eoff_4 eoff_5 foff_0 ioff_0 sup_set_class foff_3 wcel wa ioff_0 sup_set_class foff_10 cfv eqidd foff_0 ioff_0 sup_set_class foff_4 wcel wa ioff_0 sup_set_class foff_11 cfv eqidd offval feq1d mpbird $.
$}
$( Restrict the operands of a function operation to the same domain as that
       of the operation itself.  (Contributed by Mario Carneiro,
       15-Sep-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v x $.
	$d x A $.
	$d x C $.
	$d x F $.
	$d x G $.
	$d x ph $.
	$d x R $.
	iofres_0 $f set x $.
	fofres_0 $f wff ph $.
	fofres_1 $f class A $.
	fofres_2 $f class B $.
	fofres_3 $f class C $.
	fofres_4 $f class R $.
	fofres_5 $f class F $.
	fofres_6 $f class G $.
	fofres_7 $f class V $.
	fofres_8 $f class W $.
	eofres_0 $e |- ( ph -> F Fn A ) $.
	eofres_1 $e |- ( ph -> G Fn B ) $.
	eofres_2 $e |- ( ph -> A e. V ) $.
	eofres_3 $e |- ( ph -> B e. W ) $.
	eofres_4 $e |- ( A i^i B ) = C $.
	ofres $p |- ( ph -> ( F oF R G ) = ( ( F |` C ) oF R ( G |` C ) ) ) $= fofres_0 fofres_5 fofres_6 fofres_4 cof co iofres_0 fofres_3 iofres_0 sup_set_class fofres_5 cfv iofres_0 sup_set_class fofres_6 cfv fofres_4 co cmpt fofres_5 fofres_3 cres fofres_6 fofres_3 cres fofres_4 cof co fofres_0 iofres_0 fofres_1 fofres_2 iofres_0 sup_set_class fofres_5 cfv iofres_0 sup_set_class fofres_6 cfv fofres_4 fofres_3 fofres_5 fofres_6 fofres_7 fofres_8 eofres_0 eofres_1 eofres_2 eofres_3 eofres_4 fofres_0 iofres_0 sup_set_class fofres_1 wcel wa iofres_0 sup_set_class fofres_5 cfv eqidd fofres_0 iofres_0 sup_set_class fofres_2 wcel wa iofres_0 sup_set_class fofres_6 cfv eqidd offval fofres_0 iofres_0 fofres_3 fofres_3 iofres_0 sup_set_class fofres_5 cfv iofres_0 sup_set_class fofres_6 cfv fofres_4 fofres_3 fofres_5 fofres_3 cres fofres_6 fofres_3 cres cvv cvv fofres_0 fofres_5 fofres_1 wfn fofres_3 fofres_1 wss fofres_5 fofres_3 cres fofres_3 wfn eofres_0 fofres_3 fofres_1 fofres_2 cin fofres_1 eofres_4 fofres_1 fofres_2 inss1 eqsstr3i fofres_1 fofres_3 fofres_5 fnssres sylancl fofres_0 fofres_6 fofres_2 wfn fofres_3 fofres_2 wss fofres_6 fofres_3 cres fofres_3 wfn eofres_1 fofres_3 fofres_1 fofres_2 cin fofres_2 eofres_4 fofres_1 fofres_2 inss2 eqsstr3i fofres_2 fofres_3 fofres_6 fnssres sylancl fofres_0 fofres_3 fofres_1 wss fofres_1 fofres_7 wcel fofres_3 cvv wcel fofres_3 fofres_1 fofres_2 cin fofres_1 eofres_4 fofres_1 fofres_2 inss1 eqsstr3i eofres_2 fofres_3 fofres_1 fofres_7 ssexg sylancr fofres_0 fofres_3 fofres_1 wss fofres_1 fofres_7 wcel fofres_3 cvv wcel fofres_3 fofres_1 fofres_2 cin fofres_1 eofres_4 fofres_1 fofres_2 inss1 eqsstr3i eofres_2 fofres_3 fofres_1 fofres_7 ssexg sylancr fofres_3 inidm iofres_0 sup_set_class fofres_3 wcel iofres_0 sup_set_class fofres_5 fofres_3 cres cfv iofres_0 sup_set_class fofres_5 cfv wceq fofres_0 iofres_0 sup_set_class fofres_3 fofres_5 fvres adantl iofres_0 sup_set_class fofres_3 wcel iofres_0 sup_set_class fofres_6 fofres_3 cres cfv iofres_0 sup_set_class fofres_6 cfv wceq fofres_0 iofres_0 sup_set_class fofres_3 fofres_6 fvres adantl offval eqtr4d $.
$}
$( The function operation expressed as a mapping.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v X $.
	$v y $.
	$d x y A $.
	$d y B $.
	$d y C $.
	$d y F $.
	$d y G $.
	$d x y ph $.
	$d x y R $.
	ioffval2_0 $f set y $.
	foffval2_0 $f wff ph $.
	foffval2_1 $f set x $.
	foffval2_2 $f class A $.
	foffval2_3 $f class B $.
	foffval2_4 $f class C $.
	foffval2_5 $f class R $.
	foffval2_6 $f class F $.
	foffval2_7 $f class G $.
	foffval2_8 $f class V $.
	foffval2_9 $f class W $.
	foffval2_10 $f class X $.
	eoffval2_0 $e |- ( ph -> A e. V ) $.
	eoffval2_1 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
	eoffval2_2 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
	eoffval2_3 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
	eoffval2_4 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
	offval2 $p |- ( ph -> ( F oF R G ) = ( x e. A |-> ( B R C ) ) ) $= foffval2_0 foffval2_6 foffval2_7 foffval2_5 cof co ioffval2_0 foffval2_2 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co cmpt foffval2_1 foffval2_2 foffval2_3 foffval2_4 foffval2_5 co cmpt foffval2_0 ioffval2_0 foffval2_2 foffval2_2 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 foffval2_2 foffval2_6 foffval2_7 foffval2_8 foffval2_8 foffval2_0 foffval2_6 foffval2_2 wfn foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_2 wfn foffval2_0 foffval2_3 foffval2_9 wcel foffval2_1 foffval2_2 wral foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_2 wfn foffval2_0 foffval2_3 foffval2_9 wcel foffval2_1 foffval2_2 eoffval2_1 ralrimiva foffval2_1 foffval2_2 foffval2_3 foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_9 foffval2_1 foffval2_2 foffval2_3 cmpt eqid fnmpt syl foffval2_0 foffval2_2 foffval2_6 foffval2_1 foffval2_2 foffval2_3 cmpt eoffval2_3 fneq1d mpbird foffval2_0 foffval2_7 foffval2_2 wfn foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_2 wfn foffval2_0 foffval2_4 foffval2_10 wcel foffval2_1 foffval2_2 wral foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_2 wfn foffval2_0 foffval2_4 foffval2_10 wcel foffval2_1 foffval2_2 eoffval2_2 ralrimiva foffval2_1 foffval2_2 foffval2_4 foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_10 foffval2_1 foffval2_2 foffval2_4 cmpt eqid fnmpt syl foffval2_0 foffval2_2 foffval2_7 foffval2_1 foffval2_2 foffval2_4 cmpt eoffval2_4 fneq1d mpbird eoffval2_0 eoffval2_0 foffval2_2 inidm foffval2_0 ioffval2_0 sup_set_class foffval2_2 wcel wa ioffval2_0 sup_set_class foffval2_6 foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_0 foffval2_6 foffval2_1 foffval2_2 foffval2_3 cmpt wceq ioffval2_0 sup_set_class foffval2_2 wcel eoffval2_3 adantr fveq1d foffval2_0 ioffval2_0 sup_set_class foffval2_2 wcel wa ioffval2_0 sup_set_class foffval2_7 foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_0 foffval2_7 foffval2_1 foffval2_2 foffval2_4 cmpt wceq ioffval2_0 sup_set_class foffval2_2 wcel eoffval2_4 adantr fveq1d offval foffval2_0 ioffval2_0 foffval2_2 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co cmpt foffval2_1 foffval2_2 foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co cmpt foffval2_1 foffval2_2 foffval2_3 foffval2_4 foffval2_5 co cmpt ioffval2_0 foffval2_1 foffval2_2 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co foffval2_1 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 foffval2_1 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_1 foffval2_2 foffval2_3 nfmpt1 foffval2_1 ioffval2_0 sup_set_class nfcv nffv foffval2_1 foffval2_5 nfcv foffval2_1 ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_1 foffval2_2 foffval2_4 nfmpt1 foffval2_1 ioffval2_0 sup_set_class nfcv nffv nfov ioffval2_0 foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co nfcv ioffval2_0 sup_set_class foffval2_1 sup_set_class wceq ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv ioffval2_0 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 ioffval2_0 sup_set_class foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt fveq2 ioffval2_0 sup_set_class foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt fveq2 oveq12d cbvmpt foffval2_0 foffval2_1 foffval2_2 foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_5 co foffval2_3 foffval2_4 foffval2_5 co foffval2_0 foffval2_1 sup_set_class foffval2_2 wcel wa foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_3 foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_4 foffval2_5 foffval2_0 foffval2_1 sup_set_class foffval2_2 wcel wa foffval2_1 sup_set_class foffval2_2 wcel foffval2_3 foffval2_9 wcel foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_3 cmpt cfv foffval2_3 wceq foffval2_0 foffval2_1 sup_set_class foffval2_2 wcel simpr eoffval2_1 foffval2_1 foffval2_2 foffval2_3 foffval2_9 foffval2_1 foffval2_2 foffval2_3 cmpt foffval2_1 foffval2_2 foffval2_3 cmpt eqid fvmpt2 syl2anc foffval2_0 foffval2_1 sup_set_class foffval2_2 wcel wa foffval2_1 sup_set_class foffval2_2 wcel foffval2_4 foffval2_10 wcel foffval2_1 sup_set_class foffval2_1 foffval2_2 foffval2_4 cmpt cfv foffval2_4 wceq foffval2_0 foffval2_1 sup_set_class foffval2_2 wcel simpr eoffval2_2 foffval2_1 foffval2_2 foffval2_4 foffval2_10 foffval2_1 foffval2_2 foffval2_4 cmpt foffval2_1 foffval2_2 foffval2_4 cmpt eqid fvmpt2 syl2anc oveq12d mpteq2dva syl5eq eqtrd $.
$}
$( The function relation acting on maps.  (Contributed by Mario Carneiro,
       20-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v G $.
	$v V $.
	$v W $.
	$v X $.
	$v y $.
	$d x y A $.
	$d y B $.
	$d y C $.
	$d y F $.
	$d y G $.
	$d x y ph $.
	$d x y R $.
	iofrfval2_0 $f set y $.
	fofrfval2_0 $f wff ph $.
	fofrfval2_1 $f set x $.
	fofrfval2_2 $f class A $.
	fofrfval2_3 $f class B $.
	fofrfval2_4 $f class C $.
	fofrfval2_5 $f class R $.
	fofrfval2_6 $f class F $.
	fofrfval2_7 $f class G $.
	fofrfval2_8 $f class V $.
	fofrfval2_9 $f class W $.
	fofrfval2_10 $f class X $.
	eofrfval2_0 $e |- ( ph -> A e. V ) $.
	eofrfval2_1 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
	eofrfval2_2 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
	eofrfval2_3 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
	eofrfval2_4 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
	ofrfval2 $p |- ( ph -> ( F oR R G <-> A. x e. A B R C ) ) $= fofrfval2_0 fofrfval2_6 fofrfval2_7 fofrfval2_5 cofr wbr iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr iofrfval2_0 fofrfval2_2 wral fofrfval2_3 fofrfval2_4 fofrfval2_5 wbr fofrfval2_1 fofrfval2_2 wral fofrfval2_0 iofrfval2_0 fofrfval2_2 fofrfval2_2 iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 fofrfval2_2 fofrfval2_6 fofrfval2_7 fofrfval2_8 fofrfval2_8 fofrfval2_0 fofrfval2_6 fofrfval2_2 wfn fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_2 wfn fofrfval2_0 fofrfval2_3 fofrfval2_9 wcel fofrfval2_1 fofrfval2_2 wral fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_2 wfn fofrfval2_0 fofrfval2_3 fofrfval2_9 wcel fofrfval2_1 fofrfval2_2 eofrfval2_1 ralrimiva fofrfval2_1 fofrfval2_2 fofrfval2_3 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_9 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt eqid fnmpt syl fofrfval2_0 fofrfval2_2 fofrfval2_6 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt eofrfval2_3 fneq1d mpbird fofrfval2_0 fofrfval2_7 fofrfval2_2 wfn fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_2 wfn fofrfval2_0 fofrfval2_4 fofrfval2_10 wcel fofrfval2_1 fofrfval2_2 wral fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_2 wfn fofrfval2_0 fofrfval2_4 fofrfval2_10 wcel fofrfval2_1 fofrfval2_2 eofrfval2_2 ralrimiva fofrfval2_1 fofrfval2_2 fofrfval2_4 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_10 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt eqid fnmpt syl fofrfval2_0 fofrfval2_2 fofrfval2_7 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt eofrfval2_4 fneq1d mpbird eofrfval2_0 eofrfval2_0 fofrfval2_2 inidm fofrfval2_0 iofrfval2_0 sup_set_class fofrfval2_2 wcel wa iofrfval2_0 sup_set_class fofrfval2_6 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_0 fofrfval2_6 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt wceq iofrfval2_0 sup_set_class fofrfval2_2 wcel eofrfval2_3 adantr fveq1d fofrfval2_0 iofrfval2_0 sup_set_class fofrfval2_2 wcel wa iofrfval2_0 sup_set_class fofrfval2_7 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_0 fofrfval2_7 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt wceq iofrfval2_0 sup_set_class fofrfval2_2 wcel eofrfval2_4 adantr fveq1d ofrfval iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr iofrfval2_0 fofrfval2_2 wral fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr fofrfval2_1 fofrfval2_2 wral fofrfval2_0 fofrfval2_3 fofrfval2_4 fofrfval2_5 wbr fofrfval2_1 fofrfval2_2 wral iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr iofrfval2_0 fofrfval2_1 fofrfval2_2 fofrfval2_1 iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 fofrfval2_1 iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_1 fofrfval2_2 fofrfval2_3 nfmpt1 fofrfval2_1 iofrfval2_0 sup_set_class nfcv nffv fofrfval2_1 fofrfval2_5 nfcv fofrfval2_1 iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_1 fofrfval2_2 fofrfval2_4 nfmpt1 fofrfval2_1 iofrfval2_0 sup_set_class nfcv nffv nfbr fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr iofrfval2_0 nfv iofrfval2_0 sup_set_class fofrfval2_1 sup_set_class wceq iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv iofrfval2_0 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 iofrfval2_0 sup_set_class fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fveq2 iofrfval2_0 sup_set_class fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fveq2 breq12d cbvral fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_5 wbr fofrfval2_3 fofrfval2_4 fofrfval2_5 wbr fofrfval2_1 fofrfval2_2 fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_2 wcel wa fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_3 fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_4 fofrfval2_5 fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_2 wcel wa fofrfval2_1 sup_set_class fofrfval2_2 wcel fofrfval2_3 fofrfval2_9 wcel fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt cfv fofrfval2_3 wceq fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_2 wcel simpr eofrfval2_1 fofrfval2_1 fofrfval2_2 fofrfval2_3 fofrfval2_9 fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt fofrfval2_1 fofrfval2_2 fofrfval2_3 cmpt eqid fvmpt2 syl2anc fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_2 wcel wa fofrfval2_1 sup_set_class fofrfval2_2 wcel fofrfval2_4 fofrfval2_10 wcel fofrfval2_1 sup_set_class fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt cfv fofrfval2_4 wceq fofrfval2_0 fofrfval2_1 sup_set_class fofrfval2_2 wcel simpr eofrfval2_2 fofrfval2_1 fofrfval2_2 fofrfval2_4 fofrfval2_10 fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt fofrfval2_1 fofrfval2_2 fofrfval2_4 cmpt eqid fvmpt2 syl2anc breq12d ralbidva syl5bb bitrd $.
$}
$( The composition of a function operation with another function.
       (Contributed by Mario Carneiro, 19-Dec-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v F $.
	$v G $.
	$v H $.
	$v V $.
	$v W $.
	$v X $.
	$v x $.
	$v y $.
	$d y A $.
	$d x y C $.
	$d x y F $.
	$d x y G $.
	$d x y H $.
	$d x y ph $.
	$d x D $.
	$d x y R $.
	iofco_0 $f set x $.
	iofco_1 $f set y $.
	fofco_0 $f wff ph $.
	fofco_1 $f class A $.
	fofco_2 $f class B $.
	fofco_3 $f class C $.
	fofco_4 $f class D $.
	fofco_5 $f class R $.
	fofco_6 $f class F $.
	fofco_7 $f class G $.
	fofco_8 $f class H $.
	fofco_9 $f class V $.
	fofco_10 $f class W $.
	fofco_11 $f class X $.
	eofco_0 $e |- ( ph -> F Fn A ) $.
	eofco_1 $e |- ( ph -> G Fn B ) $.
	eofco_2 $e |- ( ph -> H : D --> C ) $.
	eofco_3 $e |- ( ph -> A e. V ) $.
	eofco_4 $e |- ( ph -> B e. W ) $.
	eofco_5 $e |- ( ph -> D e. X ) $.
	eofco_6 $e |- ( A i^i B ) = C $.
	ofco $p |- ( ph -> ( ( F oF R G ) o. H ) = ( ( F o. H ) oF R ( G o. H ) ) ) $= fofco_0 fofco_6 fofco_7 fofco_5 cof co fofco_8 ccom iofco_0 fofco_4 iofco_0 sup_set_class fofco_8 cfv fofco_6 cfv iofco_0 sup_set_class fofco_8 cfv fofco_7 cfv fofco_5 co cmpt fofco_6 fofco_8 ccom fofco_7 fofco_8 ccom fofco_5 cof co fofco_0 iofco_0 iofco_1 fofco_4 fofco_3 iofco_0 sup_set_class fofco_8 cfv iofco_1 sup_set_class fofco_6 cfv iofco_1 sup_set_class fofco_7 cfv fofco_5 co iofco_0 sup_set_class fofco_8 cfv fofco_6 cfv iofco_0 sup_set_class fofco_8 cfv fofco_7 cfv fofco_5 co fofco_8 fofco_6 fofco_7 fofco_5 cof co fofco_0 fofco_4 fofco_3 fofco_8 wf iofco_0 sup_set_class fofco_4 wcel iofco_0 sup_set_class fofco_8 cfv fofco_3 wcel eofco_2 fofco_4 fofco_3 iofco_0 sup_set_class fofco_8 ffvelrn sylan fofco_0 iofco_0 fofco_4 fofco_3 fofco_8 eofco_2 feqmptd fofco_0 iofco_1 fofco_1 fofco_2 iofco_1 sup_set_class fofco_6 cfv iofco_1 sup_set_class fofco_7 cfv fofco_5 fofco_3 fofco_6 fofco_7 fofco_9 fofco_10 eofco_0 eofco_1 eofco_3 eofco_4 eofco_6 fofco_0 iofco_1 sup_set_class fofco_1 wcel wa iofco_1 sup_set_class fofco_6 cfv eqidd fofco_0 iofco_1 sup_set_class fofco_2 wcel wa iofco_1 sup_set_class fofco_7 cfv eqidd offval iofco_1 sup_set_class iofco_0 sup_set_class fofco_8 cfv wceq iofco_1 sup_set_class fofco_6 cfv iofco_0 sup_set_class fofco_8 cfv fofco_6 cfv iofco_1 sup_set_class fofco_7 cfv iofco_0 sup_set_class fofco_8 cfv fofco_7 cfv fofco_5 iofco_1 sup_set_class iofco_0 sup_set_class fofco_8 cfv fofco_6 fveq2 iofco_1 sup_set_class iofco_0 sup_set_class fofco_8 cfv fofco_7 fveq2 oveq12d fmptco fofco_0 iofco_0 fofco_4 fofco_4 iofco_0 sup_set_class fofco_8 cfv fofco_6 cfv iofco_0 sup_set_class fofco_8 cfv fofco_7 cfv fofco_5 fofco_4 fofco_6 fofco_8 ccom fofco_7 fofco_8 ccom fofco_11 fofco_11 fofco_0 fofco_6 fofco_1 wfn fofco_4 fofco_1 fofco_8 wf fofco_6 fofco_8 ccom fofco_4 wfn eofco_0 fofco_0 fofco_4 fofco_3 fofco_8 wf fofco_3 fofco_1 wss fofco_4 fofco_1 fofco_8 wf eofco_2 fofco_3 fofco_1 fofco_2 cin fofco_1 eofco_6 fofco_1 fofco_2 inss1 eqsstr3i fofco_4 fofco_3 fofco_1 fofco_8 fss sylancl fofco_1 fofco_4 fofco_6 fofco_8 fnfco syl2anc fofco_0 fofco_7 fofco_2 wfn fofco_4 fofco_2 fofco_8 wf fofco_7 fofco_8 ccom fofco_4 wfn eofco_1 fofco_0 fofco_4 fofco_3 fofco_8 wf fofco_3 fofco_2 wss fofco_4 fofco_2 fofco_8 wf eofco_2 fofco_3 fofco_1 fofco_2 cin fofco_2 eofco_6 fofco_1 fofco_2 inss2 eqsstr3i fofco_4 fofco_3 fofco_2 fofco_8 fss sylancl fofco_2 fofco_4 fofco_7 fofco_8 fnfco syl2anc eofco_5 eofco_5 fofco_4 inidm fofco_0 fofco_8 fofco_4 wfn iofco_0 sup_set_class fofco_4 wcel iofco_0 sup_set_class fofco_6 fofco_8 ccom cfv iofco_0 sup_set_class fofco_8 cfv fofco_6 cfv wceq fofco_0 fofco_4 fofco_3 fofco_8 wf fofco_8 fofco_4 wfn eofco_2 fofco_4 fofco_3 fofco_8 ffn syl fofco_4 fofco_6 fofco_8 iofco_0 sup_set_class fvco2 sylan fofco_0 fofco_8 fofco_4 wfn iofco_0 sup_set_class fofco_4 wcel iofco_0 sup_set_class fofco_7 fofco_8 ccom cfv iofco_0 sup_set_class fofco_8 cfv fofco_7 cfv wceq fofco_0 fofco_4 fofco_3 fofco_8 wf fofco_8 fofco_4 wfn eofco_2 fofco_4 fofco_3 fofco_8 ffn syl fofco_4 fofco_7 fofco_8 iofco_0 sup_set_class fvco2 sylan offval eqtr4d $.
$}
$( Convert an identity of the operation to the analogous identity on the
         function operation.  (Contributed by Mario Carneiro, 24-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v G $.
	$v H $.
	$v V $.
	$d x A $.
	$d x F $.
	$d x G $.
	$d x H $.
	$d x ph $.
	$d x R $.
	foffveq_0 $f wff ph $.
	foffveq_1 $f set x $.
	foffveq_2 $f class A $.
	foffveq_3 $f class B $.
	foffveq_4 $f class C $.
	foffveq_5 $f class R $.
	foffveq_6 $f class F $.
	foffveq_7 $f class G $.
	foffveq_8 $f class H $.
	foffveq_9 $f class V $.
	eoffveq_0 $e |- ( ph -> A e. V ) $.
	eoffveq_1 $e |- ( ph -> F Fn A ) $.
	eoffveq_2 $e |- ( ph -> G Fn A ) $.
	eoffveq_3 $e |- ( ph -> H Fn A ) $.
	eoffveq_4 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
	eoffveq_5 $e |- ( ( ph /\ x e. A ) -> ( G ` x ) = C ) $.
	eoffveq_6 $e |- ( ( ph /\ x e. A ) -> ( B R C ) = ( H ` x ) ) $.
	offveq $p |- ( ph -> ( F oF R G ) = H ) $= foffveq_0 foffveq_1 foffveq_2 foffveq_6 foffveq_7 foffveq_5 cof co foffveq_8 foffveq_0 foffveq_2 foffveq_2 foffveq_5 foffveq_2 foffveq_6 foffveq_7 foffveq_9 foffveq_9 eoffveq_1 eoffveq_2 eoffveq_0 eoffveq_0 foffveq_2 inidm offn eoffveq_3 foffveq_0 foffveq_1 sup_set_class foffveq_2 wcel wa foffveq_1 sup_set_class foffveq_6 foffveq_7 foffveq_5 cof co cfv foffveq_3 foffveq_4 foffveq_5 co foffveq_1 sup_set_class foffveq_8 cfv foffveq_0 foffveq_2 foffveq_2 foffveq_3 foffveq_4 foffveq_5 foffveq_2 foffveq_6 foffveq_7 foffveq_9 foffveq_9 foffveq_1 sup_set_class eoffveq_1 eoffveq_2 eoffveq_0 eoffveq_0 foffveq_2 inidm eoffveq_4 eoffveq_5 ofval eoffveq_6 eqtrd eqfnfvd $.
$}
$( Equivalent expressions for equality with a function operation.
       (Contributed by NM, 9-Oct-2014.)  (Proof shortened by Mario Carneiro,
       5-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v G $.
	$v H $.
	$v V $.
	$d x A $.
	$d x F $.
	$d x G $.
	$d x H $.
	$d x ph $.
	$d x R $.
	$d x F $.
	foffveqb_0 $f wff ph $.
	foffveqb_1 $f set x $.
	foffveqb_2 $f class A $.
	foffveqb_3 $f class B $.
	foffveqb_4 $f class C $.
	foffveqb_5 $f class R $.
	foffveqb_6 $f class F $.
	foffveqb_7 $f class G $.
	foffveqb_8 $f class H $.
	foffveqb_9 $f class V $.
	eoffveqb_0 $e |- ( ph -> A e. V ) $.
	eoffveqb_1 $e |- ( ph -> F Fn A ) $.
	eoffveqb_2 $e |- ( ph -> G Fn A ) $.
	eoffveqb_3 $e |- ( ph -> H Fn A ) $.
	eoffveqb_4 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
	eoffveqb_5 $e |- ( ( ph /\ x e. A ) -> ( G ` x ) = C ) $.
	offveqb $p |- ( ph -> ( H = ( F oF R G ) <-> A. x e. A ( H ` x ) = ( B R C ) ) ) $= foffveqb_0 foffveqb_8 foffveqb_6 foffveqb_7 foffveqb_5 cof co wceq foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv cmpt foffveqb_1 foffveqb_2 foffveqb_3 foffveqb_4 foffveqb_5 co cmpt wceq foffveqb_1 sup_set_class foffveqb_8 cfv foffveqb_3 foffveqb_4 foffveqb_5 co wceq foffveqb_1 foffveqb_2 wral foffveqb_0 foffveqb_8 foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv cmpt foffveqb_6 foffveqb_7 foffveqb_5 cof co foffveqb_1 foffveqb_2 foffveqb_3 foffveqb_4 foffveqb_5 co cmpt foffveqb_0 foffveqb_8 foffveqb_2 wfn foffveqb_8 foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv cmpt wceq eoffveqb_3 foffveqb_1 foffveqb_2 foffveqb_8 dffn5 sylib foffveqb_0 foffveqb_1 foffveqb_2 foffveqb_2 foffveqb_3 foffveqb_4 foffveqb_5 foffveqb_2 foffveqb_6 foffveqb_7 foffveqb_9 foffveqb_9 eoffveqb_1 eoffveqb_2 eoffveqb_0 eoffveqb_0 foffveqb_2 inidm eoffveqb_4 eoffveqb_5 offval eqeq12d foffveqb_0 foffveqb_1 sup_set_class foffveqb_8 cfv cvv wcel foffveqb_1 foffveqb_2 wral foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv cmpt foffveqb_1 foffveqb_2 foffveqb_3 foffveqb_4 foffveqb_5 co cmpt wceq foffveqb_1 sup_set_class foffveqb_8 cfv foffveqb_3 foffveqb_4 foffveqb_5 co wceq foffveqb_1 foffveqb_2 wral wb foffveqb_0 foffveqb_1 sup_set_class foffveqb_8 cfv cvv wcel foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv cvv wcel foffveqb_0 foffveqb_1 sup_set_class foffveqb_8 fvex a1i ralrimivw foffveqb_1 foffveqb_2 foffveqb_1 sup_set_class foffveqb_8 cfv foffveqb_3 foffveqb_4 foffveqb_5 co cvv mpteqb syl bitrd $.
$}
$( Left operation by a constant.  (Contributed by Mario Carneiro,
       24-Jul-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v V $.
	$v W $.
	$v X $.
	fofc1_0 $f wff ph $.
	fofc1_1 $f class A $.
	fofc1_2 $f class B $.
	fofc1_3 $f class C $.
	fofc1_4 $f class R $.
	fofc1_5 $f class F $.
	fofc1_6 $f class V $.
	fofc1_7 $f class W $.
	fofc1_8 $f class X $.
	eofc1_0 $e |- ( ph -> A e. V ) $.
	eofc1_1 $e |- ( ph -> B e. W ) $.
	eofc1_2 $e |- ( ph -> F Fn A ) $.
	eofc1_3 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	ofc1 $p |- ( ( ph /\ X e. A ) -> ( ( ( A X. { B } ) oF R F ) ` X ) = ( B R C ) ) $= fofc1_0 fofc1_1 fofc1_1 fofc1_2 fofc1_3 fofc1_4 fofc1_1 fofc1_1 fofc1_2 csn cxp fofc1_5 fofc1_6 fofc1_6 fofc1_8 fofc1_0 fofc1_2 fofc1_7 wcel fofc1_1 fofc1_2 csn cxp fofc1_1 wfn eofc1_1 fofc1_1 fofc1_2 fofc1_7 fnconstg syl eofc1_2 eofc1_0 eofc1_0 fofc1_1 inidm fofc1_0 fofc1_2 fofc1_7 wcel fofc1_8 fofc1_1 wcel fofc1_8 fofc1_1 fofc1_2 csn cxp cfv fofc1_2 wceq eofc1_1 fofc1_1 fofc1_2 fofc1_8 fofc1_7 fvconst2g sylan eofc1_3 ofval $.
$}
$( Right operation by a constant.  (Contributed by NM, 7-Oct-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v F $.
	$v V $.
	$v W $.
	$v X $.
	fofc2_0 $f wff ph $.
	fofc2_1 $f class A $.
	fofc2_2 $f class B $.
	fofc2_3 $f class C $.
	fofc2_4 $f class R $.
	fofc2_5 $f class F $.
	fofc2_6 $f class V $.
	fofc2_7 $f class W $.
	fofc2_8 $f class X $.
	eofc2_0 $e |- ( ph -> A e. V ) $.
	eofc2_1 $e |- ( ph -> B e. W ) $.
	eofc2_2 $e |- ( ph -> F Fn A ) $.
	eofc2_3 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
	ofc2 $p |- ( ( ph /\ X e. A ) -> ( ( F oF R ( A X. { B } ) ) ` X ) = ( C R B ) ) $= fofc2_0 fofc2_1 fofc2_1 fofc2_3 fofc2_2 fofc2_4 fofc2_1 fofc2_5 fofc2_1 fofc2_2 csn cxp fofc2_6 fofc2_6 fofc2_8 eofc2_2 fofc2_0 fofc2_2 fofc2_7 wcel fofc2_1 fofc2_2 csn cxp fofc2_1 wfn eofc2_1 fofc2_1 fofc2_2 fofc2_7 fnconstg syl eofc2_0 eofc2_0 fofc2_1 inidm eofc2_3 fofc2_0 fofc2_2 fofc2_7 wcel fofc2_8 fofc2_1 wcel fofc2_8 fofc2_1 fofc2_2 csn cxp cfv fofc2_2 wceq eofc2_1 fofc2_1 fofc2_2 fofc2_8 fofc2_7 fvconst2g sylan ofval $.
$}
$( Function operation on two constant functions.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v V $.
	$v W $.
	$v X $.
	$v x $.
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ph $.
	$d x R $.
	$d x W $.
	$d x X $.
	iofc12_0 $f set x $.
	fofc12_0 $f wff ph $.
	fofc12_1 $f class A $.
	fofc12_2 $f class B $.
	fofc12_3 $f class C $.
	fofc12_4 $f class R $.
	fofc12_5 $f class V $.
	fofc12_6 $f class W $.
	fofc12_7 $f class X $.
	eofc12_0 $e |- ( ph -> A e. V ) $.
	eofc12_1 $e |- ( ph -> B e. W ) $.
	eofc12_2 $e |- ( ph -> C e. X ) $.
	ofc12 $p |- ( ph -> ( ( A X. { B } ) oF R ( A X. { C } ) ) = ( A X. { ( B R C ) } ) ) $= fofc12_0 fofc12_1 fofc12_2 csn cxp fofc12_1 fofc12_3 csn cxp fofc12_4 cof co iofc12_0 fofc12_1 fofc12_2 fofc12_3 fofc12_4 co cmpt fofc12_1 fofc12_2 fofc12_3 fofc12_4 co csn cxp fofc12_0 iofc12_0 fofc12_1 fofc12_2 fofc12_3 fofc12_4 fofc12_1 fofc12_2 csn cxp fofc12_1 fofc12_3 csn cxp fofc12_5 fofc12_6 fofc12_7 eofc12_0 fofc12_0 fofc12_2 fofc12_6 wcel iofc12_0 sup_set_class fofc12_1 wcel eofc12_1 adantr fofc12_0 fofc12_3 fofc12_7 wcel iofc12_0 sup_set_class fofc12_1 wcel eofc12_2 adantr fofc12_1 fofc12_2 csn cxp iofc12_0 fofc12_1 fofc12_2 cmpt wceq fofc12_0 iofc12_0 fofc12_1 fofc12_2 fconstmpt a1i fofc12_1 fofc12_3 csn cxp iofc12_0 fofc12_1 fofc12_3 cmpt wceq fofc12_0 iofc12_0 fofc12_1 fofc12_3 fconstmpt a1i offval2 iofc12_0 fofc12_1 fofc12_2 fofc12_3 fofc12_4 co fconstmpt syl6eqr $.
$}
$( Transfer a reflexive law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v R $.
	$v S $.
	$v F $.
	$v V $.
	$v w $.
	$d w x $.
	$d w x $.
	$d w x F $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	icaofref_0 $f set w $.
	fcaofref_0 $f wff ph $.
	fcaofref_1 $f set x $.
	fcaofref_2 $f class A $.
	fcaofref_3 $f class R $.
	fcaofref_4 $f class S $.
	fcaofref_5 $f class F $.
	fcaofref_6 $f class V $.
	ecaofref_0 $e |- ( ph -> A e. V ) $.
	ecaofref_1 $e |- ( ph -> F : A --> S ) $.
	ecaofref_2 $e |- ( ( ph /\ x e. S ) -> x R x ) $.
	caofref $p |- ( ph -> F oR R F ) $= fcaofref_0 fcaofref_5 fcaofref_5 fcaofref_3 cofr wbr icaofref_0 sup_set_class fcaofref_5 cfv icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 wbr icaofref_0 fcaofref_2 wral fcaofref_0 icaofref_0 sup_set_class fcaofref_5 cfv icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 wbr icaofref_0 fcaofref_2 fcaofref_0 icaofref_0 sup_set_class fcaofref_2 wcel wa icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_4 wcel fcaofref_1 sup_set_class fcaofref_1 sup_set_class fcaofref_3 wbr fcaofref_1 fcaofref_4 wral icaofref_0 sup_set_class fcaofref_5 cfv icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 wbr fcaofref_0 fcaofref_2 fcaofref_4 fcaofref_5 wf icaofref_0 sup_set_class fcaofref_2 wcel icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_4 wcel ecaofref_1 fcaofref_2 fcaofref_4 icaofref_0 sup_set_class fcaofref_5 ffvelrn sylan fcaofref_0 fcaofref_1 sup_set_class fcaofref_1 sup_set_class fcaofref_3 wbr fcaofref_1 fcaofref_4 wral icaofref_0 sup_set_class fcaofref_2 wcel fcaofref_0 fcaofref_1 sup_set_class fcaofref_1 sup_set_class fcaofref_3 wbr fcaofref_1 fcaofref_4 ecaofref_2 ralrimiva adantr fcaofref_1 sup_set_class fcaofref_1 sup_set_class fcaofref_3 wbr icaofref_0 sup_set_class fcaofref_5 cfv icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 wbr fcaofref_1 icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_4 fcaofref_1 sup_set_class icaofref_0 sup_set_class fcaofref_5 cfv wceq fcaofref_1 sup_set_class icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_1 sup_set_class icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 fcaofref_1 sup_set_class icaofref_0 sup_set_class fcaofref_5 cfv wceq id fcaofref_1 sup_set_class icaofref_0 sup_set_class fcaofref_5 cfv wceq id breq12d rspcv sylc ralrimiva fcaofref_0 icaofref_0 fcaofref_2 fcaofref_2 icaofref_0 sup_set_class fcaofref_5 cfv icaofref_0 sup_set_class fcaofref_5 cfv fcaofref_3 fcaofref_2 fcaofref_5 fcaofref_5 fcaofref_6 fcaofref_6 fcaofref_0 fcaofref_2 fcaofref_4 fcaofref_5 wf fcaofref_5 fcaofref_2 wfn ecaofref_1 fcaofref_2 fcaofref_4 fcaofref_5 ffn syl fcaofref_0 fcaofref_2 fcaofref_4 fcaofref_5 wf fcaofref_5 fcaofref_2 wfn ecaofref_1 fcaofref_2 fcaofref_4 fcaofref_5 ffn syl ecaofref_0 ecaofref_0 fcaofref_2 inidm fcaofref_0 icaofref_0 sup_set_class fcaofref_2 wcel wa icaofref_0 sup_set_class fcaofref_5 cfv eqidd fcaofref_0 icaofref_0 sup_set_class fcaofref_2 wcel wa icaofref_0 sup_set_class fcaofref_5 cfv eqidd ofrfval mpbird $.
$}
$( Transfer a left inverse law to the function operation.  (Contributed
           by NM, 22-Oct-2014.) $)
${
	$v ph $.
	$v x $.
	$v v $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v N $.
	$v V $.
	$v W $.
	$v w $.
	$d w x B $.
	$d w x $.
	$d w x F $.
	$d w x G $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	$d v A $.
	$d v F $.
	$d x v N $.
	$d v S $.
	$d v ph $.
	$d v w $.
	icaofinvl_0 $f set w $.
	fcaofinvl_0 $f wff ph $.
	fcaofinvl_1 $f set x $.
	fcaofinvl_2 $f set v $.
	fcaofinvl_3 $f class A $.
	fcaofinvl_4 $f class B $.
	fcaofinvl_5 $f class R $.
	fcaofinvl_6 $f class S $.
	fcaofinvl_7 $f class F $.
	fcaofinvl_8 $f class G $.
	fcaofinvl_9 $f class N $.
	fcaofinvl_10 $f class V $.
	fcaofinvl_11 $f class W $.
	ecaofinvl_0 $e |- ( ph -> A e. V ) $.
	ecaofinvl_1 $e |- ( ph -> F : A --> S ) $.
	ecaofinvl_2 $e |- ( ph -> B e. W ) $.
	ecaofinvl_3 $e |- ( ph -> N : S --> S ) $.
	ecaofinvl_4 $e |- ( ph -> G = ( v e. A |-> ( N ` ( F ` v ) ) ) ) $.
	ecaofinvl_5 $e |- ( ( ph /\ x e. S ) -> ( ( N ` x ) R x ) = B ) $.
	caofinvl $p |- ( ph -> ( G oF R F ) = ( A X. { B } ) ) $= fcaofinvl_0 fcaofinvl_8 fcaofinvl_7 fcaofinvl_5 cof co icaofinvl_0 fcaofinvl_3 fcaofinvl_4 cmpt fcaofinvl_3 fcaofinvl_4 csn cxp fcaofinvl_0 fcaofinvl_8 fcaofinvl_7 fcaofinvl_5 cof co icaofinvl_0 fcaofinvl_3 icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co cmpt icaofinvl_0 fcaofinvl_3 fcaofinvl_4 cmpt fcaofinvl_0 icaofinvl_0 fcaofinvl_3 icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 fcaofinvl_8 fcaofinvl_7 fcaofinvl_10 fcaofinvl_6 fcaofinvl_6 ecaofinvl_0 fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_8 wf icaofinvl_0 sup_set_class fcaofinvl_3 wcel icaofinvl_0 sup_set_class fcaofinvl_8 cfv fcaofinvl_6 wcel fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_8 wf fcaofinvl_3 fcaofinvl_6 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt wf fcaofinvl_0 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_6 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt fcaofinvl_0 fcaofinvl_2 sup_set_class fcaofinvl_3 wcel wa fcaofinvl_6 fcaofinvl_6 fcaofinvl_9 wf fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 wcel fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_6 wcel fcaofinvl_0 fcaofinvl_6 fcaofinvl_6 fcaofinvl_9 wf fcaofinvl_2 sup_set_class fcaofinvl_3 wcel ecaofinvl_3 adantr fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_7 wf fcaofinvl_2 sup_set_class fcaofinvl_3 wcel fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 wcel ecaofinvl_1 fcaofinvl_3 fcaofinvl_6 fcaofinvl_2 sup_set_class fcaofinvl_7 ffvelrn sylan fcaofinvl_6 fcaofinvl_6 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 ffvelrn syl2anc fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt eqid fmptd fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_8 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt ecaofinvl_4 feq1d mpbird fcaofinvl_3 fcaofinvl_6 icaofinvl_0 sup_set_class fcaofinvl_8 ffvelrn sylan fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_7 wf icaofinvl_0 sup_set_class fcaofinvl_3 wcel icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 wcel ecaofinvl_1 fcaofinvl_3 fcaofinvl_6 icaofinvl_0 sup_set_class fcaofinvl_7 ffvelrn sylan fcaofinvl_0 fcaofinvl_8 fcaofinvl_3 wfn fcaofinvl_8 icaofinvl_0 fcaofinvl_3 icaofinvl_0 sup_set_class fcaofinvl_8 cfv cmpt wceq fcaofinvl_0 fcaofinvl_8 fcaofinvl_3 wfn fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt fcaofinvl_3 wfn fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 fvex fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt eqid fnmpti fcaofinvl_0 fcaofinvl_3 fcaofinvl_8 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt ecaofinvl_4 fneq1d mpbiri icaofinvl_0 fcaofinvl_3 fcaofinvl_8 dffn5 sylib fcaofinvl_0 icaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_7 ecaofinvl_1 feqmptd offval2 fcaofinvl_0 icaofinvl_0 fcaofinvl_3 icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co fcaofinvl_4 fcaofinvl_0 icaofinvl_0 sup_set_class fcaofinvl_3 wcel wa icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co fcaofinvl_4 fcaofinvl_0 icaofinvl_0 sup_set_class fcaofinvl_3 wcel wa icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 fcaofinvl_0 icaofinvl_0 sup_set_class fcaofinvl_3 wcel icaofinvl_0 sup_set_class fcaofinvl_8 cfv icaofinvl_0 sup_set_class fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_0 icaofinvl_0 sup_set_class fcaofinvl_8 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt ecaofinvl_4 fveq1d fcaofinvl_2 icaofinvl_0 sup_set_class fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_3 fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt fcaofinvl_2 sup_set_class icaofinvl_0 sup_set_class wceq fcaofinvl_2 sup_set_class fcaofinvl_7 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 fcaofinvl_2 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 fveq2 fveq2d fcaofinvl_2 fcaofinvl_3 fcaofinvl_2 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv cmpt eqid icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 fvex fvmpt sylan9eq oveq1d fcaofinvl_0 icaofinvl_0 sup_set_class fcaofinvl_3 wcel wa icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 wcel fcaofinvl_1 sup_set_class fcaofinvl_9 cfv fcaofinvl_1 sup_set_class fcaofinvl_5 co fcaofinvl_4 wceq fcaofinvl_1 fcaofinvl_6 wral icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co fcaofinvl_4 wceq fcaofinvl_0 fcaofinvl_3 fcaofinvl_6 fcaofinvl_7 wf icaofinvl_0 sup_set_class fcaofinvl_3 wcel icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 wcel ecaofinvl_1 fcaofinvl_3 fcaofinvl_6 icaofinvl_0 sup_set_class fcaofinvl_7 ffvelrn sylan fcaofinvl_0 fcaofinvl_1 sup_set_class fcaofinvl_9 cfv fcaofinvl_1 sup_set_class fcaofinvl_5 co fcaofinvl_4 wceq fcaofinvl_1 fcaofinvl_6 wral icaofinvl_0 sup_set_class fcaofinvl_3 wcel fcaofinvl_0 fcaofinvl_1 sup_set_class fcaofinvl_9 cfv fcaofinvl_1 sup_set_class fcaofinvl_5 co fcaofinvl_4 wceq fcaofinvl_1 fcaofinvl_6 ecaofinvl_5 ralrimiva adantr fcaofinvl_1 sup_set_class fcaofinvl_9 cfv fcaofinvl_1 sup_set_class fcaofinvl_5 co fcaofinvl_4 wceq icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co fcaofinvl_4 wceq fcaofinvl_1 icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_6 fcaofinvl_1 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 cfv wceq fcaofinvl_1 sup_set_class fcaofinvl_9 cfv fcaofinvl_1 sup_set_class fcaofinvl_5 co icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 co fcaofinvl_4 fcaofinvl_1 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 cfv wceq fcaofinvl_1 sup_set_class fcaofinvl_9 cfv icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 cfv fcaofinvl_1 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_5 fcaofinvl_1 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 cfv fcaofinvl_9 fveq2 fcaofinvl_1 sup_set_class icaofinvl_0 sup_set_class fcaofinvl_7 cfv wceq id oveq12d eqeq1d rspcva syl2anc eqtrd mpteq2dva eqtrd icaofinvl_0 fcaofinvl_3 fcaofinvl_4 fconstmpt syl6eqr $.
$}
$( Transfer a left identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v F $.
	$v V $.
	$v W $.
	$v w $.
	$d w x B $.
	$d w x $.
	$d w x F $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	icaofid0l_0 $f set w $.
	fcaofid0l_0 $f wff ph $.
	fcaofid0l_1 $f set x $.
	fcaofid0l_2 $f class A $.
	fcaofid0l_3 $f class B $.
	fcaofid0l_4 $f class R $.
	fcaofid0l_5 $f class S $.
	fcaofid0l_6 $f class F $.
	fcaofid0l_7 $f class V $.
	fcaofid0l_8 $f class W $.
	ecaofid0l_0 $e |- ( ph -> A e. V ) $.
	ecaofid0l_1 $e |- ( ph -> F : A --> S ) $.
	ecaofid0l_2 $e |- ( ph -> B e. W ) $.
	ecaofid0l_3 $e |- ( ( ph /\ x e. S ) -> ( B R x ) = x ) $.
	caofid0l $p |- ( ph -> ( ( A X. { B } ) oF R F ) = F ) $= fcaofid0l_0 icaofid0l_0 fcaofid0l_2 fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_4 fcaofid0l_2 fcaofid0l_3 csn cxp fcaofid0l_6 fcaofid0l_6 fcaofid0l_7 ecaofid0l_0 fcaofid0l_0 fcaofid0l_3 fcaofid0l_8 wcel fcaofid0l_2 fcaofid0l_3 csn cxp fcaofid0l_2 wfn ecaofid0l_2 fcaofid0l_2 fcaofid0l_3 fcaofid0l_8 fnconstg syl fcaofid0l_0 fcaofid0l_2 fcaofid0l_5 fcaofid0l_6 wf fcaofid0l_6 fcaofid0l_2 wfn ecaofid0l_1 fcaofid0l_2 fcaofid0l_5 fcaofid0l_6 ffn syl fcaofid0l_0 fcaofid0l_2 fcaofid0l_5 fcaofid0l_6 wf fcaofid0l_6 fcaofid0l_2 wfn ecaofid0l_1 fcaofid0l_2 fcaofid0l_5 fcaofid0l_6 ffn syl fcaofid0l_0 fcaofid0l_3 fcaofid0l_8 wcel icaofid0l_0 sup_set_class fcaofid0l_2 wcel icaofid0l_0 sup_set_class fcaofid0l_2 fcaofid0l_3 csn cxp cfv fcaofid0l_3 wceq ecaofid0l_2 fcaofid0l_2 fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_8 fvconst2g sylan fcaofid0l_0 icaofid0l_0 sup_set_class fcaofid0l_2 wcel wa icaofid0l_0 sup_set_class fcaofid0l_6 cfv eqidd fcaofid0l_0 icaofid0l_0 sup_set_class fcaofid0l_2 wcel icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_5 wcel fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_4 co icaofid0l_0 sup_set_class fcaofid0l_6 cfv wceq fcaofid0l_0 fcaofid0l_2 fcaofid0l_5 fcaofid0l_6 wf icaofid0l_0 sup_set_class fcaofid0l_2 wcel icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_5 wcel ecaofid0l_1 fcaofid0l_2 fcaofid0l_5 icaofid0l_0 sup_set_class fcaofid0l_6 ffvelrn sylan fcaofid0l_0 fcaofid0l_3 fcaofid0l_1 sup_set_class fcaofid0l_4 co fcaofid0l_1 sup_set_class wceq fcaofid0l_1 fcaofid0l_5 wral icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_5 wcel fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_4 co icaofid0l_0 sup_set_class fcaofid0l_6 cfv wceq fcaofid0l_0 fcaofid0l_3 fcaofid0l_1 sup_set_class fcaofid0l_4 co fcaofid0l_1 sup_set_class wceq fcaofid0l_1 fcaofid0l_5 ecaofid0l_3 ralrimiva fcaofid0l_3 fcaofid0l_1 sup_set_class fcaofid0l_4 co fcaofid0l_1 sup_set_class wceq fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_4 co icaofid0l_0 sup_set_class fcaofid0l_6 cfv wceq fcaofid0l_1 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_5 fcaofid0l_1 sup_set_class icaofid0l_0 sup_set_class fcaofid0l_6 cfv wceq fcaofid0l_3 fcaofid0l_1 sup_set_class fcaofid0l_4 co fcaofid0l_3 icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_4 co fcaofid0l_1 sup_set_class icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_1 sup_set_class icaofid0l_0 sup_set_class fcaofid0l_6 cfv fcaofid0l_3 fcaofid0l_4 oveq2 fcaofid0l_1 sup_set_class icaofid0l_0 sup_set_class fcaofid0l_6 cfv wceq id eqeq12d rspccva sylan syldan offveq $.
$}
$( Transfer a right identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	$v F $.
	$v V $.
	$v W $.
	$v w $.
	$d w x B $.
	$d w x $.
	$d w x F $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	icaofid0r_0 $f set w $.
	fcaofid0r_0 $f wff ph $.
	fcaofid0r_1 $f set x $.
	fcaofid0r_2 $f class A $.
	fcaofid0r_3 $f class B $.
	fcaofid0r_4 $f class R $.
	fcaofid0r_5 $f class S $.
	fcaofid0r_6 $f class F $.
	fcaofid0r_7 $f class V $.
	fcaofid0r_8 $f class W $.
	ecaofid0r_0 $e |- ( ph -> A e. V ) $.
	ecaofid0r_1 $e |- ( ph -> F : A --> S ) $.
	ecaofid0r_2 $e |- ( ph -> B e. W ) $.
	ecaofid0r_3 $e |- ( ( ph /\ x e. S ) -> ( x R B ) = x ) $.
	caofid0r $p |- ( ph -> ( F oF R ( A X. { B } ) ) = F ) $= fcaofid0r_0 icaofid0r_0 fcaofid0r_2 icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 fcaofid0r_6 fcaofid0r_2 fcaofid0r_3 csn cxp fcaofid0r_6 fcaofid0r_7 ecaofid0r_0 fcaofid0r_0 fcaofid0r_2 fcaofid0r_5 fcaofid0r_6 wf fcaofid0r_6 fcaofid0r_2 wfn ecaofid0r_1 fcaofid0r_2 fcaofid0r_5 fcaofid0r_6 ffn syl fcaofid0r_0 fcaofid0r_3 fcaofid0r_8 wcel fcaofid0r_2 fcaofid0r_3 csn cxp fcaofid0r_2 wfn ecaofid0r_2 fcaofid0r_2 fcaofid0r_3 fcaofid0r_8 fnconstg syl fcaofid0r_0 fcaofid0r_2 fcaofid0r_5 fcaofid0r_6 wf fcaofid0r_6 fcaofid0r_2 wfn ecaofid0r_1 fcaofid0r_2 fcaofid0r_5 fcaofid0r_6 ffn syl fcaofid0r_0 icaofid0r_0 sup_set_class fcaofid0r_2 wcel wa icaofid0r_0 sup_set_class fcaofid0r_6 cfv eqidd fcaofid0r_0 fcaofid0r_3 fcaofid0r_8 wcel icaofid0r_0 sup_set_class fcaofid0r_2 wcel icaofid0r_0 sup_set_class fcaofid0r_2 fcaofid0r_3 csn cxp cfv fcaofid0r_3 wceq ecaofid0r_2 fcaofid0r_2 fcaofid0r_3 icaofid0r_0 sup_set_class fcaofid0r_8 fvconst2g sylan fcaofid0r_0 icaofid0r_0 sup_set_class fcaofid0r_2 wcel icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_5 wcel icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 co icaofid0r_0 sup_set_class fcaofid0r_6 cfv wceq fcaofid0r_0 fcaofid0r_2 fcaofid0r_5 fcaofid0r_6 wf icaofid0r_0 sup_set_class fcaofid0r_2 wcel icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_5 wcel ecaofid0r_1 fcaofid0r_2 fcaofid0r_5 icaofid0r_0 sup_set_class fcaofid0r_6 ffvelrn sylan fcaofid0r_0 fcaofid0r_1 sup_set_class fcaofid0r_3 fcaofid0r_4 co fcaofid0r_1 sup_set_class wceq fcaofid0r_1 fcaofid0r_5 wral icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_5 wcel icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 co icaofid0r_0 sup_set_class fcaofid0r_6 cfv wceq fcaofid0r_0 fcaofid0r_1 sup_set_class fcaofid0r_3 fcaofid0r_4 co fcaofid0r_1 sup_set_class wceq fcaofid0r_1 fcaofid0r_5 ecaofid0r_3 ralrimiva fcaofid0r_1 sup_set_class fcaofid0r_3 fcaofid0r_4 co fcaofid0r_1 sup_set_class wceq icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 co icaofid0r_0 sup_set_class fcaofid0r_6 cfv wceq fcaofid0r_1 icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_5 fcaofid0r_1 sup_set_class icaofid0r_0 sup_set_class fcaofid0r_6 cfv wceq fcaofid0r_1 sup_set_class fcaofid0r_3 fcaofid0r_4 co icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 co fcaofid0r_1 sup_set_class icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_1 sup_set_class icaofid0r_0 sup_set_class fcaofid0r_6 cfv fcaofid0r_3 fcaofid0r_4 oveq1 fcaofid0r_1 sup_set_class icaofid0r_0 sup_set_class fcaofid0r_6 cfv wceq id eqeq12d rspccva sylan syldan offveq $.
$}
$( Transfer a right absorption law to the function operation.
           (Contributed by Mario Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v F $.
	$v V $.
	$v W $.
	$v X $.
	$v w $.
	$d w x B $.
	$d w x C $.
	$d w x F $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	icaofid1_0 $f set w $.
	fcaofid1_0 $f wff ph $.
	fcaofid1_1 $f set x $.
	fcaofid1_2 $f class A $.
	fcaofid1_3 $f class B $.
	fcaofid1_4 $f class C $.
	fcaofid1_5 $f class R $.
	fcaofid1_6 $f class S $.
	fcaofid1_7 $f class F $.
	fcaofid1_8 $f class V $.
	fcaofid1_9 $f class W $.
	fcaofid1_10 $f class X $.
	ecaofid1_0 $e |- ( ph -> A e. V ) $.
	ecaofid1_1 $e |- ( ph -> F : A --> S ) $.
	ecaofid1_2 $e |- ( ph -> B e. W ) $.
	ecaofid1_3 $e |- ( ph -> C e. X ) $.
	ecaofid1_4 $e |- ( ( ph /\ x e. S ) -> ( x R B ) = C ) $.
	caofid1 $p |- ( ph -> ( F oF R ( A X. { B } ) ) = ( A X. { C } ) ) $= fcaofid1_0 icaofid1_0 fcaofid1_2 icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 fcaofid1_7 fcaofid1_2 fcaofid1_3 csn cxp fcaofid1_2 fcaofid1_4 csn cxp fcaofid1_8 ecaofid1_0 fcaofid1_0 fcaofid1_2 fcaofid1_6 fcaofid1_7 wf fcaofid1_7 fcaofid1_2 wfn ecaofid1_1 fcaofid1_2 fcaofid1_6 fcaofid1_7 ffn syl fcaofid1_0 fcaofid1_3 fcaofid1_9 wcel fcaofid1_2 fcaofid1_3 csn cxp fcaofid1_2 wfn ecaofid1_2 fcaofid1_2 fcaofid1_3 fcaofid1_9 fnconstg syl fcaofid1_0 fcaofid1_4 fcaofid1_10 wcel fcaofid1_2 fcaofid1_4 csn cxp fcaofid1_2 wfn ecaofid1_3 fcaofid1_2 fcaofid1_4 fcaofid1_10 fnconstg syl fcaofid1_0 icaofid1_0 sup_set_class fcaofid1_2 wcel wa icaofid1_0 sup_set_class fcaofid1_7 cfv eqidd fcaofid1_0 fcaofid1_3 fcaofid1_9 wcel icaofid1_0 sup_set_class fcaofid1_2 wcel icaofid1_0 sup_set_class fcaofid1_2 fcaofid1_3 csn cxp cfv fcaofid1_3 wceq ecaofid1_2 fcaofid1_2 fcaofid1_3 icaofid1_0 sup_set_class fcaofid1_9 fvconst2g sylan fcaofid1_0 icaofid1_0 sup_set_class fcaofid1_2 wcel wa icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 co fcaofid1_4 icaofid1_0 sup_set_class fcaofid1_2 fcaofid1_4 csn cxp cfv fcaofid1_0 icaofid1_0 sup_set_class fcaofid1_2 wcel icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_6 wcel icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq fcaofid1_0 fcaofid1_2 fcaofid1_6 fcaofid1_7 wf icaofid1_0 sup_set_class fcaofid1_2 wcel icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_6 wcel ecaofid1_1 fcaofid1_2 fcaofid1_6 icaofid1_0 sup_set_class fcaofid1_7 ffvelrn sylan fcaofid1_0 fcaofid1_1 sup_set_class fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq fcaofid1_1 fcaofid1_6 wral icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_6 wcel icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq fcaofid1_0 fcaofid1_1 sup_set_class fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq fcaofid1_1 fcaofid1_6 ecaofid1_4 ralrimiva fcaofid1_1 sup_set_class fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 co fcaofid1_4 wceq fcaofid1_1 icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_6 fcaofid1_1 sup_set_class icaofid1_0 sup_set_class fcaofid1_7 cfv wceq fcaofid1_1 sup_set_class fcaofid1_3 fcaofid1_5 co icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 co fcaofid1_4 fcaofid1_1 sup_set_class icaofid1_0 sup_set_class fcaofid1_7 cfv fcaofid1_3 fcaofid1_5 oveq1 eqeq1d rspccva sylan syldan fcaofid1_0 fcaofid1_4 fcaofid1_10 wcel icaofid1_0 sup_set_class fcaofid1_2 wcel icaofid1_0 sup_set_class fcaofid1_2 fcaofid1_4 csn cxp cfv fcaofid1_4 wceq ecaofid1_3 fcaofid1_2 fcaofid1_4 icaofid1_0 sup_set_class fcaofid1_10 fvconst2g sylan eqtr4d offveq $.
$}
$( Transfer a right absorption law to the function operation.
         (Contributed by Mario Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	$v S $.
	$v F $.
	$v V $.
	$v W $.
	$v X $.
	$v w $.
	$d w x B $.
	$d w x C $.
	$d w x F $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x $.
	$d w x ph $.
	$d w x R $.
	$d w A $.
	$d w x S $.
	$d w x $.
	$d w x $.
	icaofid2_0 $f set w $.
	fcaofid2_0 $f wff ph $.
	fcaofid2_1 $f set x $.
	fcaofid2_2 $f class A $.
	fcaofid2_3 $f class B $.
	fcaofid2_4 $f class C $.
	fcaofid2_5 $f class R $.
	fcaofid2_6 $f class S $.
	fcaofid2_7 $f class F $.
	fcaofid2_8 $f class V $.
	fcaofid2_9 $f class W $.
	fcaofid2_10 $f class X $.
	ecaofid2_0 $e |- ( ph -> A e. V ) $.
	ecaofid2_1 $e |- ( ph -> F : A --> S ) $.
	ecaofid2_2 $e |- ( ph -> B e. W ) $.
	ecaofid2_3 $e |- ( ph -> C e. X ) $.
	ecaofid2_4 $e |- ( ( ph /\ x e. S ) -> ( B R x ) = C ) $.
	caofid2 $p |- ( ph -> ( ( A X. { B } ) oF R F ) = ( A X. { C } ) ) $= fcaofid2_0 icaofid2_0 fcaofid2_2 fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 fcaofid2_2 fcaofid2_3 csn cxp fcaofid2_7 fcaofid2_2 fcaofid2_4 csn cxp fcaofid2_8 ecaofid2_0 fcaofid2_0 fcaofid2_3 fcaofid2_9 wcel fcaofid2_2 fcaofid2_3 csn cxp fcaofid2_2 wfn ecaofid2_2 fcaofid2_2 fcaofid2_3 fcaofid2_9 fnconstg syl fcaofid2_0 fcaofid2_2 fcaofid2_6 fcaofid2_7 wf fcaofid2_7 fcaofid2_2 wfn ecaofid2_1 fcaofid2_2 fcaofid2_6 fcaofid2_7 ffn syl fcaofid2_0 fcaofid2_4 fcaofid2_10 wcel fcaofid2_2 fcaofid2_4 csn cxp fcaofid2_2 wfn ecaofid2_3 fcaofid2_2 fcaofid2_4 fcaofid2_10 fnconstg syl fcaofid2_0 fcaofid2_3 fcaofid2_9 wcel icaofid2_0 sup_set_class fcaofid2_2 wcel icaofid2_0 sup_set_class fcaofid2_2 fcaofid2_3 csn cxp cfv fcaofid2_3 wceq ecaofid2_2 fcaofid2_2 fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_9 fvconst2g sylan fcaofid2_0 icaofid2_0 sup_set_class fcaofid2_2 wcel wa icaofid2_0 sup_set_class fcaofid2_7 cfv eqidd fcaofid2_0 icaofid2_0 sup_set_class fcaofid2_2 wcel wa fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 co fcaofid2_4 icaofid2_0 sup_set_class fcaofid2_2 fcaofid2_4 csn cxp cfv fcaofid2_0 icaofid2_0 sup_set_class fcaofid2_2 wcel icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_6 wcel fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 co fcaofid2_4 wceq fcaofid2_0 fcaofid2_2 fcaofid2_6 fcaofid2_7 wf icaofid2_0 sup_set_class fcaofid2_2 wcel icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_6 wcel ecaofid2_1 fcaofid2_2 fcaofid2_6 icaofid2_0 sup_set_class fcaofid2_7 ffvelrn sylan fcaofid2_0 fcaofid2_3 fcaofid2_1 sup_set_class fcaofid2_5 co fcaofid2_4 wceq fcaofid2_1 fcaofid2_6 wral icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_6 wcel fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 co fcaofid2_4 wceq fcaofid2_0 fcaofid2_3 fcaofid2_1 sup_set_class fcaofid2_5 co fcaofid2_4 wceq fcaofid2_1 fcaofid2_6 ecaofid2_4 ralrimiva fcaofid2_3 fcaofid2_1 sup_set_class fcaofid2_5 co fcaofid2_4 wceq fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 co fcaofid2_4 wceq fcaofid2_1 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_6 fcaofid2_1 sup_set_class icaofid2_0 sup_set_class fcaofid2_7 cfv wceq fcaofid2_3 fcaofid2_1 sup_set_class fcaofid2_5 co fcaofid2_3 icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_5 co fcaofid2_4 fcaofid2_1 sup_set_class icaofid2_0 sup_set_class fcaofid2_7 cfv fcaofid2_3 fcaofid2_5 oveq2 eqeq1d rspccva sylan syldan fcaofid2_0 fcaofid2_4 fcaofid2_10 wcel icaofid2_0 sup_set_class fcaofid2_2 wcel icaofid2_0 sup_set_class fcaofid2_2 fcaofid2_4 csn cxp cfv fcaofid2_4 wceq ecaofid2_3 fcaofid2_2 fcaofid2_4 icaofid2_0 sup_set_class fcaofid2_10 fvconst2g sylan eqtr4d offveq $.
$}
$( Transfer a commutative law to the function operation.  (Contributed by
         Mario Carneiro, 26-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v R $.
	$v S $.
	$v F $.
	$v G $.
	$v V $.
	$v w $.
	$d w x $.
	$d w x $.
	$d w x y F $.
	$d w x y G $.
	$d w x y $.
	$d w x y $.
	$d w x y $.
	$d w x y ph $.
	$d w x y R $.
	$d w A $.
	$d w x y S $.
	$d w x y $.
	$d w x y $.
	icaofcom_0 $f set w $.
	fcaofcom_0 $f wff ph $.
	fcaofcom_1 $f set x $.
	fcaofcom_2 $f set y $.
	fcaofcom_3 $f class A $.
	fcaofcom_4 $f class R $.
	fcaofcom_5 $f class S $.
	fcaofcom_6 $f class F $.
	fcaofcom_7 $f class G $.
	fcaofcom_8 $f class V $.
	ecaofcom_0 $e |- ( ph -> A e. V ) $.
	ecaofcom_1 $e |- ( ph -> F : A --> S ) $.
	ecaofcom_2 $e |- ( ph -> G : A --> S ) $.
	ecaofcom_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y ) = ( y R x ) ) $.
	caofcom $p |- ( ph -> ( F oF R G ) = ( G oF R F ) ) $= fcaofcom_0 icaofcom_0 fcaofcom_3 icaofcom_0 sup_set_class fcaofcom_6 cfv icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_4 co cmpt icaofcom_0 fcaofcom_3 icaofcom_0 sup_set_class fcaofcom_7 cfv icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_4 co cmpt fcaofcom_6 fcaofcom_7 fcaofcom_4 cof co fcaofcom_7 fcaofcom_6 fcaofcom_4 cof co fcaofcom_0 icaofcom_0 fcaofcom_3 icaofcom_0 sup_set_class fcaofcom_6 cfv icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_4 co icaofcom_0 sup_set_class fcaofcom_7 cfv icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_4 co fcaofcom_0 icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_5 wcel icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 wcel wa icaofcom_0 sup_set_class fcaofcom_6 cfv icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_4 co icaofcom_0 sup_set_class fcaofcom_7 cfv icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_4 co wceq fcaofcom_0 icaofcom_0 sup_set_class fcaofcom_3 wcel wa icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_5 wcel icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 wcel fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_6 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_5 wcel ecaofcom_1 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_6 ffvelrn sylan fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_7 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 wcel ecaofcom_2 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_7 ffvelrn sylan jca fcaofcom_0 fcaofcom_1 fcaofcom_2 icaofcom_0 sup_set_class fcaofcom_6 cfv icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 fcaofcom_4 ecaofcom_3 caovcomg syldan mpteq2dva fcaofcom_0 icaofcom_0 fcaofcom_3 icaofcom_0 sup_set_class fcaofcom_6 cfv icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_4 fcaofcom_6 fcaofcom_7 fcaofcom_8 fcaofcom_5 fcaofcom_5 ecaofcom_0 fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_6 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_5 wcel ecaofcom_1 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_6 ffvelrn sylan fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_7 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 wcel ecaofcom_2 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_7 ffvelrn sylan fcaofcom_0 icaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_6 ecaofcom_1 feqmptd fcaofcom_0 icaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_7 ecaofcom_2 feqmptd offval2 fcaofcom_0 icaofcom_0 fcaofcom_3 icaofcom_0 sup_set_class fcaofcom_7 cfv icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_4 fcaofcom_7 fcaofcom_6 fcaofcom_8 fcaofcom_5 fcaofcom_5 ecaofcom_0 fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_7 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_7 cfv fcaofcom_5 wcel ecaofcom_2 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_7 ffvelrn sylan fcaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_6 wf icaofcom_0 sup_set_class fcaofcom_3 wcel icaofcom_0 sup_set_class fcaofcom_6 cfv fcaofcom_5 wcel ecaofcom_1 fcaofcom_3 fcaofcom_5 icaofcom_0 sup_set_class fcaofcom_6 ffvelrn sylan fcaofcom_0 icaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_7 ecaofcom_2 feqmptd fcaofcom_0 icaofcom_0 fcaofcom_3 fcaofcom_5 fcaofcom_6 ecaofcom_1 feqmptd offval2 3eqtr4d $.
$}
$( Transfer a relation subset law to the function relation.  (Contributed
         by Mario Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$v V $.
	$v w $.
	$d w x $.
	$d w x $.
	$d w x y F $.
	$d w x y G $.
	$d w x y $.
	$d w x y $.
	$d w x y $.
	$d w x y ph $.
	$d w x y R $.
	$d w A $.
	$d w x y S $.
	$d w x y T $.
	$d w x y $.
	icaofrss_0 $f set w $.
	fcaofrss_0 $f wff ph $.
	fcaofrss_1 $f set x $.
	fcaofrss_2 $f set y $.
	fcaofrss_3 $f class A $.
	fcaofrss_4 $f class R $.
	fcaofrss_5 $f class S $.
	fcaofrss_6 $f class T $.
	fcaofrss_7 $f class F $.
	fcaofrss_8 $f class G $.
	fcaofrss_9 $f class V $.
	ecaofrss_0 $e |- ( ph -> A e. V ) $.
	ecaofrss_1 $e |- ( ph -> F : A --> S ) $.
	ecaofrss_2 $e |- ( ph -> G : A --> S ) $.
	ecaofrss_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x R y -> x T y ) ) $.
	caofrss $p |- ( ph -> ( F oR R G -> F oR T G ) ) $= fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 wbr icaofrss_0 fcaofrss_3 wral icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 wbr icaofrss_0 fcaofrss_3 wral fcaofrss_7 fcaofrss_8 fcaofrss_4 cofr wbr fcaofrss_7 fcaofrss_8 fcaofrss_6 cofr wbr fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 wbr icaofrss_0 fcaofrss_3 fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_3 wcel wa icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_5 wcel icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_5 wcel fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_4 wbr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_6 wbr wi fcaofrss_2 fcaofrss_5 wral fcaofrss_1 fcaofrss_5 wral icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 wbr wi fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_7 wf icaofrss_0 sup_set_class fcaofrss_3 wcel icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_5 wcel ecaofrss_1 fcaofrss_3 fcaofrss_5 icaofrss_0 sup_set_class fcaofrss_7 ffvelrn sylan fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_8 wf icaofrss_0 sup_set_class fcaofrss_3 wcel icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_5 wcel ecaofrss_2 fcaofrss_3 fcaofrss_5 icaofrss_0 sup_set_class fcaofrss_8 ffvelrn sylan fcaofrss_0 fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_4 wbr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_6 wbr wi fcaofrss_2 fcaofrss_5 wral fcaofrss_1 fcaofrss_5 wral icaofrss_0 sup_set_class fcaofrss_3 wcel fcaofrss_0 fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_4 wbr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_6 wbr wi fcaofrss_1 fcaofrss_2 fcaofrss_5 fcaofrss_5 ecaofrss_3 ralrimivva adantr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_4 wbr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_6 wbr wi icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 wbr wi icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_6 wbr wi fcaofrss_1 fcaofrss_2 icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_5 fcaofrss_5 fcaofrss_1 sup_set_class icaofrss_0 sup_set_class fcaofrss_7 cfv wceq fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_4 wbr fcaofrss_1 sup_set_class fcaofrss_2 sup_set_class fcaofrss_6 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_6 wbr fcaofrss_1 sup_set_class icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_4 breq1 fcaofrss_1 sup_set_class icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_6 breq1 imbi12d fcaofrss_2 sup_set_class icaofrss_0 sup_set_class fcaofrss_8 cfv wceq icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_2 sup_set_class fcaofrss_6 wbr icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 wbr fcaofrss_2 sup_set_class icaofrss_0 sup_set_class fcaofrss_8 cfv icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_4 breq2 fcaofrss_2 sup_set_class icaofrss_0 sup_set_class fcaofrss_8 cfv icaofrss_0 sup_set_class fcaofrss_7 cfv fcaofrss_6 breq2 imbi12d rspc2va syl21anc ralimdva fcaofrss_0 icaofrss_0 fcaofrss_3 fcaofrss_3 icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_4 fcaofrss_3 fcaofrss_7 fcaofrss_8 fcaofrss_9 fcaofrss_9 fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_7 wf fcaofrss_7 fcaofrss_3 wfn ecaofrss_1 fcaofrss_3 fcaofrss_5 fcaofrss_7 ffn syl fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_8 wf fcaofrss_8 fcaofrss_3 wfn ecaofrss_2 fcaofrss_3 fcaofrss_5 fcaofrss_8 ffn syl ecaofrss_0 ecaofrss_0 fcaofrss_3 inidm fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_3 wcel wa icaofrss_0 sup_set_class fcaofrss_7 cfv eqidd fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_3 wcel wa icaofrss_0 sup_set_class fcaofrss_8 cfv eqidd ofrfval fcaofrss_0 icaofrss_0 fcaofrss_3 fcaofrss_3 icaofrss_0 sup_set_class fcaofrss_7 cfv icaofrss_0 sup_set_class fcaofrss_8 cfv fcaofrss_6 fcaofrss_3 fcaofrss_7 fcaofrss_8 fcaofrss_9 fcaofrss_9 fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_7 wf fcaofrss_7 fcaofrss_3 wfn ecaofrss_1 fcaofrss_3 fcaofrss_5 fcaofrss_7 ffn syl fcaofrss_0 fcaofrss_3 fcaofrss_5 fcaofrss_8 wf fcaofrss_8 fcaofrss_3 wfn ecaofrss_2 fcaofrss_3 fcaofrss_5 fcaofrss_8 ffn syl ecaofrss_0 ecaofrss_0 fcaofrss_3 inidm fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_3 wcel wa icaofrss_0 sup_set_class fcaofrss_7 cfv eqidd fcaofrss_0 icaofrss_0 sup_set_class fcaofrss_3 wcel wa icaofrss_0 sup_set_class fcaofrss_8 cfv eqidd ofrfval 3imtr4d $.
$}
$( Transfer an associative law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v P $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$v H $.
	$v O $.
	$v V $.
	$v w $.
	$d w x $.
	$d w x $.
	$d w x y z F $.
	$d w x y z G $.
	$d w x y z H $.
	$d w x y z O $.
	$d w x y z P $.
	$d w x y z ph $.
	$d w x y z R $.
	$d w A $.
	$d w x y z S $.
	$d w x y z T $.
	$d w x y z $.
	icaofass_0 $f set w $.
	fcaofass_0 $f wff ph $.
	fcaofass_1 $f set x $.
	fcaofass_2 $f set y $.
	fcaofass_3 $f set z $.
	fcaofass_4 $f class A $.
	fcaofass_5 $f class P $.
	fcaofass_6 $f class R $.
	fcaofass_7 $f class S $.
	fcaofass_8 $f class T $.
	fcaofass_9 $f class F $.
	fcaofass_10 $f class G $.
	fcaofass_11 $f class H $.
	fcaofass_12 $f class O $.
	fcaofass_13 $f class V $.
	ecaofass_0 $e |- ( ph -> A e. V ) $.
	ecaofass_1 $e |- ( ph -> F : A --> S ) $.
	ecaofass_2 $e |- ( ph -> G : A --> S ) $.
	ecaofass_3 $e |- ( ph -> H : A --> S ) $.
	ecaofass_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y ) T z ) = ( x O ( y P z ) ) ) $.
	caofass $p |- ( ph -> ( ( F oF R G ) oF T H ) = ( F oF O ( G oF P H ) ) ) $= fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co cmpt icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co cmpt fcaofass_9 fcaofass_10 fcaofass_6 cof co fcaofass_11 fcaofass_8 cof co fcaofass_9 fcaofass_10 fcaofass_11 fcaofass_5 cof co fcaofass_12 cof co fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co fcaofass_0 icaofass_0 sup_set_class fcaofass_4 wcel wa fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq fcaofass_3 fcaofass_7 wral fcaofass_2 fcaofass_7 wral fcaofass_1 fcaofass_7 wral icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co wceq fcaofass_0 fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq fcaofass_3 fcaofass_7 wral fcaofass_2 fcaofass_7 wral fcaofass_1 fcaofass_7 wral icaofass_0 sup_set_class fcaofass_4 wcel fcaofass_0 fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq fcaofass_1 fcaofass_2 fcaofass_3 fcaofass_7 fcaofass_7 fcaofass_7 ecaofass_4 ralrimivvva adantr fcaofass_0 icaofass_0 sup_set_class fcaofass_4 wcel wa icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_7 wcel icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_7 wcel icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_7 wcel fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq fcaofass_3 fcaofass_7 wral fcaofass_2 fcaofass_7 wral fcaofass_1 fcaofass_7 wral icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co wceq wi fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_9 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_7 wcel ecaofass_1 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_9 ffvelrn sylan fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_10 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_7 wcel ecaofass_2 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_10 ffvelrn sylan fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_11 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_7 wcel ecaofass_3 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_11 ffvelrn sylan fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co wceq icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co wceq fcaofass_1 fcaofass_2 fcaofass_3 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_7 fcaofass_7 fcaofass_7 fcaofass_1 sup_set_class icaofass_0 sup_set_class fcaofass_9 cfv wceq fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co fcaofass_1 sup_set_class icaofass_0 sup_set_class fcaofass_9 cfv wceq fcaofass_1 sup_set_class fcaofass_2 sup_set_class fcaofass_6 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 fcaofass_1 sup_set_class icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 oveq1 oveq1d fcaofass_1 sup_set_class icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 oveq1 eqeq12d fcaofass_2 sup_set_class icaofass_0 sup_set_class fcaofass_10 cfv wceq icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co fcaofass_2 sup_set_class icaofass_0 sup_set_class fcaofass_10 cfv wceq icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_2 sup_set_class fcaofass_6 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 fcaofass_2 sup_set_class icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_6 oveq2 oveq1d fcaofass_2 sup_set_class icaofass_0 sup_set_class fcaofass_10 cfv wceq fcaofass_2 sup_set_class fcaofass_3 sup_set_class fcaofass_5 co icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_12 fcaofass_2 sup_set_class icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 oveq1 oveq2d eqeq12d fcaofass_3 sup_set_class icaofass_0 sup_set_class fcaofass_11 cfv wceq icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co fcaofass_3 sup_set_class fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 co fcaofass_12 co icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 co fcaofass_3 sup_set_class icaofass_0 sup_set_class fcaofass_11 cfv icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co fcaofass_8 oveq2 fcaofass_3 sup_set_class icaofass_0 sup_set_class fcaofass_11 cfv wceq icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_3 sup_set_class fcaofass_5 co icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_12 fcaofass_3 sup_set_class icaofass_0 sup_set_class fcaofass_11 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_5 oveq2 oveq2d eqeq12d rspc3v syl3anc mpd mpteq2dva fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_8 fcaofass_9 fcaofass_10 fcaofass_6 cof co fcaofass_11 fcaofass_13 cvv fcaofass_7 ecaofass_0 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 co cvv wcel fcaofass_0 icaofass_0 sup_set_class fcaofass_4 wcel wa icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 ovex a1i fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_11 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_7 wcel ecaofass_3 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_11 ffvelrn sylan fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_6 fcaofass_9 fcaofass_10 fcaofass_13 fcaofass_7 fcaofass_7 ecaofass_0 fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_9 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_7 wcel ecaofass_1 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_9 ffvelrn sylan fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_10 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_7 wcel ecaofass_2 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_10 ffvelrn sylan fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_9 ecaofass_1 feqmptd fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_10 ecaofass_2 feqmptd offval2 fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_11 ecaofass_3 feqmptd offval2 fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_9 cfv icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co fcaofass_12 fcaofass_9 fcaofass_10 fcaofass_11 fcaofass_5 cof co fcaofass_13 fcaofass_7 cvv ecaofass_0 fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_9 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_9 cfv fcaofass_7 wcel ecaofass_1 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_9 ffvelrn sylan icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 co cvv wcel fcaofass_0 icaofass_0 sup_set_class fcaofass_4 wcel wa icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 ovex a1i fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_9 ecaofass_1 feqmptd fcaofass_0 icaofass_0 fcaofass_4 icaofass_0 sup_set_class fcaofass_10 cfv icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_5 fcaofass_10 fcaofass_11 fcaofass_13 fcaofass_7 fcaofass_7 ecaofass_0 fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_10 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_10 cfv fcaofass_7 wcel ecaofass_2 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_10 ffvelrn sylan fcaofass_0 fcaofass_4 fcaofass_7 fcaofass_11 wf icaofass_0 sup_set_class fcaofass_4 wcel icaofass_0 sup_set_class fcaofass_11 cfv fcaofass_7 wcel ecaofass_3 fcaofass_4 fcaofass_7 icaofass_0 sup_set_class fcaofass_11 ffvelrn sylan fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_10 ecaofass_2 feqmptd fcaofass_0 icaofass_0 fcaofass_4 fcaofass_7 fcaofass_11 ecaofass_3 feqmptd offval2 offval2 3eqtr4d $.
$}
$( Transfer a transitivity law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v R $.
	$v S $.
	$v T $.
	$v U $.
	$v F $.
	$v G $.
	$v H $.
	$v V $.
	$v w $.
	$d w x $.
	$d w x $.
	$d w x y z F $.
	$d w x y z G $.
	$d w x y z H $.
	$d w x y z $.
	$d w x y z $.
	$d w x y z ph $.
	$d w x y z R $.
	$d w A $.
	$d w x y z S $.
	$d w x y z T $.
	$d w x y z U $.
	icaoftrn_0 $f set w $.
	fcaoftrn_0 $f wff ph $.
	fcaoftrn_1 $f set x $.
	fcaoftrn_2 $f set y $.
	fcaoftrn_3 $f set z $.
	fcaoftrn_4 $f class A $.
	fcaoftrn_5 $f class R $.
	fcaoftrn_6 $f class S $.
	fcaoftrn_7 $f class T $.
	fcaoftrn_8 $f class U $.
	fcaoftrn_9 $f class F $.
	fcaoftrn_10 $f class G $.
	fcaoftrn_11 $f class H $.
	fcaoftrn_12 $f class V $.
	ecaoftrn_0 $e |- ( ph -> A e. V ) $.
	ecaoftrn_1 $e |- ( ph -> F : A --> S ) $.
	ecaoftrn_2 $e |- ( ph -> G : A --> S ) $.
	ecaoftrn_3 $e |- ( ph -> H : A --> S ) $.
	ecaoftrn_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x R y /\ y T z ) -> x U z ) ) $.
	caoftrn $p |- ( ph -> ( ( F oR R G /\ G oR T H ) -> F oR U H ) ) $= fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 fcaoftrn_4 wral icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr icaoftrn_0 fcaoftrn_4 wral fcaoftrn_9 fcaoftrn_10 fcaoftrn_5 cofr wbr fcaoftrn_10 fcaoftrn_11 fcaoftrn_7 cofr wbr wa fcaoftrn_9 fcaoftrn_11 fcaoftrn_8 cofr wbr fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr icaoftrn_0 fcaoftrn_4 fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi fcaoftrn_3 fcaoftrn_6 wral fcaoftrn_2 fcaoftrn_6 wral fcaoftrn_1 fcaoftrn_6 wral icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr wi fcaoftrn_0 fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi fcaoftrn_3 fcaoftrn_6 wral fcaoftrn_2 fcaoftrn_6 wral fcaoftrn_1 fcaoftrn_6 wral icaoftrn_0 sup_set_class fcaoftrn_4 wcel fcaoftrn_0 fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi fcaoftrn_1 fcaoftrn_2 fcaoftrn_3 fcaoftrn_6 fcaoftrn_6 fcaoftrn_6 ecaoftrn_4 ralrimivvva adantr fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_6 wcel icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_6 wcel icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_6 wcel fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi fcaoftrn_3 fcaoftrn_6 wral fcaoftrn_2 fcaoftrn_6 wral fcaoftrn_1 fcaoftrn_6 wral icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr wi wi fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_9 wf icaoftrn_0 sup_set_class fcaoftrn_4 wcel icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_6 wcel ecaoftrn_1 fcaoftrn_4 fcaoftrn_6 icaoftrn_0 sup_set_class fcaoftrn_9 ffvelrn sylan fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_10 wf icaoftrn_0 sup_set_class fcaoftrn_4 wcel icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_6 wcel ecaoftrn_2 fcaoftrn_4 fcaoftrn_6 icaoftrn_0 sup_set_class fcaoftrn_10 ffvelrn sylan fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_11 wf icaoftrn_0 sup_set_class fcaoftrn_4 wcel icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_6 wcel ecaoftrn_3 fcaoftrn_4 fcaoftrn_6 icaoftrn_0 sup_set_class fcaoftrn_11 ffvelrn sylan fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr wi icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 wbr wi fcaoftrn_1 fcaoftrn_2 fcaoftrn_3 icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_6 fcaoftrn_6 fcaoftrn_6 fcaoftrn_1 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_9 cfv wceq fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa fcaoftrn_1 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_8 wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 wbr fcaoftrn_1 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_9 cfv wceq fcaoftrn_1 sup_set_class fcaoftrn_2 sup_set_class fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr fcaoftrn_1 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 breq1 anbi1d fcaoftrn_1 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 breq1 imbi12d fcaoftrn_2 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_10 cfv wceq icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 wbr fcaoftrn_2 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_10 cfv wceq icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_2 sup_set_class fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr fcaoftrn_2 sup_set_class fcaoftrn_3 sup_set_class fcaoftrn_7 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 wbr fcaoftrn_2 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_5 breq2 fcaoftrn_2 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 breq1 anbi12d imbi1d fcaoftrn_3 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_11 cfv wceq icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_3 sup_set_class fcaoftrn_8 wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 wbr fcaoftrn_3 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_11 cfv wceq icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_3 sup_set_class fcaoftrn_7 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr fcaoftrn_3 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_11 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_7 breq2 anbi2d fcaoftrn_3 sup_set_class icaoftrn_0 sup_set_class fcaoftrn_11 cfv icaoftrn_0 sup_set_class fcaoftrn_9 cfv fcaoftrn_8 breq2 imbi12d rspc3v syl3anc mpd ralimdva fcaoftrn_0 fcaoftrn_9 fcaoftrn_10 fcaoftrn_5 cofr wbr fcaoftrn_10 fcaoftrn_11 fcaoftrn_7 cofr wbr wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 fcaoftrn_4 wral icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr icaoftrn_0 fcaoftrn_4 wral wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr wa icaoftrn_0 fcaoftrn_4 wral fcaoftrn_0 fcaoftrn_9 fcaoftrn_10 fcaoftrn_5 cofr wbr icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 fcaoftrn_4 wral fcaoftrn_10 fcaoftrn_11 fcaoftrn_7 cofr wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr icaoftrn_0 fcaoftrn_4 wral fcaoftrn_0 icaoftrn_0 fcaoftrn_4 fcaoftrn_4 icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 fcaoftrn_4 fcaoftrn_9 fcaoftrn_10 fcaoftrn_12 fcaoftrn_12 fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_9 wf fcaoftrn_9 fcaoftrn_4 wfn ecaoftrn_1 fcaoftrn_4 fcaoftrn_6 fcaoftrn_9 ffn syl fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_10 wf fcaoftrn_10 fcaoftrn_4 wfn ecaoftrn_2 fcaoftrn_4 fcaoftrn_6 fcaoftrn_10 ffn syl ecaoftrn_0 ecaoftrn_0 fcaoftrn_4 inidm fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv eqidd fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_10 cfv eqidd ofrfval fcaoftrn_0 icaoftrn_0 fcaoftrn_4 fcaoftrn_4 icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 fcaoftrn_4 fcaoftrn_10 fcaoftrn_11 fcaoftrn_12 fcaoftrn_12 fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_10 wf fcaoftrn_10 fcaoftrn_4 wfn ecaoftrn_2 fcaoftrn_4 fcaoftrn_6 fcaoftrn_10 ffn syl fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_11 wf fcaoftrn_11 fcaoftrn_4 wfn ecaoftrn_3 fcaoftrn_4 fcaoftrn_6 fcaoftrn_11 ffn syl ecaoftrn_0 ecaoftrn_0 fcaoftrn_4 inidm fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_10 cfv eqidd fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_11 cfv eqidd ofrfval anbi12d icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_10 cfv fcaoftrn_5 wbr icaoftrn_0 sup_set_class fcaoftrn_10 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_7 wbr icaoftrn_0 fcaoftrn_4 r19.26 syl6bbr fcaoftrn_0 icaoftrn_0 fcaoftrn_4 fcaoftrn_4 icaoftrn_0 sup_set_class fcaoftrn_9 cfv icaoftrn_0 sup_set_class fcaoftrn_11 cfv fcaoftrn_8 fcaoftrn_4 fcaoftrn_9 fcaoftrn_11 fcaoftrn_12 fcaoftrn_12 fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_9 wf fcaoftrn_9 fcaoftrn_4 wfn ecaoftrn_1 fcaoftrn_4 fcaoftrn_6 fcaoftrn_9 ffn syl fcaoftrn_0 fcaoftrn_4 fcaoftrn_6 fcaoftrn_11 wf fcaoftrn_11 fcaoftrn_4 wfn ecaoftrn_3 fcaoftrn_4 fcaoftrn_6 fcaoftrn_11 ffn syl ecaoftrn_0 ecaoftrn_0 fcaoftrn_4 inidm fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_9 cfv eqidd fcaoftrn_0 icaoftrn_0 sup_set_class fcaoftrn_4 wcel wa icaoftrn_0 sup_set_class fcaoftrn_11 cfv eqidd ofrfval 3imtr4d $.
$}
$( Transfer a distributive law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$v H $.
	$v K $.
	$v O $.
	$v V $.
	$v w $.
	$d w x y z A $.
	$d w x y z F $.
	$d w x y z G $.
	$d w x y z ph $.
	$d w x y z H $.
	$d w x y z K $.
	$d w x y z O $.
	$d w x y z R $.
	$d w x y z S $.
	$d w x y z T $.
	icaofdi_0 $f set w $.
	fcaofdi_0 $f wff ph $.
	fcaofdi_1 $f set x $.
	fcaofdi_2 $f set y $.
	fcaofdi_3 $f set z $.
	fcaofdi_4 $f class A $.
	fcaofdi_5 $f class R $.
	fcaofdi_6 $f class S $.
	fcaofdi_7 $f class T $.
	fcaofdi_8 $f class F $.
	fcaofdi_9 $f class G $.
	fcaofdi_10 $f class H $.
	fcaofdi_11 $f class K $.
	fcaofdi_12 $f class O $.
	fcaofdi_13 $f class V $.
	ecaofdi_0 $e |- ( ph -> A e. V ) $.
	ecaofdi_1 $e |- ( ph -> F : A --> K ) $.
	ecaofdi_2 $e |- ( ph -> G : A --> S ) $.
	ecaofdi_3 $e |- ( ph -> H : A --> S ) $.
	ecaofdi_4 $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x T ( y R z ) ) = ( ( x T y ) O ( x T z ) ) ) $.
	caofdi $p |- ( ph -> ( F oF T ( G oF R H ) ) = ( ( F oF T G ) oF O ( F oF T H ) ) ) $= fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 co fcaofdi_7 co cmpt icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 co icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 co fcaofdi_12 co cmpt fcaofdi_8 fcaofdi_9 fcaofdi_10 fcaofdi_5 cof co fcaofdi_7 cof co fcaofdi_8 fcaofdi_9 fcaofdi_7 cof co fcaofdi_8 fcaofdi_10 fcaofdi_7 cof co fcaofdi_12 cof co fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 co fcaofdi_7 co icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 co icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 co fcaofdi_12 co fcaofdi_0 icaofdi_0 sup_set_class fcaofdi_4 wcel wa fcaofdi_1 fcaofdi_2 fcaofdi_3 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_6 fcaofdi_5 fcaofdi_7 fcaofdi_12 fcaofdi_11 fcaofdi_0 fcaofdi_1 sup_set_class fcaofdi_11 wcel fcaofdi_2 sup_set_class fcaofdi_6 wcel fcaofdi_3 sup_set_class fcaofdi_6 wcel w3a fcaofdi_1 sup_set_class fcaofdi_2 sup_set_class fcaofdi_3 sup_set_class fcaofdi_5 co fcaofdi_7 co fcaofdi_1 sup_set_class fcaofdi_2 sup_set_class fcaofdi_7 co fcaofdi_1 sup_set_class fcaofdi_3 sup_set_class fcaofdi_7 co fcaofdi_12 co wceq icaofdi_0 sup_set_class fcaofdi_4 wcel ecaofdi_4 adantlr fcaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_8 cfv fcaofdi_11 wcel ecaofdi_1 fcaofdi_4 fcaofdi_11 icaofdi_0 sup_set_class fcaofdi_8 ffvelrn sylan fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_9 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_6 wcel ecaofdi_2 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_9 ffvelrn sylan fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_10 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_6 wcel ecaofdi_3 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_10 ffvelrn sylan caovdid mpteq2dva fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 co fcaofdi_7 fcaofdi_8 fcaofdi_9 fcaofdi_10 fcaofdi_5 cof co fcaofdi_13 fcaofdi_11 cvv ecaofdi_0 fcaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_8 cfv fcaofdi_11 wcel ecaofdi_1 fcaofdi_4 fcaofdi_11 icaofdi_0 sup_set_class fcaofdi_8 ffvelrn sylan icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 co cvv wcel fcaofdi_0 icaofdi_0 sup_set_class fcaofdi_4 wcel wa icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 ovex a1i fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 ecaofdi_1 feqmptd fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_9 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_5 fcaofdi_9 fcaofdi_10 fcaofdi_13 fcaofdi_6 fcaofdi_6 ecaofdi_0 fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_9 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_6 wcel ecaofdi_2 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_9 ffvelrn sylan fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_10 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_6 wcel ecaofdi_3 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_10 ffvelrn sylan fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_9 ecaofdi_2 feqmptd fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_10 ecaofdi_3 feqmptd offval2 offval2 fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 co icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 co fcaofdi_12 fcaofdi_8 fcaofdi_9 fcaofdi_7 cof co fcaofdi_8 fcaofdi_10 fcaofdi_7 cof co fcaofdi_13 cvv cvv ecaofdi_0 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 co cvv wcel fcaofdi_0 icaofdi_0 sup_set_class fcaofdi_4 wcel wa icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 ovex a1i icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 co cvv wcel fcaofdi_0 icaofdi_0 sup_set_class fcaofdi_4 wcel wa icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 ovex a1i fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_7 fcaofdi_8 fcaofdi_9 fcaofdi_13 fcaofdi_11 fcaofdi_6 ecaofdi_0 fcaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_8 cfv fcaofdi_11 wcel ecaofdi_1 fcaofdi_4 fcaofdi_11 icaofdi_0 sup_set_class fcaofdi_8 ffvelrn sylan fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_9 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_9 cfv fcaofdi_6 wcel ecaofdi_2 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_9 ffvelrn sylan fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 ecaofdi_1 feqmptd fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_9 ecaofdi_2 feqmptd offval2 fcaofdi_0 icaofdi_0 fcaofdi_4 icaofdi_0 sup_set_class fcaofdi_8 cfv icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_7 fcaofdi_8 fcaofdi_10 fcaofdi_13 fcaofdi_11 fcaofdi_6 ecaofdi_0 fcaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_8 cfv fcaofdi_11 wcel ecaofdi_1 fcaofdi_4 fcaofdi_11 icaofdi_0 sup_set_class fcaofdi_8 ffvelrn sylan fcaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_10 wf icaofdi_0 sup_set_class fcaofdi_4 wcel icaofdi_0 sup_set_class fcaofdi_10 cfv fcaofdi_6 wcel ecaofdi_3 fcaofdi_4 fcaofdi_6 icaofdi_0 sup_set_class fcaofdi_10 ffvelrn sylan fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_11 fcaofdi_8 ecaofdi_1 feqmptd fcaofdi_0 icaofdi_0 fcaofdi_4 fcaofdi_6 fcaofdi_10 ecaofdi_3 feqmptd offval2 offval2 3eqtr4d $.
$}
$( Transfer a reverse distributive law to the function operation.
         (Contributed by NM, 19-Oct-2014.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v R $.
	$v S $.
	$v T $.
	$v F $.
	$v G $.
	$v H $.
	$v K $.
	$v O $.
	$v V $.
	$v w $.
	$d w x y z A $.
	$d w x y z F $.
	$d w x y z G $.
	$d w x y z ph $.
	$d w x y z H $.
	$d w x y z K $.
	$d w x y z O $.
	$d w x y z R $.
	$d w x y z S $.
	$d w x y z T $.
	icaofdir_0 $f set w $.
	fcaofdir_0 $f wff ph $.
	fcaofdir_1 $f set x $.
	fcaofdir_2 $f set y $.
	fcaofdir_3 $f set z $.
	fcaofdir_4 $f class A $.
	fcaofdir_5 $f class R $.
	fcaofdir_6 $f class S $.
	fcaofdir_7 $f class T $.
	fcaofdir_8 $f class F $.
	fcaofdir_9 $f class G $.
	fcaofdir_10 $f class H $.
	fcaofdir_11 $f class K $.
	fcaofdir_12 $f class O $.
	fcaofdir_13 $f class V $.
	ecaofdir_0 $e |- ( ph -> A e. V ) $.
	ecaofdir_1 $e |- ( ph -> F : A --> K ) $.
	ecaofdir_2 $e |- ( ph -> G : A --> S ) $.
	ecaofdir_3 $e |- ( ph -> H : A --> S ) $.
	ecaofdir_4 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x R y ) T z ) = ( ( x T z ) O ( y T z ) ) ) $.
	caofdir $p |- ( ph -> ( ( G oF R H ) oF T F ) = ( ( G oF T F ) oF O ( H oF T F ) ) ) $= fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 co icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co cmpt icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co fcaofdir_12 co cmpt fcaofdir_9 fcaofdir_10 fcaofdir_5 cof co fcaofdir_8 fcaofdir_7 cof co fcaofdir_9 fcaofdir_8 fcaofdir_7 cof co fcaofdir_10 fcaofdir_8 fcaofdir_7 cof co fcaofdir_12 cof co fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 co icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co fcaofdir_12 co fcaofdir_0 icaofdir_0 sup_set_class fcaofdir_4 wcel wa fcaofdir_1 fcaofdir_2 fcaofdir_3 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_6 fcaofdir_5 fcaofdir_7 fcaofdir_12 fcaofdir_11 fcaofdir_0 fcaofdir_1 sup_set_class fcaofdir_6 wcel fcaofdir_2 sup_set_class fcaofdir_6 wcel fcaofdir_3 sup_set_class fcaofdir_11 wcel w3a fcaofdir_1 sup_set_class fcaofdir_2 sup_set_class fcaofdir_5 co fcaofdir_3 sup_set_class fcaofdir_7 co fcaofdir_1 sup_set_class fcaofdir_3 sup_set_class fcaofdir_7 co fcaofdir_2 sup_set_class fcaofdir_3 sup_set_class fcaofdir_7 co fcaofdir_12 co wceq icaofdir_0 sup_set_class fcaofdir_4 wcel ecaofdir_4 adantlr fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_9 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_9 cfv fcaofdir_6 wcel ecaofdir_2 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_9 ffvelrn sylan fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_10 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_6 wcel ecaofdir_3 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_10 ffvelrn sylan fcaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_11 wcel ecaofdir_1 fcaofdir_4 fcaofdir_11 icaofdir_0 sup_set_class fcaofdir_8 ffvelrn sylan caovdird mpteq2dva fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 co icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 fcaofdir_9 fcaofdir_10 fcaofdir_5 cof co fcaofdir_8 fcaofdir_13 cvv fcaofdir_11 ecaofdir_0 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 co cvv wcel fcaofdir_0 icaofdir_0 sup_set_class fcaofdir_4 wcel wa icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 ovex a1i fcaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_11 wcel ecaofdir_1 fcaofdir_4 fcaofdir_11 icaofdir_0 sup_set_class fcaofdir_8 ffvelrn sylan fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_5 fcaofdir_9 fcaofdir_10 fcaofdir_13 fcaofdir_6 fcaofdir_6 ecaofdir_0 fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_9 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_9 cfv fcaofdir_6 wcel ecaofdir_2 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_9 ffvelrn sylan fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_10 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_6 wcel ecaofdir_3 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_10 ffvelrn sylan fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_9 ecaofdir_2 feqmptd fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_10 ecaofdir_3 feqmptd offval2 fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 ecaofdir_1 feqmptd offval2 fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co fcaofdir_12 fcaofdir_9 fcaofdir_8 fcaofdir_7 cof co fcaofdir_10 fcaofdir_8 fcaofdir_7 cof co fcaofdir_13 cvv cvv ecaofdir_0 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co cvv wcel fcaofdir_0 icaofdir_0 sup_set_class fcaofdir_4 wcel wa icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 ovex a1i icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 co cvv wcel fcaofdir_0 icaofdir_0 sup_set_class fcaofdir_4 wcel wa icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 ovex a1i fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_9 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 fcaofdir_9 fcaofdir_8 fcaofdir_13 fcaofdir_6 fcaofdir_11 ecaofdir_0 fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_9 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_9 cfv fcaofdir_6 wcel ecaofdir_2 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_9 ffvelrn sylan fcaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_11 wcel ecaofdir_1 fcaofdir_4 fcaofdir_11 icaofdir_0 sup_set_class fcaofdir_8 ffvelrn sylan fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_9 ecaofdir_2 feqmptd fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 ecaofdir_1 feqmptd offval2 fcaofdir_0 icaofdir_0 fcaofdir_4 icaofdir_0 sup_set_class fcaofdir_10 cfv icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_7 fcaofdir_10 fcaofdir_8 fcaofdir_13 fcaofdir_6 fcaofdir_11 ecaofdir_0 fcaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_10 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_10 cfv fcaofdir_6 wcel ecaofdir_3 fcaofdir_4 fcaofdir_6 icaofdir_0 sup_set_class fcaofdir_10 ffvelrn sylan fcaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 wf icaofdir_0 sup_set_class fcaofdir_4 wcel icaofdir_0 sup_set_class fcaofdir_8 cfv fcaofdir_11 wcel ecaofdir_1 fcaofdir_4 fcaofdir_11 icaofdir_0 sup_set_class fcaofdir_8 ffvelrn sylan fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_6 fcaofdir_10 ecaofdir_3 feqmptd fcaofdir_0 icaofdir_0 fcaofdir_4 fcaofdir_11 fcaofdir_8 ecaofdir_1 feqmptd offval2 offval2 3eqtr4d $.
$}
$( Transfer ~ nncan -shaped laws to vectors of numbers.  (Contributed by
       Stefan O'Rear, 27-Mar-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v S $.
	$v I $.
	$v M $.
	$v V $.
	$v z $.
	$d ph x y z $.
	$d A x y z $.
	$d B y z $.
	$d I z $.
	$d M x y z $.
	$d S x y $.
	icaonncan_0 $f set z $.
	fcaonncan_0 $f wff ph $.
	fcaonncan_1 $f set x $.
	fcaonncan_2 $f set y $.
	fcaonncan_3 $f class A $.
	fcaonncan_4 $f class B $.
	fcaonncan_5 $f class S $.
	fcaonncan_6 $f class I $.
	fcaonncan_7 $f class M $.
	fcaonncan_8 $f class V $.
	ecaonncan_0 $e |- ( ph -> I e. V ) $.
	ecaonncan_1 $e |- ( ph -> A : I --> S ) $.
	ecaonncan_2 $e |- ( ph -> B : I --> S ) $.
	ecaonncan_3 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x M ( x M y ) ) = y ) $.
	caonncan $p |- ( ph -> ( A oF M ( A oF M B ) ) = B ) $= fcaonncan_0 icaonncan_0 fcaonncan_6 icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 co cmpt icaonncan_0 fcaonncan_6 icaonncan_0 sup_set_class fcaonncan_4 cfv cmpt fcaonncan_3 fcaonncan_3 fcaonncan_4 fcaonncan_7 cof co fcaonncan_7 cof co fcaonncan_4 fcaonncan_0 icaonncan_0 fcaonncan_6 icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_0 icaonncan_0 sup_set_class fcaonncan_6 wcel wa icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_5 wcel icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_5 wcel fcaonncan_1 sup_set_class fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class wceq fcaonncan_2 fcaonncan_5 wral fcaonncan_1 fcaonncan_5 wral icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_4 cfv wceq fcaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_3 wf icaonncan_0 sup_set_class fcaonncan_6 wcel icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_5 wcel ecaonncan_1 fcaonncan_6 fcaonncan_5 icaonncan_0 sup_set_class fcaonncan_3 ffvelrn sylan fcaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_4 wf icaonncan_0 sup_set_class fcaonncan_6 wcel icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_5 wcel ecaonncan_2 fcaonncan_6 fcaonncan_5 icaonncan_0 sup_set_class fcaonncan_4 ffvelrn sylan fcaonncan_0 fcaonncan_1 sup_set_class fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class wceq fcaonncan_2 fcaonncan_5 wral fcaonncan_1 fcaonncan_5 wral icaonncan_0 sup_set_class fcaonncan_6 wcel fcaonncan_0 fcaonncan_1 sup_set_class fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class wceq fcaonncan_1 fcaonncan_2 fcaonncan_5 fcaonncan_5 ecaonncan_3 ralrimivva adantr fcaonncan_1 sup_set_class fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class wceq icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_4 cfv wceq icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class wceq fcaonncan_1 fcaonncan_2 icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_5 fcaonncan_5 fcaonncan_1 sup_set_class icaonncan_0 sup_set_class fcaonncan_3 cfv wceq fcaonncan_1 sup_set_class fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class fcaonncan_1 sup_set_class icaonncan_0 sup_set_class fcaonncan_3 cfv wceq fcaonncan_1 sup_set_class icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_1 sup_set_class fcaonncan_2 sup_set_class fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 fcaonncan_1 sup_set_class icaonncan_0 sup_set_class fcaonncan_3 cfv wceq id fcaonncan_1 sup_set_class icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 oveq1 oveq12d eqeq1d fcaonncan_2 sup_set_class icaonncan_0 sup_set_class fcaonncan_4 cfv wceq icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 co fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 co fcaonncan_2 sup_set_class icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_2 sup_set_class icaonncan_0 sup_set_class fcaonncan_4 cfv wceq icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_2 sup_set_class fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_7 fcaonncan_2 sup_set_class icaonncan_0 sup_set_class fcaonncan_4 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv fcaonncan_7 oveq2 oveq2d fcaonncan_2 sup_set_class icaonncan_0 sup_set_class fcaonncan_4 cfv wceq id eqeq12d rspc2va syl21anc mpteq2dva fcaonncan_0 icaonncan_0 fcaonncan_6 icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co fcaonncan_7 fcaonncan_3 fcaonncan_3 fcaonncan_4 fcaonncan_7 cof co fcaonncan_8 cvv cvv ecaonncan_0 icaonncan_0 sup_set_class fcaonncan_3 cfv cvv wcel fcaonncan_0 icaonncan_0 sup_set_class fcaonncan_6 wcel wa icaonncan_0 sup_set_class fcaonncan_3 fvex a1i icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 co cvv wcel fcaonncan_0 icaonncan_0 sup_set_class fcaonncan_6 wcel wa icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 ovex a1i fcaonncan_0 icaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_3 ecaonncan_1 feqmptd fcaonncan_0 icaonncan_0 fcaonncan_6 icaonncan_0 sup_set_class fcaonncan_3 cfv icaonncan_0 sup_set_class fcaonncan_4 cfv fcaonncan_7 fcaonncan_3 fcaonncan_4 fcaonncan_8 cvv cvv ecaonncan_0 icaonncan_0 sup_set_class fcaonncan_3 cfv cvv wcel fcaonncan_0 icaonncan_0 sup_set_class fcaonncan_6 wcel wa icaonncan_0 sup_set_class fcaonncan_3 fvex a1i icaonncan_0 sup_set_class fcaonncan_4 cfv cvv wcel fcaonncan_0 icaonncan_0 sup_set_class fcaonncan_6 wcel wa icaonncan_0 sup_set_class fcaonncan_4 fvex a1i fcaonncan_0 icaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_3 ecaonncan_1 feqmptd fcaonncan_0 icaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_4 ecaonncan_2 feqmptd offval2 offval2 fcaonncan_0 icaonncan_0 fcaonncan_6 fcaonncan_5 fcaonncan_4 ecaonncan_2 feqmptd 3eqtr4d $.
$}
$( Equivalent expressions for a restriction of the function operation map.
       Unlike ` oF R ` which is a proper class, ` ( oF R | `` ( A X. B ) ) `
       can be a set by ~ ofmresex , allowing it to be used as a function or
       structure argument.  By ~ ofmresval , the restricted operation map
       values are the same as the original values, allowing theorems for
       ` oF R ` to be reused.  (Contributed by NM, 20-Oct-2014.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v f $.
	$v g $.
	$v x $.
	$d f g A $.
	$d f g B $.
	$d f g x R $.
	iofmres_0 $f set x $.
	fofmres_0 $f class A $.
	fofmres_1 $f class B $.
	fofmres_2 $f class R $.
	fofmres_3 $f set f $.
	fofmres_4 $f set g $.
	ofmres $p |- ( oF R |` ( A X. B ) ) = ( f e. A , g e. B |-> ( f oF R g ) ) $= fofmres_3 fofmres_4 cvv cvv iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cmpt2 fofmres_0 fofmres_1 cxp cres fofmres_3 fofmres_4 fofmres_0 fofmres_1 iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cmpt2 fofmres_2 cof fofmres_0 fofmres_1 cxp cres fofmres_3 fofmres_4 fofmres_0 fofmres_1 fofmres_3 sup_set_class fofmres_4 sup_set_class fofmres_2 cof co cmpt2 fofmres_0 cvv wss fofmres_1 cvv wss fofmres_3 fofmres_4 cvv cvv iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cmpt2 fofmres_0 fofmres_1 cxp cres fofmres_3 fofmres_4 fofmres_0 fofmres_1 iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cmpt2 wceq fofmres_0 ssv fofmres_1 ssv fofmres_3 fofmres_4 cvv cvv fofmres_0 fofmres_1 iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt resmpt2 mp2an fofmres_2 cof fofmres_3 fofmres_4 cvv cvv iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cmpt2 fofmres_0 fofmres_1 cxp iofmres_0 fofmres_2 fofmres_3 fofmres_4 df-of reseq1i fofmres_3 fofmres_4 fofmres_0 fofmres_1 fofmres_3 sup_set_class fofmres_4 sup_set_class fofmres_2 cof co fofmres_0 fofmres_1 iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt fofmres_0 eqid fofmres_1 eqid fofmres_3 sup_set_class cvv wcel fofmres_4 sup_set_class cvv wcel iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt cvv wcel fofmres_3 sup_set_class fofmres_4 sup_set_class fofmres_2 cof co iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt wceq fofmres_3 vex fofmres_4 vex iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm fofmres_3 sup_set_class fofmres_3 vex dmex inex1 mptex fofmres_3 fofmres_4 cvv cvv iofmres_0 fofmres_3 sup_set_class cdm fofmres_4 sup_set_class cdm cin iofmres_0 sup_set_class fofmres_3 sup_set_class cfv iofmres_0 sup_set_class fofmres_4 sup_set_class cfv fofmres_2 co cmpt fofmres_2 cof cvv iofmres_0 fofmres_2 fofmres_3 fofmres_4 df-of ovmpt4g mp3an mpt2eq123i 3eqtr4i $.
$}
$( Value of a restriction of the function operation map.  (Contributed by
       NM, 20-Oct-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v R $.
	$v F $.
	$v G $.
	fofmresval_0 $f wff ph $.
	fofmresval_1 $f class A $.
	fofmresval_2 $f class B $.
	fofmresval_3 $f class R $.
	fofmresval_4 $f class F $.
	fofmresval_5 $f class G $.
	eofmresval_0 $e |- ( ph -> F e. A ) $.
	eofmresval_1 $e |- ( ph -> G e. B ) $.
	ofmresval $p |- ( ph -> ( F ( oF R |` ( A X. B ) ) G ) = ( F oF R G ) ) $= fofmresval_0 fofmresval_4 fofmresval_1 wcel fofmresval_5 fofmresval_2 wcel fofmresval_4 fofmresval_5 fofmresval_3 cof fofmresval_1 fofmresval_2 cxp cres co fofmresval_4 fofmresval_5 fofmresval_3 cof co wceq eofmresval_0 eofmresval_1 fofmresval_4 fofmresval_5 fofmresval_1 fofmresval_2 fofmresval_3 cof ovres syl2anc $.
$}
$( Existence of a restriction of the function operation map.  (Contributed
       by NM, 20-Oct-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v R $.
	$v V $.
	$v W $.
	fofmresex_0 $f wff ph $.
	fofmresex_1 $f class A $.
	fofmresex_2 $f class B $.
	fofmresex_3 $f class R $.
	fofmresex_4 $f class V $.
	fofmresex_5 $f class W $.
	eofmresex_0 $e |- ( ph -> A e. V ) $.
	eofmresex_1 $e |- ( ph -> B e. W ) $.
	ofmresex $p |- ( ph -> ( oF R |` ( A X. B ) ) e. _V ) $= fofmresex_0 fofmresex_1 fofmresex_2 cxp cvv wcel fofmresex_3 cof fofmresex_1 fofmresex_2 cxp cres cvv wcel fofmresex_0 fofmresex_1 fofmresex_4 wcel fofmresex_2 fofmresex_5 wcel fofmresex_1 fofmresex_2 cxp cvv wcel eofmresex_0 eofmresex_1 fofmresex_1 fofmresex_2 fofmresex_4 fofmresex_5 xpexg syl2anc fofmresex_1 fofmresex_2 cxp fofmresex_3 cvv ofexg syl $.
$}
$( Formula building theorem for support restrictions: vector operation with
       left annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
${
	$v ph $.
	$v v $.
	$v A $.
	$v B $.
	$v D $.
	$v R $.
	$v L $.
	$v O $.
	$v V $.
	$v W $.
	$v Y $.
	$v Z $.
	$v x $.
	$d ph v x $.
	$d A x $.
	$d B v x $.
	$d D x $.
	$d O v x $.
	$d R v $.
	$d Y v x $.
	$d Z v x $.
	isuppssof1_0 $f set x $.
	fsuppssof1_0 $f wff ph $.
	fsuppssof1_1 $f set v $.
	fsuppssof1_2 $f class A $.
	fsuppssof1_3 $f class B $.
	fsuppssof1_4 $f class D $.
	fsuppssof1_5 $f class R $.
	fsuppssof1_6 $f class L $.
	fsuppssof1_7 $f class O $.
	fsuppssof1_8 $f class V $.
	fsuppssof1_9 $f class W $.
	fsuppssof1_10 $f class Y $.
	fsuppssof1_11 $f class Z $.
	esuppssof1_0 $e |- ( ph -> ( `' A " ( _V \ { Y } ) ) C_ L ) $.
	esuppssof1_1 $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
	esuppssof1_2 $e |- ( ph -> A : D --> V ) $.
	esuppssof1_3 $e |- ( ph -> B : D --> R ) $.
	esuppssof1_4 $e |- ( ph -> D e. W ) $.
	suppssof1 $p |- ( ph -> ( `' ( A oF O B ) " ( _V \ { Z } ) ) C_ L ) $= fsuppssof1_0 fsuppssof1_2 fsuppssof1_3 fsuppssof1_7 cof co ccnv cvv fsuppssof1_11 csn cdif cima isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_7 co cmpt ccnv cvv fsuppssof1_11 csn cdif cima fsuppssof1_6 fsuppssof1_0 fsuppssof1_2 fsuppssof1_3 fsuppssof1_7 cof co ccnv isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_7 co cmpt ccnv cvv fsuppssof1_11 csn cdif fsuppssof1_0 fsuppssof1_2 fsuppssof1_3 fsuppssof1_7 cof co isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_7 co cmpt fsuppssof1_0 isuppssof1_0 fsuppssof1_4 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_7 fsuppssof1_4 fsuppssof1_2 fsuppssof1_3 fsuppssof1_9 fsuppssof1_9 fsuppssof1_0 fsuppssof1_4 fsuppssof1_8 fsuppssof1_2 wf fsuppssof1_2 fsuppssof1_4 wfn esuppssof1_2 fsuppssof1_4 fsuppssof1_8 fsuppssof1_2 ffn syl fsuppssof1_0 fsuppssof1_4 fsuppssof1_5 fsuppssof1_3 wf fsuppssof1_3 fsuppssof1_4 wfn esuppssof1_3 fsuppssof1_4 fsuppssof1_5 fsuppssof1_3 ffn syl esuppssof1_4 esuppssof1_4 fsuppssof1_4 inidm fsuppssof1_0 isuppssof1_0 sup_set_class fsuppssof1_4 wcel wa isuppssof1_0 sup_set_class fsuppssof1_2 cfv eqidd fsuppssof1_0 isuppssof1_0 sup_set_class fsuppssof1_4 wcel wa isuppssof1_0 sup_set_class fsuppssof1_3 cfv eqidd offval cnveqd imaeq1d fsuppssof1_0 isuppssof1_0 fsuppssof1_1 isuppssof1_0 sup_set_class fsuppssof1_2 cfv isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_4 fsuppssof1_5 fsuppssof1_6 fsuppssof1_7 cvv fsuppssof1_10 fsuppssof1_11 fsuppssof1_0 isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv cmpt ccnv cvv fsuppssof1_10 csn cdif cima fsuppssof1_2 ccnv cvv fsuppssof1_10 csn cdif cima fsuppssof1_6 fsuppssof1_0 fsuppssof1_2 ccnv isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv cmpt ccnv cvv fsuppssof1_10 csn cdif fsuppssof1_0 fsuppssof1_2 isuppssof1_0 fsuppssof1_4 isuppssof1_0 sup_set_class fsuppssof1_2 cfv cmpt fsuppssof1_0 isuppssof1_0 fsuppssof1_4 fsuppssof1_8 fsuppssof1_2 esuppssof1_2 feqmptd cnveqd imaeq1d esuppssof1_0 eqsstr3d esuppssof1_1 isuppssof1_0 sup_set_class fsuppssof1_2 cfv cvv wcel fsuppssof1_0 isuppssof1_0 sup_set_class fsuppssof1_4 wcel wa isuppssof1_0 sup_set_class fsuppssof1_2 fvex a1i fsuppssof1_0 fsuppssof1_4 fsuppssof1_5 fsuppssof1_3 wf isuppssof1_0 sup_set_class fsuppssof1_4 wcel isuppssof1_0 sup_set_class fsuppssof1_3 cfv fsuppssof1_5 wcel esuppssof1_3 fsuppssof1_4 fsuppssof1_5 isuppssof1_0 sup_set_class fsuppssof1_3 ffvelrn sylan suppssov1 eqsstrd $.
$}

