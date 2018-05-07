$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/First_and_second_members_of_an_ordered_pair.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Function transposition

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c tpos  $.
$( Function transposition $)
$( The transposition of a function. $)
${
	$v F $.
	fctpos_0 $f class F $.
	ctpos $a class tpos F $.
$}
$( Define the transposition of a function, which is a function
       ` G = tpos F ` satisfying ` G ( x , y ) = F ( y , x ) ` .  (Contributed
       by Mario Carneiro, 10-Sep-2015.) $)
${
	$v x $.
	$v F $.
	$d F x $.
	fdf-tpos_0 $f set x $.
	fdf-tpos_1 $f class F $.
	df-tpos $a |- tpos F = ( F o. ( x e. ( `' dom F u. { (/) } ) |-> U. `' { x } ) ) $.
$}
$( Subset theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	$v G $.
	$v x $.
	$d x F $.
	$d x G $.
	itposss_0 $f set x $.
	ftposss_0 $f class F $.
	ftposss_1 $f class G $.
	tposss $p |- ( F C_ G -> tpos F C_ tpos G ) $= ftposss_0 ftposss_1 wss ftposss_0 itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_1 itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_0 ctpos ftposss_1 ctpos ftposss_0 ftposss_1 wss ftposss_0 itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_1 itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_1 itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_0 ftposss_1 itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt coss1 ftposss_0 ftposss_1 wss itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt wss ftposss_1 itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom ftposss_1 itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ccom wss ftposss_0 ftposss_1 wss itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_0 cdm ccnv c0 csn cun cres itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt wss itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt wss itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_0 cdm ccnv c0 csn cun resss ftposss_0 ftposss_1 wss itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_0 cdm ccnv c0 csn cun cres itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_0 ftposss_1 wss ftposss_0 cdm ccnv ftposss_1 cdm ccnv wss ftposss_0 cdm ccnv c0 csn cun ftposss_1 cdm ccnv c0 csn cun wss itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_0 cdm ccnv c0 csn cun cres itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt wceq ftposss_0 ftposss_1 wss ftposss_0 cdm ftposss_1 cdm wss ftposss_0 cdm ccnv ftposss_1 cdm ccnv wss ftposss_0 ftposss_1 dmss ftposss_0 cdm ftposss_1 cdm cnvss syl ftposss_0 cdm ccnv ftposss_1 cdm ccnv c0 csn unss1 itposss_0 ftposss_1 cdm ccnv c0 csn cun ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni resmpt 3syl sseq1d mpbii itposss_0 ftposss_0 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt itposss_0 ftposss_1 cdm ccnv c0 csn cun itposss_0 sup_set_class csn ccnv cuni cmpt ftposss_1 coss2 syl sstrd itposss_0 ftposss_0 df-tpos itposss_0 ftposss_1 df-tpos 3sstr4g $.
$}
$( Equality theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	$v G $.
	ftposeq_0 $f class F $.
	ftposeq_1 $f class G $.
	tposeq $p |- ( F = G -> tpos F = tpos G ) $= ftposeq_0 ftposeq_1 wceq ftposeq_0 ctpos ftposeq_1 ctpos ftposeq_0 ftposeq_1 wceq ftposeq_0 ftposeq_1 wss ftposeq_0 ctpos ftposeq_1 ctpos wss ftposeq_0 ftposeq_1 eqimss ftposeq_0 ftposeq_1 tposss syl ftposeq_0 ftposeq_1 wceq ftposeq_1 ftposeq_0 wss ftposeq_1 ctpos ftposeq_0 ctpos wss ftposeq_1 ftposeq_0 eqimss2 ftposeq_1 ftposeq_0 tposss syl eqssd $.
$}
$( Equality theorem for transposition.  (Contributed by Mario Carneiro,
         7-Jan-2017.) $)
${
	$v ph $.
	$v F $.
	$v G $.
	ftposeqd_0 $f wff ph $.
	ftposeqd_1 $f class F $.
	ftposeqd_2 $f class G $.
	etposeqd_0 $e |- ( ph -> F = G ) $.
	tposeqd $p |- ( ph -> tpos F = tpos G ) $= ftposeqd_0 ftposeqd_1 ftposeqd_2 wceq ftposeqd_1 ctpos ftposeqd_2 ctpos wceq etposeqd_0 ftposeqd_1 ftposeqd_2 tposeq syl $.
$}
$( The transposition is a subset of a cross product.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
${
	$v F $.
	$v x $.
	$d x F $.
	itposssxp_0 $f set x $.
	ftposssxp_0 $f class F $.
	tposssxp $p |- tpos F C_ ( ( `' dom F u. { (/) } ) X. ran F ) $= ftposssxp_0 ctpos itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cdm ftposssxp_0 crn cxp ftposssxp_0 cdm ccnv c0 csn cun ftposssxp_0 crn cxp ftposssxp_0 ctpos ftposssxp_0 itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt ccom itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cdm ftposssxp_0 crn cxp itposssxp_0 ftposssxp_0 df-tpos ftposssxp_0 itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cossxp eqsstri itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cdm ftposssxp_0 cdm ccnv c0 csn cun wss itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cdm ftposssxp_0 crn cxp ftposssxp_0 cdm ccnv c0 csn cun ftposssxp_0 crn cxp wss itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt eqid dmmptss itposssxp_0 ftposssxp_0 cdm ccnv c0 csn cun itposssxp_0 sup_set_class csn ccnv cuni cmpt cdm ftposssxp_0 cdm ccnv c0 csn cun ftposssxp_0 crn xpss1 ax-mp sstri $.
$}
$( The transposition is a relation.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	freltpos_0 $f class F $.
	reltpos $p |- Rel tpos F $= freltpos_0 ctpos freltpos_0 cdm ccnv c0 csn cun freltpos_0 crn cxp wss freltpos_0 cdm ccnv c0 csn cun freltpos_0 crn cxp wrel freltpos_0 ctpos wrel freltpos_0 tposssxp freltpos_0 cdm ccnv c0 csn cun freltpos_0 crn relxp freltpos_0 ctpos freltpos_0 cdm ccnv c0 csn cun freltpos_0 crn cxp relss mp2 $.
$}
$( Value of the transposition at a pair ` <. A , B >. ` .  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	$v V $.
	$v x $.
	$v y $.
	$d x y A $.
	$d x y B $.
	$d x y F $.
	ibrtpos2_0 $f set x $.
	ibrtpos2_1 $f set y $.
	fbrtpos2_0 $f class A $.
	fbrtpos2_1 $f class B $.
	fbrtpos2_2 $f class F $.
	fbrtpos2_3 $f class V $.
	brtpos2 $p |- ( B e. V -> ( A tpos F B <-> ( A e. ( `' dom F u. { (/) } ) /\ U. `' { A } F B ) ) ) $= fbrtpos2_1 fbrtpos2_3 wcel fbrtpos2_0 cvv wcel fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos wbr fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos wbr fbrtpos2_0 cvv wcel wi fbrtpos2_1 fbrtpos2_3 wcel fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos fbrtpos2_2 reltpos brrelexi a1i fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa fbrtpos2_0 cvv wcel wi fbrtpos2_1 fbrtpos2_3 wcel fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 cvv wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun elex adantr a1i fbrtpos2_0 cvv wcel fbrtpos2_1 fbrtpos2_3 wcel fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos wbr fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa wb fbrtpos2_0 cvv wcel fbrtpos2_1 fbrtpos2_3 wcel wa fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos wbr fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 wex fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos wbr fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt ccom wbr fbrtpos2_0 cvv wcel fbrtpos2_1 fbrtpos2_3 wcel wa fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 wex fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ctpos fbrtpos2_2 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt ccom ibrtpos2_0 fbrtpos2_2 df-tpos breqi ibrtpos2_1 fbrtpos2_0 fbrtpos2_1 fbrtpos2_2 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cvv fbrtpos2_3 brcog syl5bb fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 wex ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa wa ibrtpos2_1 wex fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa wa ibrtpos2_1 fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel wa ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa wa fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel wa ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq wa ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel wa fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cdm wcel fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv ibrtpos2_1 sup_set_class wceq wa fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq wa ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wfun fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt wbr fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cdm wcel fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv ibrtpos2_1 sup_set_class wceq wa wb ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni funmpt fbrtpos2_0 ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt funbrfv2b ax-mp fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cdm wcel fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv ibrtpos2_1 sup_set_class wceq wa fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv wceq wa fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq wa fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cdm wcel fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv ibrtpos2_1 sup_set_class wceq ibrtpos2_1 sup_set_class fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv wceq ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cdm fbrtpos2_2 cdm ccnv c0 csn cun fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt ibrtpos2_0 sup_set_class csn ccnv ibrtpos2_0 sup_set_class csn ibrtpos2_0 sup_set_class snex cnvex uniex ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt eqid dmmpti eleq2i fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv ibrtpos2_1 sup_set_class eqcom anbi12i fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv wceq ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt cfv fbrtpos2_0 csn ccnv cuni ibrtpos2_1 sup_set_class ibrtpos2_0 fbrtpos2_0 ibrtpos2_0 sup_set_class csn ccnv cuni fbrtpos2_0 csn ccnv cuni fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt ibrtpos2_0 sup_set_class fbrtpos2_0 wceq ibrtpos2_0 sup_set_class csn ccnv fbrtpos2_0 csn ccnv ibrtpos2_0 sup_set_class fbrtpos2_0 wceq ibrtpos2_0 sup_set_class csn fbrtpos2_0 csn ibrtpos2_0 sup_set_class fbrtpos2_0 sneq cnveqd unieqd ibrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun ibrtpos2_0 sup_set_class csn ccnv cuni cmpt eqid fbrtpos2_0 csn ccnv fbrtpos2_0 csn fbrtpos2_0 snex cnvex uniex fvmpt eqeq2d pm5.32i bitri bitri fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq ancom bitri anbi1i ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr anass bitri exbii fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr wa fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr wa ibrtpos2_1 fbrtpos2_0 csn ccnv cuni fbrtpos2_0 csn ccnv fbrtpos2_0 csn fbrtpos2_0 snex cnvex uniex ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni wceq ibrtpos2_1 sup_set_class fbrtpos2_1 fbrtpos2_2 wbr fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 wbr fbrtpos2_0 fbrtpos2_2 cdm ccnv c0 csn cun wcel ibrtpos2_1 sup_set_class fbrtpos2_0 csn ccnv cuni fbrtpos2_1 fbrtpos2_2 breq1 anbi2d ceqsexv bitri syl6bb expcom pm5.21ndd $.
$}
$( The behavior of ` tpos ` when the left argument is the empty set (which
       is not an ordered pair but is the "default" value of an ordered pair
       when the arguments are proper classes).  This allows us to eliminate
       sethood hypotheses on ` A , B ` in ~ brtpos .  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
${
	$v A $.
	$v F $.
	$v V $.
	fbrtpos0_0 $f class A $.
	fbrtpos0_1 $f class F $.
	fbrtpos0_2 $f class V $.
	brtpos0 $p |- ( A e. V -> ( (/) tpos F A <-> (/) F A ) ) $= fbrtpos0_0 fbrtpos0_2 wcel c0 fbrtpos0_0 fbrtpos0_1 ctpos wbr c0 fbrtpos0_1 cdm ccnv c0 csn cun wcel c0 csn ccnv cuni fbrtpos0_0 fbrtpos0_1 wbr wa c0 fbrtpos0_0 fbrtpos0_1 wbr c0 fbrtpos0_0 fbrtpos0_1 fbrtpos0_2 brtpos2 c0 fbrtpos0_1 cdm ccnv c0 csn cun wcel c0 csn ccnv cuni fbrtpos0_0 fbrtpos0_1 wbr wa c0 csn ccnv cuni fbrtpos0_0 fbrtpos0_1 wbr c0 fbrtpos0_0 fbrtpos0_1 wbr c0 fbrtpos0_1 cdm ccnv c0 csn cun wcel c0 csn ccnv cuni fbrtpos0_0 fbrtpos0_1 wbr c0 csn fbrtpos0_1 cdm ccnv c0 csn cun c0 c0 csn fbrtpos0_1 cdm ccnv ssun2 c0 0ex snid sselii biantrur c0 csn ccnv cuni c0 fbrtpos0_0 fbrtpos0_1 c0 csn ccnv cuni c0 cuni c0 c0 csn ccnv c0 cnvsn0 unieqi uni0 eqtri breq1i bitr3i syl6bb $.
$}
$( Necessary and sufficient condition for ` dom tpos F ` to be a relation.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
${
	$v F $.
	$v x $.
	$v y $.
	$d x y $.
	$d x y $.
	$d x y F $.
	ireldmtpos_0 $f set x $.
	ireldmtpos_1 $f set y $.
	freldmtpos_0 $f class F $.
	reldmtpos $p |- ( Rel dom tpos F <-> -. (/) e. dom F ) $= freldmtpos_0 ctpos cdm wrel c0 freldmtpos_0 cdm wcel wn c0 freldmtpos_0 cdm wcel freldmtpos_0 ctpos cdm wrel c0 freldmtpos_0 cdm wcel c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr ireldmtpos_1 wex freldmtpos_0 ctpos cdm wrel wn ireldmtpos_1 c0 freldmtpos_0 0ex eldm c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr freldmtpos_0 ctpos cdm wrel wn ireldmtpos_1 c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr freldmtpos_0 ctpos cdm wrel wn ireldmtpos_1 sup_set_class cvv wcel c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr wb ireldmtpos_1 vex ireldmtpos_1 sup_set_class freldmtpos_0 cvv brtpos0 ax-mp freldmtpos_0 ctpos cdm wrel c0 freldmtpos_0 ctpos cdm wcel c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr freldmtpos_0 ctpos cdm wrel c0 freldmtpos_0 ctpos cdm wcel c0 cvv cvv cxp wcel cvv cvv 0nelxp freldmtpos_0 ctpos cdm wrel freldmtpos_0 ctpos cdm cvv cvv cxp wss c0 freldmtpos_0 ctpos cdm wcel c0 cvv cvv cxp wcel wi freldmtpos_0 ctpos cdm df-rel freldmtpos_0 ctpos cdm cvv cvv cxp c0 ssel sylbi mtoi c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos 0ex ireldmtpos_1 vex breldm nsyl3 sylbir exlimiv sylbi con2i c0 freldmtpos_0 cdm wcel wn freldmtpos_0 ctpos cdm cvv cvv cxp wss freldmtpos_0 ctpos cdm wrel c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 freldmtpos_0 ctpos cdm cvv cvv cxp ireldmtpos_0 sup_set_class freldmtpos_0 ctpos cdm wcel ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_1 wex c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class cvv cvv cxp wcel ireldmtpos_1 ireldmtpos_0 sup_set_class freldmtpos_0 ctpos ireldmtpos_0 vex eldm c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class cvv cvv cxp wcel ireldmtpos_1 c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class cvv cvv cxp wcel c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr wa ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv wcel ireldmtpos_0 sup_set_class cvv cvv cxp wcel ireldmtpos_0 sup_set_class c0 csn wcel ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv wcel ireldmtpos_0 sup_set_class cvv cvv cxp wcel wi c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr wa freldmtpos_0 cdm ccnv cvv cvv cxp ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv wrel freldmtpos_0 cdm ccnv cvv cvv cxp wss freldmtpos_0 cdm relcnv freldmtpos_0 cdm ccnv df-rel mpbi sseli a1i ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class c0 csn wcel ireldmtpos_0 sup_set_class cvv cvv cxp wcel wi ireldmtpos_0 sup_set_class c0 csn wcel ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class cvv cvv cxp wcel ireldmtpos_0 sup_set_class c0 csn wcel ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class cvv cvv cxp wcel wi ireldmtpos_0 sup_set_class c0 csn wcel ireldmtpos_0 sup_set_class c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos ireldmtpos_0 sup_set_class c0 elsni breq1d c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class cvv cvv cxp wcel wi ireldmtpos_1 sup_set_class cvv wcel c0 ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr wb ireldmtpos_1 vex ireldmtpos_1 sup_set_class freldmtpos_0 cvv brtpos0 ax-mp c0 ireldmtpos_1 sup_set_class freldmtpos_0 wbr c0 freldmtpos_0 cdm wcel ireldmtpos_0 sup_set_class cvv cvv cxp wcel c0 ireldmtpos_1 sup_set_class freldmtpos_0 0ex ireldmtpos_1 vex breldm pm2.24d sylbi syl6bi com3l impcom ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv wcel ireldmtpos_0 sup_set_class c0 csn wcel wo c0 freldmtpos_0 cdm wcel wn ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv c0 csn cun wcel ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv wcel ireldmtpos_0 sup_set_class c0 csn wcel wo ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv c0 csn cun wcel ireldmtpos_0 sup_set_class csn ccnv cuni ireldmtpos_1 sup_set_class freldmtpos_0 wbr ireldmtpos_1 sup_set_class cvv wcel ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 ctpos wbr ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv c0 csn cun wcel ireldmtpos_0 sup_set_class csn ccnv cuni ireldmtpos_1 sup_set_class freldmtpos_0 wbr wa wb ireldmtpos_1 vex ireldmtpos_0 sup_set_class ireldmtpos_1 sup_set_class freldmtpos_0 cvv brtpos2 ax-mp simplbi ireldmtpos_0 sup_set_class freldmtpos_0 cdm ccnv c0 csn elun sylib adantl mpjaod ex exlimdv syl5bi ssrdv freldmtpos_0 ctpos cdm df-rel sylibr impbii $.
$}
$( The transposition swaps arguments of a three-parameter relation.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v V $.
	fbrtpos_0 $f class A $.
	fbrtpos_1 $f class B $.
	fbrtpos_2 $f class C $.
	fbrtpos_3 $f class F $.
	fbrtpos_4 $f class V $.
	brtpos $p |- ( C e. V -> ( <. A , B >. tpos F C <-> <. B , A >. F C ) ) $= fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr wb fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr wb fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wa fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_0 fbrtpos_1 cop csn ccnv cuni fbrtpos_2 fbrtpos_3 wbr wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_0 fbrtpos_1 cop csn ccnv cuni fbrtpos_2 fbrtpos_3 wbr wa wb fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 fbrtpos_4 brtpos2 adantr fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr wa fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_0 fbrtpos_1 cop csn ccnv cuni fbrtpos_2 fbrtpos_3 wbr wa fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv wcel fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_3 cdm wcel fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv wcel fbrtpos_2 fbrtpos_4 wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_3 cdm wcel wi fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_1 fbrtpos_0 cop cvv wcel fbrtpos_2 fbrtpos_4 wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_3 cdm wcel wi fbrtpos_1 fbrtpos_0 opex fbrtpos_1 fbrtpos_0 cop cvv wcel fbrtpos_2 fbrtpos_4 wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_3 cdm wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_2 cvv fbrtpos_4 fbrtpos_3 breldmg 3expia mpan adantr fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv wcel fbrtpos_1 fbrtpos_0 cop fbrtpos_3 cdm wcel wb fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 fbrtpos_1 cvv cvv fbrtpos_3 cdm opelcnvg adantl sylibrd fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn elun1 syl6 pm4.71rd fbrtpos_0 fbrtpos_1 cop csn ccnv cuni fbrtpos_2 fbrtpos_3 wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr fbrtpos_0 fbrtpos_1 cop fbrtpos_3 cdm ccnv c0 csn cun wcel fbrtpos_0 fbrtpos_1 cop csn ccnv cuni fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 fbrtpos_0 fbrtpos_1 opswap breq1i anbi2i syl6bbr bitr4d ex fbrtpos_2 fbrtpos_4 wcel fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr wb fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wn c0 fbrtpos_2 fbrtpos_3 ctpos wbr c0 fbrtpos_2 fbrtpos_3 wbr wb fbrtpos_2 fbrtpos_3 fbrtpos_4 brtpos0 fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wn fbrtpos_0 fbrtpos_1 cop fbrtpos_2 fbrtpos_3 ctpos wbr c0 fbrtpos_2 fbrtpos_3 ctpos wbr fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr c0 fbrtpos_2 fbrtpos_3 wbr fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa wn fbrtpos_0 fbrtpos_1 cop c0 fbrtpos_2 fbrtpos_3 ctpos fbrtpos_0 fbrtpos_1 opprc breq1d fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel wa fbrtpos_1 cvv wcel fbrtpos_0 cvv wcel wa fbrtpos_1 fbrtpos_0 cop fbrtpos_2 fbrtpos_3 wbr c0 fbrtpos_2 fbrtpos_3 wbr wb fbrtpos_0 cvv wcel fbrtpos_1 cvv wcel ancom fbrtpos_1 cvv wcel fbrtpos_0 cvv wcel wa wn fbrtpos_1 fbrtpos_0 cop c0 fbrtpos_2 fbrtpos_3 fbrtpos_1 fbrtpos_0 opprc breq1d sylnbi bibi12d syl5ibrcom pm2.61d $.
$}
$( The transposition swaps the first two elements in a collection of
       ordered triples.  (Contributed by Mario Carneiro, 1-Dec-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v V $.
	fottpos_0 $f class A $.
	fottpos_1 $f class B $.
	fottpos_2 $f class C $.
	fottpos_3 $f class F $.
	fottpos_4 $f class V $.
	ottpos $p |- ( C e. V -> ( <. A , B , C >. e. tpos F <-> <. B , A , C >. e. F ) ) $= fottpos_2 fottpos_4 wcel fottpos_0 fottpos_1 cop fottpos_2 cop fottpos_3 ctpos wcel fottpos_1 fottpos_0 cop fottpos_2 cop fottpos_3 wcel fottpos_0 fottpos_1 fottpos_2 cotp fottpos_3 ctpos wcel fottpos_1 fottpos_0 fottpos_2 cotp fottpos_3 wcel fottpos_2 fottpos_4 wcel fottpos_0 fottpos_1 cop fottpos_2 fottpos_3 ctpos wbr fottpos_1 fottpos_0 cop fottpos_2 fottpos_3 wbr fottpos_0 fottpos_1 cop fottpos_2 cop fottpos_3 ctpos wcel fottpos_1 fottpos_0 cop fottpos_2 cop fottpos_3 wcel fottpos_0 fottpos_1 fottpos_2 fottpos_3 fottpos_4 brtpos fottpos_0 fottpos_1 cop fottpos_2 fottpos_3 ctpos df-br fottpos_1 fottpos_0 cop fottpos_2 fottpos_3 df-br 3bitr3g fottpos_0 fottpos_1 fottpos_2 cotp fottpos_0 fottpos_1 cop fottpos_2 cop fottpos_3 ctpos fottpos_0 fottpos_1 fottpos_2 df-ot eleq1i fottpos_1 fottpos_0 fottpos_2 cotp fottpos_1 fottpos_0 cop fottpos_2 cop fottpos_3 fottpos_1 fottpos_0 fottpos_2 df-ot eleq1i 3bitr4g $.
$}
$( The transposition swaps arguments of a three-parameter relation.
       (Contributed by Mario Carneiro, 3-Nov-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	frelbrtpos_0 $f class A $.
	frelbrtpos_1 $f class B $.
	frelbrtpos_2 $f class C $.
	frelbrtpos_3 $f class F $.
	relbrtpos $p |- ( Rel F -> ( <. A , B >. tpos F C <-> <. B , A >. F C ) ) $= frelbrtpos_3 wrel frelbrtpos_0 frelbrtpos_1 cop frelbrtpos_2 frelbrtpos_3 ctpos wbr frelbrtpos_1 frelbrtpos_0 cop frelbrtpos_2 frelbrtpos_3 wbr frelbrtpos_2 cvv wcel frelbrtpos_3 wrel frelbrtpos_3 ctpos wrel frelbrtpos_0 frelbrtpos_1 cop frelbrtpos_2 frelbrtpos_3 ctpos wbr frelbrtpos_2 cvv wcel frelbrtpos_3 ctpos wrel frelbrtpos_3 wrel frelbrtpos_3 reltpos a1i frelbrtpos_0 frelbrtpos_1 cop frelbrtpos_2 frelbrtpos_3 ctpos brrelex2 sylan frelbrtpos_1 frelbrtpos_0 cop frelbrtpos_2 frelbrtpos_3 brrelex2 frelbrtpos_0 frelbrtpos_1 frelbrtpos_2 frelbrtpos_3 cvv brtpos pm5.21nd $.
$}
$( The domain of ` tpos F ` when ` dom F ` is a relation.  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
${
	$v F $.
	$v x $.
	$v y $.
	$v z $.
	$d x y $.
	$d x y $.
	$d x y z F $.
	idmtpos_0 $f set x $.
	idmtpos_1 $f set y $.
	idmtpos_2 $f set z $.
	fdmtpos_0 $f class F $.
	dmtpos $p |- ( Rel dom F -> dom tpos F = `' dom F ) $= fdmtpos_0 ctpos cdm wrel fdmtpos_0 cdm ccnv wrel wa fdmtpos_0 cdm wrel fdmtpos_0 ctpos cdm fdmtpos_0 cdm ccnv wceq fdmtpos_0 cdm wrel fdmtpos_0 ctpos cdm wrel fdmtpos_0 cdm ccnv wrel fdmtpos_0 cdm cvv cvv cxp wss c0 fdmtpos_0 cdm wcel wn fdmtpos_0 cdm wrel fdmtpos_0 ctpos cdm wrel fdmtpos_0 cdm cvv cvv cxp wss c0 fdmtpos_0 cdm wcel c0 cvv cvv cxp wcel cvv cvv 0nelxp fdmtpos_0 cdm cvv cvv cxp c0 ssel mtoi fdmtpos_0 cdm df-rel fdmtpos_0 reldmtpos 3imtr4i fdmtpos_0 cdm relcnv jctir fdmtpos_0 cdm wrel idmtpos_0 idmtpos_1 fdmtpos_0 ctpos cdm fdmtpos_0 cdm ccnv fdmtpos_0 cdm wrel idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 ctpos wbr idmtpos_2 wex idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 wbr idmtpos_2 wex idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop fdmtpos_0 ctpos cdm wcel idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop fdmtpos_0 cdm ccnv wcel fdmtpos_0 cdm wrel idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 ctpos wbr idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 wbr idmtpos_2 idmtpos_2 sup_set_class cvv wcel idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 ctpos wbr idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 wbr wb fdmtpos_0 cdm wrel idmtpos_2 vex idmtpos_0 sup_set_class idmtpos_1 sup_set_class idmtpos_2 sup_set_class fdmtpos_0 cvv brtpos mp1i exbidv idmtpos_2 idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop fdmtpos_0 ctpos idmtpos_0 sup_set_class idmtpos_1 sup_set_class opex eldm idmtpos_0 sup_set_class idmtpos_1 sup_set_class cop fdmtpos_0 cdm ccnv wcel idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop fdmtpos_0 cdm wcel idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop idmtpos_2 sup_set_class fdmtpos_0 wbr idmtpos_2 wex idmtpos_0 sup_set_class idmtpos_1 sup_set_class fdmtpos_0 cdm idmtpos_0 vex idmtpos_1 vex opelcnv idmtpos_2 idmtpos_1 sup_set_class idmtpos_0 sup_set_class cop fdmtpos_0 idmtpos_1 sup_set_class idmtpos_0 sup_set_class opex eldm bitri 3bitr4g eqrelrdv2 mpancom $.
$}
$( The range of ` tpos F ` when ` dom F ` is a relation.  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
${
	$v F $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d x y $.
	$d w x y z F $.
	irntpos_0 $f set x $.
	irntpos_1 $f set y $.
	irntpos_2 $f set z $.
	irntpos_3 $f set w $.
	frntpos_0 $f class F $.
	rntpos $p |- ( Rel dom F -> ran tpos F = ran F ) $= frntpos_0 cdm wrel irntpos_2 frntpos_0 ctpos crn frntpos_0 crn frntpos_0 cdm wrel irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_2 sup_set_class frntpos_0 crn wcel irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_3 wex frntpos_0 cdm wrel irntpos_2 sup_set_class frntpos_0 crn wcel irntpos_3 irntpos_2 sup_set_class frntpos_0 ctpos irntpos_2 vex elrn frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_2 sup_set_class frntpos_0 crn wcel irntpos_3 irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_1 wex irntpos_0 wex irntpos_2 sup_set_class frntpos_0 crn wcel frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_3 sup_set_class frntpos_0 cdm ccnv wcel irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_1 wex irntpos_0 wex irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_3 sup_set_class frntpos_0 ctpos cdm wcel frntpos_0 cdm wrel irntpos_3 sup_set_class frntpos_0 cdm ccnv wcel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos irntpos_3 vex irntpos_2 vex breldm frntpos_0 cdm wrel frntpos_0 ctpos cdm frntpos_0 cdm ccnv irntpos_3 sup_set_class frntpos_0 dmtpos eleq2d syl5ib frntpos_0 cdm ccnv wrel irntpos_3 sup_set_class frntpos_0 cdm ccnv wcel irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_1 wex irntpos_0 wex frntpos_0 cdm relcnv irntpos_0 irntpos_1 irntpos_3 sup_set_class frntpos_0 cdm ccnv elrel mpan syl6 irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_2 sup_set_class frntpos_0 crn wcel wi irntpos_0 irntpos_1 irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 wbr irntpos_2 sup_set_class frntpos_0 crn wcel irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 wbr irntpos_3 sup_set_class irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos breq1 irntpos_2 sup_set_class cvv wcel irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 wbr wb irntpos_2 vex irntpos_0 sup_set_class irntpos_1 sup_set_class irntpos_2 sup_set_class frntpos_0 cvv brtpos ax-mp syl6bb irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 irntpos_1 sup_set_class irntpos_0 sup_set_class opex irntpos_2 vex brelrn syl6bi exlimivv syli exlimdv syl5bi irntpos_2 sup_set_class frntpos_0 crn wcel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_3 wex frntpos_0 cdm wrel irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_3 irntpos_2 sup_set_class frntpos_0 irntpos_2 vex elrn frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_3 irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_0 wex irntpos_1 wex irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_3 sup_set_class frntpos_0 cdm wcel frntpos_0 cdm wrel irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_0 wex irntpos_1 wex irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 irntpos_3 vex irntpos_2 vex breldm frntpos_0 cdm wrel irntpos_3 sup_set_class frntpos_0 cdm wcel irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_0 wex irntpos_1 wex irntpos_1 irntpos_0 irntpos_3 sup_set_class frntpos_0 cdm elrel ex syl5 irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_2 sup_set_class frntpos_0 ctpos crn wcel wi irntpos_1 irntpos_0 irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_2 sup_set_class frntpos_0 ctpos crn wcel irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop wceq irntpos_3 sup_set_class irntpos_2 sup_set_class frntpos_0 wbr irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 wbr irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_3 sup_set_class irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 breq1 irntpos_2 sup_set_class cvv wcel irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos wbr irntpos_1 sup_set_class irntpos_0 sup_set_class cop irntpos_2 sup_set_class frntpos_0 wbr wb irntpos_2 vex irntpos_0 sup_set_class irntpos_1 sup_set_class irntpos_2 sup_set_class frntpos_0 cvv brtpos ax-mp syl6bbr irntpos_0 sup_set_class irntpos_1 sup_set_class cop irntpos_2 sup_set_class frntpos_0 ctpos irntpos_0 sup_set_class irntpos_1 sup_set_class opex irntpos_2 vex brelrn syl6bi exlimivv syli exlimdv syl5bi impbid eqrdv $.
$}
$( The transposition of a set is a set.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	$v V $.
	ftposexg_0 $f class F $.
	ftposexg_1 $f class V $.
	tposexg $p |- ( F e. V -> tpos F e. _V ) $= ftposexg_0 ftposexg_1 wcel ftposexg_0 ctpos ftposexg_0 cdm ccnv c0 csn cun ftposexg_0 crn cxp wss ftposexg_0 cdm ccnv c0 csn cun ftposexg_0 crn cxp cvv wcel ftposexg_0 ctpos cvv wcel ftposexg_0 tposssxp ftposexg_0 ftposexg_1 wcel ftposexg_0 cdm ccnv c0 csn cun cvv wcel ftposexg_0 crn cvv wcel ftposexg_0 cdm ccnv c0 csn cun ftposexg_0 crn cxp cvv wcel ftposexg_0 ftposexg_1 wcel ftposexg_0 cdm ccnv cvv wcel c0 csn cvv wcel ftposexg_0 cdm ccnv c0 csn cun cvv wcel ftposexg_0 ftposexg_1 wcel ftposexg_0 cdm cvv wcel ftposexg_0 cdm ccnv cvv wcel ftposexg_0 ftposexg_1 dmexg ftposexg_0 cdm cvv cnvexg syl c0 snex ftposexg_0 cdm ccnv c0 csn cvv cvv unexg sylancl ftposexg_0 ftposexg_1 rnexg ftposexg_0 cdm ccnv c0 csn cun ftposexg_0 crn cvv cvv xpexg syl2anc ftposexg_0 ctpos ftposexg_0 cdm ccnv c0 csn cun ftposexg_0 crn cxp cvv ssexg sylancr $.
$}
$( The transposition swaps the arguments in a two-argument function.  When
       ` F ` is a matrix, which is to say a function from
       ` ( 1 ... m ) X. ( 1 ... n ) ` to ` RR ` or some ring, ` tpos F ` is the
       transposition of ` F ` , which is where the name comes from.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	$v y $.
	$d y A $.
	$d y B $.
	$d y F $.
	iovtpos_0 $f set y $.
	fovtpos_0 $f class A $.
	fovtpos_1 $f class B $.
	fovtpos_2 $f class F $.
	ovtpos $p |- ( A tpos F B ) = ( B F A ) $= fovtpos_0 fovtpos_1 cop fovtpos_2 ctpos cfv fovtpos_1 fovtpos_0 cop fovtpos_2 cfv fovtpos_0 fovtpos_1 fovtpos_2 ctpos co fovtpos_1 fovtpos_0 fovtpos_2 co fovtpos_0 fovtpos_1 cop iovtpos_0 sup_set_class fovtpos_2 ctpos wbr iovtpos_0 cio fovtpos_1 fovtpos_0 cop iovtpos_0 sup_set_class fovtpos_2 wbr iovtpos_0 cio fovtpos_0 fovtpos_1 cop fovtpos_2 ctpos cfv fovtpos_1 fovtpos_0 cop fovtpos_2 cfv fovtpos_0 fovtpos_1 cop iovtpos_0 sup_set_class fovtpos_2 ctpos wbr fovtpos_1 fovtpos_0 cop iovtpos_0 sup_set_class fovtpos_2 wbr iovtpos_0 iovtpos_0 sup_set_class cvv wcel fovtpos_0 fovtpos_1 cop iovtpos_0 sup_set_class fovtpos_2 ctpos wbr fovtpos_1 fovtpos_0 cop iovtpos_0 sup_set_class fovtpos_2 wbr wb iovtpos_0 vex fovtpos_0 fovtpos_1 iovtpos_0 sup_set_class fovtpos_2 cvv brtpos ax-mp iotabii iovtpos_0 fovtpos_0 fovtpos_1 cop fovtpos_2 ctpos df-fv iovtpos_0 fovtpos_1 fovtpos_0 cop fovtpos_2 df-fv 3eqtr4i fovtpos_0 fovtpos_1 fovtpos_2 ctpos df-ov fovtpos_1 fovtpos_0 fovtpos_2 df-ov 3eqtr4i $.
$}
$( The transposition of a function is a function.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
${
	$v F $.
	$v x $.
	$d x F $.
	itposfun_0 $f set x $.
	ftposfun_0 $f class F $.
	tposfun $p |- ( Fun F -> Fun tpos F ) $= ftposfun_0 wfun ftposfun_0 itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni cmpt ccom wfun ftposfun_0 ctpos wfun ftposfun_0 wfun itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni cmpt wfun ftposfun_0 itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni cmpt ccom wfun itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni funmpt ftposfun_0 itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni cmpt funco mpan2 ftposfun_0 ctpos ftposfun_0 itposfun_0 ftposfun_0 cdm ccnv c0 csn cun itposfun_0 sup_set_class csn ccnv cuni cmpt ccom itposfun_0 ftposfun_0 df-tpos funeqi sylibr $.
$}
$( Alternate definition of ` tpos ` when ` F ` has relational domain.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
${
	$v x $.
	$v F $.
	$d x F $.
	fdftpos2_0 $f set x $.
	fdftpos2_1 $f class F $.
	dftpos2 $p |- ( Rel dom F -> tpos F = ( F o. ( x e. `' dom F |-> U. `' { x } ) ) ) $= fdftpos2_1 cdm wrel fdftpos2_1 ctpos fdftpos2_1 ctpos cdm cres fdftpos2_1 ctpos fdftpos2_1 cdm ccnv cres fdftpos2_1 ctpos fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv fdftpos2_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos2_1 cdm wrel fdftpos2_1 ctpos cdm fdftpos2_1 cdm ccnv fdftpos2_1 ctpos fdftpos2_1 dmtpos reseq2d fdftpos2_1 ctpos wrel fdftpos2_1 ctpos fdftpos2_1 ctpos cdm cres fdftpos2_1 ctpos wceq fdftpos2_1 reltpos fdftpos2_1 ctpos resdm ax-mp fdftpos2_1 ctpos fdftpos2_1 cdm ccnv cres fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos2_1 cdm ccnv cres fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt fdftpos2_1 cdm ccnv cres ccom fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv fdftpos2_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos2_1 ctpos fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos2_1 cdm ccnv fdftpos2_0 fdftpos2_1 df-tpos reseq1i fdftpos2_1 fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt fdftpos2_1 cdm ccnv resco fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt fdftpos2_1 cdm ccnv cres fdftpos2_0 fdftpos2_1 cdm ccnv fdftpos2_0 sup_set_class csn ccnv cuni cmpt fdftpos2_1 fdftpos2_1 cdm ccnv fdftpos2_1 cdm ccnv c0 csn cun wss fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_0 sup_set_class csn ccnv cuni cmpt fdftpos2_1 cdm ccnv cres fdftpos2_0 fdftpos2_1 cdm ccnv fdftpos2_0 sup_set_class csn ccnv cuni cmpt wceq fdftpos2_1 cdm ccnv c0 csn ssun1 fdftpos2_0 fdftpos2_1 cdm ccnv c0 csn cun fdftpos2_1 cdm ccnv fdftpos2_0 sup_set_class csn ccnv cuni resmpt ax-mp coeq2i 3eqtri 3eqtr3g $.
$}
$( Alternate definition of ` tpos ` when ` F ` has relational domain.
       Compare ~ df-cnv .  (Contributed by Mario Carneiro, 10-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v F $.
	$v w $.
	$d x y $.
	$d x y $.
	$d w x y z F $.
	idftpos3_0 $f set w $.
	fdftpos3_0 $f set x $.
	fdftpos3_1 $f set y $.
	fdftpos3_2 $f set z $.
	fdftpos3_3 $f class F $.
	dftpos3 $p |- ( Rel dom F -> tpos F = { <. <. x , y >. , z >. | <. y , x >. F z } ) $= fdftpos3_3 cdm wrel fdftpos3_3 ctpos idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wa fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 cab fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr fdftpos3_0 fdftpos3_1 fdftpos3_2 coprab fdftpos3_3 cdm wrel idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wa fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 fdftpos3_3 ctpos fdftpos3_3 cdm wrel idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel wa idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wa fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex fdftpos3_3 cdm wrel idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex fdftpos3_3 cdm wrel idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel idftpos3_0 sup_set_class cvv cvv cxp cvv cxp wcel idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex fdftpos3_3 cdm wrel fdftpos3_3 ctpos cvv cvv cxp cvv cxp idftpos3_0 sup_set_class fdftpos3_3 cdm wrel fdftpos3_3 ctpos wrel fdftpos3_3 ctpos cdm wrel wa fdftpos3_3 ctpos cvv cvv cxp cvv cxp wss fdftpos3_3 cdm wrel fdftpos3_3 ctpos cdm wrel fdftpos3_3 ctpos wrel fdftpos3_3 cdm wrel fdftpos3_3 ctpos cdm wrel fdftpos3_3 cdm ccnv wrel fdftpos3_3 cdm relcnv fdftpos3_3 cdm wrel fdftpos3_3 ctpos cdm fdftpos3_3 cdm ccnv fdftpos3_3 dmtpos releqd mpbiri fdftpos3_3 reltpos jctil fdftpos3_3 ctpos relrelss sylib sseld fdftpos3_0 fdftpos3_1 fdftpos3_2 idftpos3_0 sup_set_class elvvv syl6ib pm4.71rd idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel wa idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel wa fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wa fdftpos3_2 wex fdftpos3_1 wex fdftpos3_0 wex idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel fdftpos3_0 fdftpos3_1 fdftpos3_2 19.41vvv idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel wa idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wa fdftpos3_0 fdftpos3_1 fdftpos3_2 idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop wceq idftpos3_0 sup_set_class fdftpos3_3 ctpos wcel fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop fdftpos3_3 ctpos wcel fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr idftpos3_0 sup_set_class fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop fdftpos3_3 ctpos eleq1 fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class cop fdftpos3_3 ctpos wcel fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 ctpos wbr fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 ctpos df-br fdftpos3_2 sup_set_class cvv wcel fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 ctpos wbr fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr wb fdftpos3_2 vex fdftpos3_0 sup_set_class fdftpos3_1 sup_set_class fdftpos3_2 sup_set_class fdftpos3_3 cvv brtpos ax-mp bitr3i syl6bb pm5.32i 3exbii bitr3i syl6bb abbi2dv fdftpos3_1 sup_set_class fdftpos3_0 sup_set_class cop fdftpos3_2 sup_set_class fdftpos3_3 wbr fdftpos3_0 fdftpos3_1 fdftpos3_2 idftpos3_0 df-oprab syl6eqr $.
$}
$( Alternate definition of ` tpos ` .  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
${
	$v x $.
	$v F $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d x y $.
	$d w x y z F $.
	idftpos4_0 $f set y $.
	idftpos4_1 $f set z $.
	idftpos4_2 $f set w $.
	fdftpos4_0 $f set x $.
	fdftpos4_1 $f class F $.
	dftpos4 $p |- tpos F = ( F o. ( x e. ( ( _V X. _V ) u. { (/) } ) |-> U. `' { x } ) ) $= fdftpos4_1 ctpos fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos4_1 ctpos fdftpos4_1 fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos4_0 fdftpos4_1 df-tpos fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wss fdftpos4_1 fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom wss fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_1 cdm ccnv c0 csn cun cres fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_1 cdm ccnv cvv cvv cxp wss fdftpos4_1 cdm ccnv c0 csn cun cvv cvv cxp c0 csn cun wss fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_1 cdm ccnv c0 csn cun cres fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wceq fdftpos4_1 cdm ccnv wrel fdftpos4_1 cdm ccnv cvv cvv cxp wss fdftpos4_1 cdm relcnv fdftpos4_1 cdm ccnv df-rel mpbi fdftpos4_1 cdm ccnv cvv cvv cxp c0 csn unss1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni resmpt mp2b fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_1 cdm ccnv c0 csn cun resss eqsstr3i fdftpos4_0 fdftpos4_1 cdm ccnv c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt fdftpos4_1 coss2 ax-mp eqsstri idftpos4_0 idftpos4_1 fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom fdftpos4_1 ctpos fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt relco idftpos4_0 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt ccom wcel idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wbr idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_2 wex idftpos4_0 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 ctpos wcel idftpos4_2 idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt idftpos4_0 vex idftpos4_1 vex opelco idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wbr idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 ctpos wcel idftpos4_2 idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wbr idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 ctpos wbr idftpos4_0 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 ctpos wcel idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wbr idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 ctpos wbr idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt wbr idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_1 wbr wa fdftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_1 sup_set_class fdftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_1 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa fdftpos4_0 idftpos4_1 idftpos4_0 sup_set_class idftpos4_2 sup_set_class fdftpos4_0 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni cmpt idftpos4_0 vex idftpos4_2 vex fdftpos4_0 sup_set_class idftpos4_0 sup_set_class wceq fdftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_1 sup_set_class fdftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_1 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq fdftpos4_0 sup_set_class idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun eleq1 fdftpos4_0 sup_set_class idftpos4_0 sup_set_class wceq fdftpos4_0 sup_set_class csn ccnv cuni idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_0 sup_set_class idftpos4_0 sup_set_class wceq fdftpos4_0 sup_set_class csn ccnv idftpos4_0 sup_set_class csn ccnv fdftpos4_0 sup_set_class idftpos4_0 sup_set_class wceq fdftpos4_0 sup_set_class csn idftpos4_0 sup_set_class csn fdftpos4_0 sup_set_class idftpos4_0 sup_set_class sneq cnveqd unieqd eqeq2d anbi12d idftpos4_1 sup_set_class idftpos4_2 sup_set_class wceq idftpos4_1 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni eqeq1 anbi2d fdftpos4_0 idftpos4_1 cvv cvv cxp c0 csn cun fdftpos4_0 sup_set_class csn ccnv cuni df-mpt brab idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_1 wbr idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class c0 csn wcel idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel wi idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr simplr idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr idftpos4_2 sup_set_class fdftpos4_1 cdm wcel idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 idftpos4_2 vex idftpos4_1 vex breldm adantl eqeltrrd idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_2 wex idftpos4_1 wex idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel wb idftpos4_1 idftpos4_2 idftpos4_0 sup_set_class elvv idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel wb idftpos4_1 idftpos4_2 idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel wb idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop fdftpos4_1 cdm ccnv wcel wb idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_2 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 cdm wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop fdftpos4_1 cdm ccnv wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv cuni idftpos4_2 sup_set_class idftpos4_1 sup_set_class cop fdftpos4_1 cdm idftpos4_1 sup_set_class idftpos4_2 sup_set_class opswap eleq1i idftpos4_1 sup_set_class idftpos4_2 sup_set_class fdftpos4_1 cdm idftpos4_1 vex idftpos4_2 vex opelcnv bitr4i idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv cuni fdftpos4_1 cdm wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv wcel idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop fdftpos4_1 cdm ccnv wcel idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv cuni fdftpos4_1 cdm idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn ccnv idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn ccnv idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop wceq idftpos4_0 sup_set_class csn idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop csn idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop sneq cnveqd unieqd eleq1d idftpos4_0 sup_set_class idftpos4_1 sup_set_class idftpos4_2 sup_set_class cop fdftpos4_1 cdm ccnv eleq1 bibi12d mpbiri exlimivv sylbi biimpcd idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn elun1 syl6 syl idftpos4_0 sup_set_class c0 csn wcel idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel wi idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class c0 csn fdftpos4_1 cdm ccnv elun2 a1i idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_0 sup_set_class cvv cvv cxp wcel idftpos4_0 sup_set_class c0 csn wcel wo idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr simpll idftpos4_0 sup_set_class cvv cvv cxp c0 csn elun sylib mpjaod idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr wa idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_1 idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr simplr idftpos4_0 sup_set_class cvv cvv cxp c0 csn cun wcel idftpos4_2 sup_set_class idftpos4_0 sup_set_class csn ccnv cuni wceq wa idftpos4_2 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 wbr simpr eqbrtrrd jca sylanb idftpos4_1 sup_set_class cvv wcel idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 ctpos wbr idftpos4_0 sup_set_class fdftpos4_1 cdm ccnv c0 csn cun wcel idftpos4_0 sup_set_class csn ccnv cuni idftpos4_1 sup_set_class fdftpos4_1 wbr wa wb idftpos4_1 vex idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 cvv brtpos2 ax-mp sylibr idftpos4_0 sup_set_class idftpos4_1 sup_set_class fdftpos4_1 ctpos df-br sylib exlimiv sylbi relssi eqssi $.
$}
$( Value of the double transposition for a general class ` F ` .
       (Contributed by Mario Carneiro, 16-Sep-2015.) $)
${
	$v F $.
	$v x $.
	$v y $.
	$v z $.
	$v w $.
	$d x y $.
	$d x y $.
	$d w x y z F $.
	itpostpos_0 $f set x $.
	itpostpos_1 $f set y $.
	itpostpos_2 $f set z $.
	itpostpos_3 $f set w $.
	ftpostpos_0 $f class F $.
	tpostpos $p |- tpos tpos F = ( F i^i ( ( ( _V X. _V ) u. { (/) } ) X. _V ) ) $= itpostpos_3 itpostpos_2 ftpostpos_0 ctpos ctpos ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp cin ftpostpos_0 ctpos reltpos ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp cin cvv cvv cxp c0 csn cun cvv cxp wss cvv cvv cxp c0 csn cun cvv cxp wrel ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp cin wrel ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp inss2 cvv cvv cxp c0 csn cun cvv relxp ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp cin cvv cvv cxp c0 csn cun cvv cxp relss mp2 itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv c0 csn cun wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv cxp wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 ctpos ctpos wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp cin wbr itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class c0 csn wcel wo itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class c0 csn wcel wo wa itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv c0 csn cun wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv cxp wbr wa itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa wo itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel wa wo itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class c0 csn wcel wo itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class c0 csn wcel wo wa itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel wa itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel wa itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel wa itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa ftpostpos_0 ctpos cdm ccnv cvv cvv cxp itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wrel ftpostpos_0 ctpos cdm ccnv cvv cvv cxp wss ftpostpos_0 ctpos cdm relcnv ftpostpos_0 ctpos cdm ccnv df-rel mpbi itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr simpl sseldi itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel simpr itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel wa itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_1 wex itpostpos_0 wex itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr wb itpostpos_0 itpostpos_1 itpostpos_3 sup_set_class elvv itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr wb itpostpos_0 itpostpos_1 itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop ftpostpos_0 ctpos cdm wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop ftpostpos_0 ctpos cdm wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop ftpostpos_0 ctpos cdm ccnv wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop ftpostpos_0 ctpos cdm wcel itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop ftpostpos_0 ctpos cdm ccnv eleq1 itpostpos_0 sup_set_class itpostpos_1 sup_set_class ftpostpos_0 ctpos cdm itpostpos_0 vex itpostpos_1 vex opelcnv syl6bb itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class csn ccnv cuni itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class csn ccnv cuni itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop csn ccnv cuni itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class csn ccnv itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop csn ccnv itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop wceq itpostpos_3 sup_set_class csn itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop csn itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop sneq cnveqd unieqd itpostpos_0 sup_set_class itpostpos_1 sup_set_class opswap syl6eq breq1d anbi12d itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop ftpostpos_0 ctpos cdm wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop ftpostpos_0 ctpos cdm wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos itpostpos_1 sup_set_class itpostpos_0 sup_set_class opex itpostpos_2 vex breldm pm4.71ri itpostpos_2 sup_set_class cvv wcel itpostpos_1 sup_set_class itpostpos_0 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 wbr wb itpostpos_2 vex itpostpos_1 sup_set_class itpostpos_0 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 cvv brtpos ax-mp bitr3i syl6bb itpostpos_3 sup_set_class itpostpos_0 sup_set_class itpostpos_1 sup_set_class cop itpostpos_2 sup_set_class ftpostpos_0 breq1 bitr4d exlimivv sylbi itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr iba bitrd pm5.21nii itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr wa itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel wa itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr c0 itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr c0 itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr c0 itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni c0 itpostpos_2 sup_set_class ftpostpos_0 ctpos itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni c0 cuni c0 itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv c0 itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv c0 csn ccnv c0 itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn c0 csn itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class c0 itpostpos_3 sup_set_class c0 elsni sneqd cnveqd cnvsn0 syl6eq unieqd uni0 syl6eq breq1d itpostpos_2 sup_set_class cvv wcel c0 itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr c0 itpostpos_2 sup_set_class ftpostpos_0 wbr wb itpostpos_2 vex itpostpos_2 sup_set_class ftpostpos_0 cvv brtpos0 ax-mp syl6bb itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class c0 itpostpos_2 sup_set_class ftpostpos_0 itpostpos_3 sup_set_class c0 elsni breq1d bitr4d pm5.32i itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr ancom bitri orbi12i itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class c0 csn wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr andir itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class c0 csn wcel andi 3bitr4i itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv c0 csn cun wcel itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv wcel itpostpos_3 sup_set_class c0 csn wcel wo itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv c0 csn elun anbi1i itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv cxp wbr itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class c0 csn wcel wo itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 wbr itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv cxp wbr itpostpos_3 sup_set_class cvv cvv cxp c0 csn cun wcel itpostpos_3 sup_set_class cvv cvv cxp wcel itpostpos_3 sup_set_class c0 csn wcel wo itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv cxp wbr itpostpos_3 sup_set_class cvv cvv cxp c0 csn cun wcel itpostpos_2 sup_set_class cvv wcel itpostpos_2 vex itpostpos_3 sup_set_class itpostpos_2 sup_set_class cvv cvv cxp c0 csn cun cvv brxp mpbiran2 itpostpos_3 sup_set_class cvv cvv cxp c0 csn elun bitri anbi2i 3bitr4i itpostpos_2 sup_set_class cvv wcel itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 ctpos ctpos wbr itpostpos_3 sup_set_class ftpostpos_0 ctpos cdm ccnv c0 csn cun wcel itpostpos_3 sup_set_class csn ccnv cuni itpostpos_2 sup_set_class ftpostpos_0 ctpos wbr wa wb itpostpos_2 vex itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 ctpos cvv brtpos2 ax-mp itpostpos_3 sup_set_class itpostpos_2 sup_set_class ftpostpos_0 cvv cvv cxp c0 csn cun cvv cxp brin 3bitr4i eqbrriv $.
$}
$( Value of the double transposition for a relation on triples.
       (Contributed by Mario Carneiro, 16-Sep-2015.) $)
${
	$v F $.
	ftpostpos2_0 $f class F $.
	tpostpos2 $p |- ( ( Rel F /\ Rel dom F ) -> tpos tpos F = F ) $= ftpostpos2_0 wrel ftpostpos2_0 cdm wrel wa ftpostpos2_0 ctpos ctpos ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp cin ftpostpos2_0 ftpostpos2_0 tpostpos ftpostpos2_0 wrel ftpostpos2_0 cdm wrel wa ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp wss ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp cin ftpostpos2_0 wceq ftpostpos2_0 wrel ftpostpos2_0 cdm wrel wa ftpostpos2_0 cvv cvv cxp cvv cxp wss ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp wss ftpostpos2_0 relrelss ftpostpos2_0 cvv cvv cxp cvv cxp wss cvv cvv cxp cvv cxp cvv cvv cxp c0 csn cun cvv cxp wss ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp wss cvv cvv cxp cvv cvv cxp c0 csn cun wss cvv cvv cxp cvv cxp cvv cvv cxp c0 csn cun cvv cxp wss cvv cvv cxp c0 csn ssun1 cvv cvv cxp cvv cvv cxp c0 csn cun cvv xpss1 ax-mp ftpostpos2_0 cvv cvv cxp cvv cxp cvv cvv cxp c0 csn cun cvv cxp sstr mpan2 sylbi ftpostpos2_0 cvv cvv cxp c0 csn cun cvv cxp df-ss sylib syl5eq $.
$}
$( The domain of a transposition.  (Contributed by NM, 10-Sep-2015.) $)
${
	$v A $.
	$v F $.
	ftposfn2_0 $f class A $.
	ftposfn2_1 $f class F $.
	tposfn2 $p |- ( Rel A -> ( F Fn A -> tpos F Fn `' A ) ) $= ftposfn2_0 wrel ftposfn2_1 wfun ftposfn2_1 cdm ftposfn2_0 wceq wa ftposfn2_1 ctpos wfun ftposfn2_1 ctpos cdm ftposfn2_0 ccnv wceq wa ftposfn2_1 ftposfn2_0 wfn ftposfn2_1 ctpos ftposfn2_0 ccnv wfn ftposfn2_0 wrel ftposfn2_1 wfun ftposfn2_1 ctpos wfun ftposfn2_1 cdm ftposfn2_0 wceq ftposfn2_1 ctpos cdm ftposfn2_0 ccnv wceq ftposfn2_1 wfun ftposfn2_1 ctpos wfun wi ftposfn2_0 wrel ftposfn2_1 tposfun a1i ftposfn2_1 cdm ftposfn2_0 wceq ftposfn2_0 wrel ftposfn2_1 ctpos cdm ftposfn2_0 ccnv wceq ftposfn2_1 cdm ftposfn2_0 wceq ftposfn2_1 cdm wrel ftposfn2_1 ctpos cdm ftposfn2_1 cdm ccnv wceq ftposfn2_0 wrel ftposfn2_1 ctpos cdm ftposfn2_0 ccnv wceq ftposfn2_1 cdm wrel ftposfn2_1 ctpos cdm ftposfn2_1 cdm ccnv wceq wi ftposfn2_1 cdm ftposfn2_0 wceq ftposfn2_1 dmtpos a1i ftposfn2_1 cdm ftposfn2_0 releq ftposfn2_1 cdm ftposfn2_0 wceq ftposfn2_1 cdm ccnv ftposfn2_0 ccnv ftposfn2_1 ctpos cdm ftposfn2_1 cdm ftposfn2_0 cnveq eqeq2d 3imtr3d com12 anim12d ftposfn2_1 ftposfn2_0 df-fn ftposfn2_1 ctpos ftposfn2_0 ccnv df-fn 3imtr4g $.
$}
$( Condition for a surjective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	ftposfo2_0 $f class A $.
	ftposfo2_1 $f class B $.
	ftposfo2_2 $f class F $.
	tposfo2 $p |- ( Rel A -> ( F : A -onto-> B -> tpos F : `' A -onto-> B ) ) $= ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 crn ftposfo2_1 wceq wa ftposfo2_2 ctpos ftposfo2_0 ccnv wfn ftposfo2_2 ctpos crn ftposfo2_1 wceq wa ftposfo2_0 ftposfo2_1 ftposfo2_2 wfo ftposfo2_0 ccnv ftposfo2_1 ftposfo2_2 ctpos wfo ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 crn ftposfo2_1 wceq wa ftposfo2_2 ctpos ftposfo2_0 ccnv wfn ftposfo2_2 ctpos crn ftposfo2_1 wceq ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 ctpos ftposfo2_0 ccnv wfn ftposfo2_2 crn ftposfo2_1 wceq ftposfo2_0 ftposfo2_2 tposfn2 adantrd ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 crn ftposfo2_1 wceq ftposfo2_2 ctpos crn ftposfo2_1 wceq ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn wa ftposfo2_2 ctpos crn ftposfo2_1 wceq ftposfo2_2 crn ftposfo2_1 wceq ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn wa ftposfo2_2 ctpos crn ftposfo2_2 crn ftposfo2_1 ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn wa ftposfo2_2 cdm wrel ftposfo2_2 ctpos crn ftposfo2_2 crn wceq ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 cdm wrel ftposfo2_0 wrel ftposfo2_2 ftposfo2_0 wfn ftposfo2_2 cdm ftposfo2_0 ftposfo2_0 ftposfo2_2 fndm releqd biimparc ftposfo2_2 rntpos syl eqeq1d biimprd expimpd jcad ftposfo2_0 ftposfo2_1 ftposfo2_2 df-fo ftposfo2_0 ccnv ftposfo2_1 ftposfo2_2 ctpos df-fo 3imtr4g $.
$}
$( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	ftposf2_0 $f class A $.
	ftposf2_1 $f class B $.
	ftposf2_2 $f class F $.
	tposf2 $p |- ( Rel A -> ( F : A --> B -> tpos F : `' A --> B ) ) $= ftposf2_0 wrel ftposf2_0 ftposf2_1 ftposf2_2 wf ftposf2_0 ccnv ftposf2_1 ftposf2_2 ctpos wf ftposf2_0 wrel ftposf2_0 ftposf2_1 ftposf2_2 wf wa ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos wf ftposf2_2 crn ftposf2_1 wss ftposf2_0 ccnv ftposf2_1 ftposf2_2 ctpos wf ftposf2_0 wrel ftposf2_0 ftposf2_1 ftposf2_2 wf wa ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos wfo ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos wf ftposf2_0 wrel ftposf2_0 ftposf2_1 ftposf2_2 wf ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos wfo ftposf2_0 ftposf2_1 ftposf2_2 wf ftposf2_0 ftposf2_2 crn ftposf2_2 wfo ftposf2_0 wrel ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos wfo ftposf2_0 ftposf2_1 ftposf2_2 wf ftposf2_2 ftposf2_0 wfn ftposf2_0 ftposf2_2 crn ftposf2_2 wfo ftposf2_0 ftposf2_1 ftposf2_2 ffn ftposf2_0 ftposf2_2 dffn4 sylib ftposf2_0 ftposf2_2 crn ftposf2_2 tposfo2 syl5 imp ftposf2_0 ccnv ftposf2_2 crn ftposf2_2 ctpos fof syl ftposf2_0 ftposf2_1 ftposf2_2 wf ftposf2_2 crn ftposf2_1 wss ftposf2_0 wrel ftposf2_0 ftposf2_1 ftposf2_2 frn adantl ftposf2_0 ccnv ftposf2_2 crn ftposf2_1 ftposf2_2 ctpos fss syl2anc ex $.
$}
$( Condition for an injective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	$v x $.
	$d x A $.
	$d x B $.
	$d x F $.
	itposf12_0 $f set x $.
	ftposf12_0 $f class A $.
	ftposf12_1 $f class B $.
	ftposf12_2 $f class F $.
	tposf12 $p |- ( Rel A -> ( F : A -1-1-> B -> tpos F : `' A -1-1-> B ) ) $= ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 ftposf12_0 ccnv ftposf12_1 ftposf12_2 ctpos wf1 ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ccnv ftposf12_1 ftposf12_2 ctpos wf1 ftposf12_0 ccnv ftposf12_1 ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt ccom wf1 ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ftposf12_1 ftposf12_2 wf1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv ftposf12_1 ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt ccom wf1 ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 simpr ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ccnv ftposf12_0 ccnv ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv wrel ftposf12_0 ccnv ftposf12_0 ccnv ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1o ftposf12_0 ccnv ftposf12_0 ccnv ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 relcnv itposf12_0 ftposf12_0 ccnv cnvf1o ftposf12_0 ccnv ftposf12_0 ccnv ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt f1of1 mp2b ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ccnv ccnv ftposf12_0 wceq ftposf12_0 ccnv ftposf12_0 ccnv ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 wb ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 wrel ftposf12_0 ccnv ccnv ftposf12_0 wceq ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 simpl ftposf12_0 dfrel2 sylib ftposf12_0 ccnv ccnv ftposf12_0 ftposf12_0 ccnv itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt f1eq3 syl mpbii ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_2 cdm ccnv ftposf12_0 ccnv wceq itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wceq ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt wf1 wb ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_2 cdm ftposf12_0 ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_0 ftposf12_1 ftposf12_2 wf1 ftposf12_2 cdm ftposf12_0 wceq ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 simpr ftposf12_0 ftposf12_1 ftposf12_2 f1dm syl cnveqd itposf12_0 ftposf12_2 cdm ccnv ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni mpteq1 ftposf12_0 ccnv ftposf12_0 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt itposf12_0 ftposf12_0 ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt f1eq1 3syl mpbird ftposf12_0 ccnv ftposf12_0 ftposf12_1 ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt f1co syl2anc ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 wa ftposf12_2 cdm wrel ftposf12_2 ctpos ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt ccom wceq ftposf12_0 ccnv ftposf12_1 ftposf12_2 ctpos wf1 ftposf12_0 ccnv ftposf12_1 ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt ccom wf1 wb ftposf12_0 ftposf12_1 ftposf12_2 wf1 ftposf12_2 cdm wrel ftposf12_0 wrel ftposf12_0 ftposf12_1 ftposf12_2 wf1 ftposf12_2 cdm ftposf12_0 ftposf12_0 ftposf12_1 ftposf12_2 f1dm releqd biimparc itposf12_0 ftposf12_2 dftpos2 ftposf12_0 ccnv ftposf12_1 ftposf12_2 ctpos ftposf12_2 itposf12_0 ftposf12_2 cdm ccnv itposf12_0 sup_set_class csn ccnv cuni cmpt ccom f1eq1 3syl mpbird ex $.
$}
$( Condition of a bijective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	ftposf1o2_0 $f class A $.
	ftposf1o2_1 $f class B $.
	ftposf1o2_2 $f class F $.
	tposf1o2 $p |- ( Rel A -> ( F : A -1-1-onto-> B -> tpos F : `' A -1-1-onto-> B ) ) $= ftposf1o2_0 wrel ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 wf1 ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 wfo wa ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos wf1 ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos wfo wa ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 wf1o ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos wf1o ftposf1o2_0 wrel ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 wf1 ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos wf1 ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 wfo ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos wfo ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 tposf12 ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 tposfo2 anim12d ftposf1o2_0 ftposf1o2_1 ftposf1o2_2 df-f1o ftposf1o2_0 ccnv ftposf1o2_1 ftposf1o2_2 ctpos df-f1o 3imtr4g $.
$}
$( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	ftposfo_0 $f class A $.
	ftposfo_1 $f class B $.
	ftposfo_2 $f class C $.
	ftposfo_3 $f class F $.
	tposfo $p |- ( F : ( A X. B ) -onto-> C -> tpos F : ( B X. A ) -onto-> C ) $= ftposfo_0 ftposfo_1 cxp ftposfo_2 ftposfo_3 wfo ftposfo_0 ftposfo_1 cxp ccnv ftposfo_2 ftposfo_3 ctpos wfo ftposfo_1 ftposfo_0 cxp ftposfo_2 ftposfo_3 ctpos wfo ftposfo_0 ftposfo_1 cxp wrel ftposfo_0 ftposfo_1 cxp ftposfo_2 ftposfo_3 wfo ftposfo_0 ftposfo_1 cxp ccnv ftposfo_2 ftposfo_3 ctpos wfo wi ftposfo_0 ftposfo_1 relxp ftposfo_0 ftposfo_1 cxp ftposfo_2 ftposfo_3 tposfo2 ax-mp ftposfo_0 ftposfo_1 cxp ccnv ftposfo_1 ftposfo_0 cxp wceq ftposfo_0 ftposfo_1 cxp ccnv ftposfo_2 ftposfo_3 ctpos wfo ftposfo_1 ftposfo_0 cxp ftposfo_2 ftposfo_3 ctpos wfo wb ftposfo_0 ftposfo_1 cnvxp ftposfo_0 ftposfo_1 cxp ccnv ftposfo_1 ftposfo_0 cxp ftposfo_2 ftposfo_3 ctpos foeq2 ax-mp sylib $.
$}
$( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	ftposf_0 $f class A $.
	ftposf_1 $f class B $.
	ftposf_2 $f class C $.
	ftposf_3 $f class F $.
	tposf $p |- ( F : ( A X. B ) --> C -> tpos F : ( B X. A ) --> C ) $= ftposf_0 ftposf_1 cxp ftposf_2 ftposf_3 wf ftposf_0 ftposf_1 cxp ccnv ftposf_2 ftposf_3 ctpos wf ftposf_1 ftposf_0 cxp ftposf_2 ftposf_3 ctpos wf ftposf_0 ftposf_1 cxp wrel ftposf_0 ftposf_1 cxp ftposf_2 ftposf_3 wf ftposf_0 ftposf_1 cxp ccnv ftposf_2 ftposf_3 ctpos wf wi ftposf_0 ftposf_1 relxp ftposf_0 ftposf_1 cxp ftposf_2 ftposf_3 tposf2 ax-mp ftposf_0 ftposf_1 cxp ccnv ftposf_1 ftposf_0 cxp ftposf_2 ftposf_3 ctpos ftposf_0 ftposf_1 cnvxp feq2i sylib $.
$}
$( Functionality of a transposition.  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
${
	$v A $.
	$v B $.
	$v F $.
	ftposfn_0 $f class A $.
	ftposfn_1 $f class B $.
	ftposfn_2 $f class F $.
	tposfn $p |- ( F Fn ( A X. B ) -> tpos F Fn ( B X. A ) ) $= ftposfn_0 ftposfn_1 cxp cvv ftposfn_2 wf ftposfn_1 ftposfn_0 cxp cvv ftposfn_2 ctpos wf ftposfn_2 ftposfn_0 ftposfn_1 cxp wfn ftposfn_2 ctpos ftposfn_1 ftposfn_0 cxp wfn ftposfn_0 ftposfn_1 cvv ftposfn_2 tposf ftposfn_0 ftposfn_1 cxp ftposfn_2 dffn2 ftposfn_1 ftposfn_0 cxp ftposfn_2 ctpos dffn2 3imtr4i $.
$}
$( Transposition of the empty set.  (Contributed by NM, 10-Sep-2015.) $)
${
	tpos0 $p |- tpos (/) = (/) $= c0 ctpos c0 wfn c0 ctpos c0 wceq c0 ctpos c0 ccnv wfn c0 ctpos c0 wfn c0 wrel c0 c0 wfn c0 ctpos c0 ccnv wfn rel0 c0 c0 wfn c0 c0 wceq c0 eqid c0 fn0 mpbir c0 c0 tposfn2 mp2 c0 ccnv c0 c0 ctpos cnv0 fneq2i mpbi c0 ctpos fn0 mpbi $.
$}
$( Transposition of a composition.  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
${
	$v F $.
	$v G $.
	$v x $.
	$d x F $.
	$d x G $.
	itposco_0 $f set x $.
	ftposco_0 $f class F $.
	ftposco_1 $f class G $.
	tposco $p |- tpos ( F o. G ) = ( F o. tpos G ) $= ftposco_0 ftposco_1 ccom itposco_0 cvv cvv cxp c0 csn cun itposco_0 sup_set_class csn ccnv cuni cmpt ccom ftposco_0 ftposco_1 itposco_0 cvv cvv cxp c0 csn cun itposco_0 sup_set_class csn ccnv cuni cmpt ccom ccom ftposco_0 ftposco_1 ccom ctpos ftposco_0 ftposco_1 ctpos ccom ftposco_0 ftposco_1 itposco_0 cvv cvv cxp c0 csn cun itposco_0 sup_set_class csn ccnv cuni cmpt coass itposco_0 ftposco_0 ftposco_1 ccom dftpos4 ftposco_1 ctpos ftposco_1 itposco_0 cvv cvv cxp c0 csn cun itposco_0 sup_set_class csn ccnv cuni cmpt ccom ftposco_0 itposco_0 ftposco_1 dftpos4 coeq2i 3eqtr4i $.
$}
$( Two ways to say a function is symmetric.  (Contributed by Mario
       Carneiro, 4-Oct-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v F $.
	$d x y A $.
	$d x y $.
	$d x y F $.
	ftpossym_0 $f set x $.
	ftpossym_1 $f set y $.
	ftpossym_2 $f class A $.
	ftpossym_3 $f class F $.
	tpossym $p |- ( F Fn ( A X. A ) -> ( tpos F = F <-> A. x e. A A. y e. A ( x F y ) = ( y F x ) ) ) $= ftpossym_3 ftpossym_2 ftpossym_2 cxp wfn ftpossym_3 ctpos ftpossym_3 wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co wceq ftpossym_1 ftpossym_2 wral ftpossym_0 ftpossym_2 wral ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co ftpossym_1 sup_set_class ftpossym_0 sup_set_class ftpossym_3 co wceq ftpossym_1 ftpossym_2 wral ftpossym_0 ftpossym_2 wral ftpossym_3 ctpos ftpossym_2 ftpossym_2 cxp wfn ftpossym_3 ftpossym_2 ftpossym_2 cxp wfn ftpossym_3 ctpos ftpossym_3 wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co wceq ftpossym_1 ftpossym_2 wral ftpossym_0 ftpossym_2 wral wb ftpossym_2 ftpossym_2 ftpossym_3 tposfn ftpossym_0 ftpossym_1 ftpossym_2 ftpossym_2 ftpossym_3 ctpos ftpossym_3 eqfnov2 mpancom ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co ftpossym_1 sup_set_class ftpossym_0 sup_set_class ftpossym_3 co wceq ftpossym_0 ftpossym_1 ftpossym_2 ftpossym_2 ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co ftpossym_1 sup_set_class ftpossym_0 sup_set_class ftpossym_3 co wceq ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co eqcom ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ctpos co ftpossym_1 sup_set_class ftpossym_0 sup_set_class ftpossym_3 co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 co ftpossym_0 sup_set_class ftpossym_1 sup_set_class ftpossym_3 ovtpos eqeq2i bitri 2ralbii syl6bb $.
$}
$( Equality theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	$v G $.
	ftposeqi_0 $f class F $.
	ftposeqi_1 $f class G $.
	etposeqi_0 $e |- F = G $.
	tposeqi $p |- tpos F = tpos G $= ftposeqi_0 ftposeqi_1 wceq ftposeqi_0 ctpos ftposeqi_1 ctpos wceq etposeqi_0 ftposeqi_0 ftposeqi_1 tposeq ax-mp $.
$}
$( A transposition is a set.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v F $.
	ftposex_0 $f class F $.
	etposex_0 $e |- F e. _V $.
	tposex $p |- tpos F e. _V $= ftposex_0 cvv wcel ftposex_0 ctpos cvv wcel etposex_0 ftposex_0 cvv tposexg ax-mp $.
$}
$( Hypothesis builder for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
${
	$v x $.
	$v F $.
	$v y $.
	$d x y $.
	$d y F $.
	inftpos_0 $f set y $.
	fnftpos_0 $f set x $.
	fnftpos_1 $f class F $.
	enftpos_0 $e |- F/_ x F $.
	nftpos $p |- F/_ x tpos F $= fnftpos_0 fnftpos_1 ctpos fnftpos_1 inftpos_0 cvv cvv cxp c0 csn cun inftpos_0 sup_set_class csn ccnv cuni cmpt ccom inftpos_0 fnftpos_1 dftpos4 fnftpos_0 fnftpos_1 inftpos_0 cvv cvv cxp c0 csn cun inftpos_0 sup_set_class csn ccnv cuni cmpt enftpos_0 fnftpos_0 inftpos_0 cvv cvv cxp c0 csn cun inftpos_0 sup_set_class csn ccnv cuni cmpt nfcv nfco nfcxfr $.
$}
$( Transposition of a class of ordered triples.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$v z $.
	$v F $.
	$v a $.
	$v b $.
	$v c $.
	$d a b c x y z $.
	$d a b c ph $.
	itposoprab_0 $f set a $.
	itposoprab_1 $f set b $.
	itposoprab_2 $f set c $.
	ftposoprab_0 $f wff ph $.
	ftposoprab_1 $f set x $.
	ftposoprab_2 $f set y $.
	ftposoprab_3 $f set z $.
	ftposoprab_4 $f class F $.
	etposoprab_0 $e |- F = { <. <. x , y >. , z >. | ph } $.
	tposoprab $p |- tpos F = { <. <. y , x >. , z >. | ph } $= ftposoprab_4 ctpos ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab ctpos itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_0 itposoprab_1 itposoprab_2 coprab ftposoprab_0 ftposoprab_2 ftposoprab_1 ftposoprab_3 coprab ftposoprab_4 ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab etposoprab_0 tposeqi ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab cdm wrel ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab ctpos itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_0 itposoprab_1 itposoprab_2 coprab wceq ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 reldmoprab itposoprab_0 itposoprab_1 itposoprab_2 ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab dftpos3 ax-mp itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_0 itposoprab_1 itposoprab_2 coprab ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_2 ftposoprab_1 itposoprab_2 coprab ftposoprab_0 ftposoprab_2 ftposoprab_1 ftposoprab_3 coprab itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_0 itposoprab_1 itposoprab_2 ftposoprab_2 ftposoprab_1 ftposoprab_2 itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab ftposoprab_2 itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop nfcv ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 nfoprab2 ftposoprab_2 itposoprab_2 sup_set_class nfcv nfbr ftposoprab_1 itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab ftposoprab_1 itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop nfcv ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 nfoprab1 ftposoprab_1 itposoprab_2 sup_set_class nfcv nfbr ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_0 nfv ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr itposoprab_1 nfv itposoprab_0 sup_set_class ftposoprab_2 sup_set_class wceq itposoprab_1 sup_set_class ftposoprab_1 sup_set_class wceq wa itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab itposoprab_1 sup_set_class ftposoprab_1 sup_set_class wceq itposoprab_0 sup_set_class ftposoprab_2 sup_set_class wceq itposoprab_1 sup_set_class itposoprab_0 sup_set_class cop ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop wceq itposoprab_1 sup_set_class itposoprab_0 sup_set_class ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class opeq12 ancoms breq1d cbvoprab12 ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_0 ftposoprab_2 ftposoprab_1 itposoprab_2 ftposoprab_3 ftposoprab_3 ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab ftposoprab_3 ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop nfcv ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 nfoprab3 ftposoprab_3 itposoprab_2 sup_set_class nfcv nfbr ftposoprab_0 itposoprab_2 nfv itposoprab_2 sup_set_class ftposoprab_3 sup_set_class wceq ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop itposoprab_2 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop ftposoprab_3 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_0 itposoprab_2 sup_set_class ftposoprab_3 sup_set_class ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab breq2 ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop ftposoprab_3 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wbr ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop ftposoprab_3 sup_set_class cop ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab wcel ftposoprab_0 ftposoprab_1 sup_set_class ftposoprab_2 sup_set_class cop ftposoprab_3 sup_set_class ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 coprab df-br ftposoprab_0 ftposoprab_1 ftposoprab_2 ftposoprab_3 oprabid bitri syl6bb cbvoprab3 eqtri 3eqtri $.
$}
$( Transposition of a two-argument mapping.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v F $.
	$v z $.
	$d x y z $.
	$d z A $.
	$d z B $.
	$d z C $.
	itposmpt2_0 $f set z $.
	ftposmpt2_0 $f set x $.
	ftposmpt2_1 $f set y $.
	ftposmpt2_2 $f class A $.
	ftposmpt2_3 $f class B $.
	ftposmpt2_4 $f class C $.
	ftposmpt2_5 $f class F $.
	etposmpt2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	tposmpt2 $p |- tpos F = ( y e. B , x e. A |-> C ) $= ftposmpt2_5 ctpos ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ftposmpt2_0 sup_set_class ftposmpt2_2 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_1 ftposmpt2_0 itposmpt2_0 coprab ftposmpt2_1 ftposmpt2_0 ftposmpt2_3 ftposmpt2_2 ftposmpt2_4 cmpt2 ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ftposmpt2_0 sup_set_class ftposmpt2_2 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_0 ftposmpt2_1 itposmpt2_0 ftposmpt2_5 ftposmpt2_5 ftposmpt2_0 ftposmpt2_1 ftposmpt2_2 ftposmpt2_3 ftposmpt2_4 cmpt2 ftposmpt2_0 sup_set_class ftposmpt2_2 wcel ftposmpt2_1 sup_set_class ftposmpt2_3 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_0 ftposmpt2_1 itposmpt2_0 coprab ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ftposmpt2_0 sup_set_class ftposmpt2_2 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_0 ftposmpt2_1 itposmpt2_0 coprab etposmpt2_0 ftposmpt2_0 ftposmpt2_1 itposmpt2_0 ftposmpt2_2 ftposmpt2_3 ftposmpt2_4 df-mpt2 ftposmpt2_0 sup_set_class ftposmpt2_2 wcel ftposmpt2_1 sup_set_class ftposmpt2_3 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ftposmpt2_0 sup_set_class ftposmpt2_2 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq wa ftposmpt2_0 ftposmpt2_1 itposmpt2_0 ftposmpt2_0 sup_set_class ftposmpt2_2 wcel ftposmpt2_1 sup_set_class ftposmpt2_3 wcel wa ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ftposmpt2_0 sup_set_class ftposmpt2_2 wcel wa itposmpt2_0 sup_set_class ftposmpt2_4 wceq ftposmpt2_0 sup_set_class ftposmpt2_2 wcel ftposmpt2_1 sup_set_class ftposmpt2_3 wcel ancom anbi1i oprabbii 3eqtri tposoprab ftposmpt2_1 ftposmpt2_0 itposmpt2_0 ftposmpt2_3 ftposmpt2_2 ftposmpt2_4 df-mpt2 eqtr4i $.
$}

