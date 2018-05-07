$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Miscellaneous_theorems_of_propositional_calculus.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Abbreviated conjunction and disjunction of three wff's

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Extend wff definition to include 3-way disjunction ('or'). $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fw3o_0 $f wff ph $.
	fw3o_1 $f wff ps $.
	fw3o_2 $f wff ch $.
	w3o $a wff ( ph \/ ps \/ ch ) $.
$}
$( Extend wff definition to include 3-way conjunction ('and'). $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fw3a_0 $f wff ph $.
	fw3a_1 $f wff ps $.
	fw3a_2 $f wff ch $.
	w3a $a wff ( ph /\ ps /\ ch ) $.
$}
$( These abbreviations help eliminate parentheses to aid readability. $)
$( Define disjunction ('or') of three wff's.  Definition *2.33 of
     [WhiteheadRussell] p. 105.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ orass .  (Contributed by NM,
     8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fdf-3or_0 $f wff ph $.
	fdf-3or_1 $f wff ps $.
	fdf-3or_2 $f wff ch $.
	df-3or $a |- ( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) ) $.
$}
$( Define conjunction ('and') of three wff's.  Definition *4.34 of
     [WhiteheadRussell] p. 118.  This abbreviation reduces the number of
     parentheses and emphasizes that the order of bracketing is not important
     by virtue of the associative law ~ anass .  (Contributed by NM,
     8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fdf-3an_0 $f wff ph $.
	fdf-3an_1 $f wff ps $.
	fdf-3an_2 $f wff ch $.
	df-3an $a |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) ) $.
$}
$( Associative law for triple disjunction.  (Contributed by NM,
     8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3orass_0 $f wff ph $.
	f3orass_1 $f wff ps $.
	f3orass_2 $f wff ch $.
	3orass $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ) $= f3orass_0 f3orass_1 f3orass_2 w3o f3orass_0 f3orass_1 wo f3orass_2 wo f3orass_0 f3orass_1 f3orass_2 wo wo f3orass_0 f3orass_1 f3orass_2 df-3or f3orass_0 f3orass_1 f3orass_2 orass bitri $.
$}
$( Associative law for triple conjunction.  (Contributed by NM,
     8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anass_0 $f wff ph $.
	f3anass_1 $f wff ps $.
	f3anass_2 $f wff ch $.
	3anass $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ) $= f3anass_0 f3anass_1 f3anass_2 w3a f3anass_0 f3anass_1 wa f3anass_2 wa f3anass_0 f3anass_1 f3anass_2 wa wa f3anass_0 f3anass_1 f3anass_2 df-3an f3anass_0 f3anass_1 f3anass_2 anass bitri $.
$}
$( Rotation law for triple conjunction.  (Contributed by NM, 8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anrot_0 $f wff ph $.
	f3anrot_1 $f wff ps $.
	f3anrot_2 $f wff ch $.
	3anrot $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ch /\ ph ) ) $= f3anrot_0 f3anrot_1 f3anrot_2 wa wa f3anrot_1 f3anrot_2 wa f3anrot_0 wa f3anrot_0 f3anrot_1 f3anrot_2 w3a f3anrot_1 f3anrot_2 f3anrot_0 w3a f3anrot_0 f3anrot_1 f3anrot_2 wa ancom f3anrot_0 f3anrot_1 f3anrot_2 3anass f3anrot_1 f3anrot_2 f3anrot_0 df-3an 3bitr4i $.
$}
$( Rotation law for triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3orrot_0 $f wff ph $.
	f3orrot_1 $f wff ps $.
	f3orrot_2 $f wff ch $.
	3orrot $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ) $= f3orrot_0 f3orrot_1 f3orrot_2 wo wo f3orrot_1 f3orrot_2 wo f3orrot_0 wo f3orrot_0 f3orrot_1 f3orrot_2 w3o f3orrot_1 f3orrot_2 f3orrot_0 w3o f3orrot_0 f3orrot_1 f3orrot_2 wo orcom f3orrot_0 f3orrot_1 f3orrot_2 3orass f3orrot_1 f3orrot_2 f3orrot_0 df-3or 3bitr4i $.
$}
$( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3ancoma_0 $f wff ph $.
	f3ancoma_1 $f wff ps $.
	f3ancoma_2 $f wff ch $.
	3ancoma $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ph /\ ch ) ) $= f3ancoma_0 f3ancoma_1 wa f3ancoma_2 wa f3ancoma_1 f3ancoma_0 wa f3ancoma_2 wa f3ancoma_0 f3ancoma_1 f3ancoma_2 w3a f3ancoma_1 f3ancoma_0 f3ancoma_2 w3a f3ancoma_0 f3ancoma_1 wa f3ancoma_1 f3ancoma_0 wa f3ancoma_2 f3ancoma_0 f3ancoma_1 ancom anbi1i f3ancoma_0 f3ancoma_1 f3ancoma_2 df-3an f3ancoma_1 f3ancoma_0 f3ancoma_2 df-3an 3bitr4i $.
$}
$( Commutation law for triple disjunction.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3orcoma_0 $f wff ph $.
	f3orcoma_1 $f wff ps $.
	f3orcoma_2 $f wff ch $.
	3orcoma $p |- ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) ) $= f3orcoma_0 f3orcoma_1 f3orcoma_2 wo wo f3orcoma_1 f3orcoma_0 f3orcoma_2 wo wo f3orcoma_0 f3orcoma_1 f3orcoma_2 w3o f3orcoma_1 f3orcoma_0 f3orcoma_2 w3o f3orcoma_0 f3orcoma_1 f3orcoma_2 or12 f3orcoma_0 f3orcoma_1 f3orcoma_2 3orass f3orcoma_1 f3orcoma_0 f3orcoma_2 3orass 3bitr4i $.
$}
$( Commutation law for triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3ancomb_0 $f wff ph $.
	f3ancomb_1 $f wff ps $.
	f3ancomb_2 $f wff ch $.
	3ancomb $p |- ( ( ph /\ ps /\ ch ) <-> ( ph /\ ch /\ ps ) ) $= f3ancomb_0 f3ancomb_1 f3ancomb_2 w3a f3ancomb_1 f3ancomb_0 f3ancomb_2 w3a f3ancomb_0 f3ancomb_2 f3ancomb_1 w3a f3ancomb_0 f3ancomb_1 f3ancomb_2 3ancoma f3ancomb_1 f3ancomb_0 f3ancomb_2 3anrot bitri $.
$}
$( Commutation law for triple disjunction.  (Contributed by Scott Fenton,
     20-Apr-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3orcomb_0 $f wff ph $.
	f3orcomb_1 $f wff ps $.
	f3orcomb_2 $f wff ch $.
	3orcomb $p |- ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ) $= f3orcomb_0 f3orcomb_1 f3orcomb_2 wo wo f3orcomb_0 f3orcomb_2 f3orcomb_1 wo wo f3orcomb_0 f3orcomb_1 f3orcomb_2 w3o f3orcomb_0 f3orcomb_2 f3orcomb_1 w3o f3orcomb_1 f3orcomb_2 wo f3orcomb_2 f3orcomb_1 wo f3orcomb_0 f3orcomb_1 f3orcomb_2 orcom orbi2i f3orcomb_0 f3orcomb_1 f3orcomb_2 3orass f3orcomb_0 f3orcomb_2 f3orcomb_1 3orass 3bitr4i $.
$}
$( Reversal law for triple conjunction.  (Contributed by NM, 21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anrev_0 $f wff ph $.
	f3anrev_1 $f wff ps $.
	f3anrev_2 $f wff ch $.
	3anrev $p |- ( ( ph /\ ps /\ ch ) <-> ( ch /\ ps /\ ph ) ) $= f3anrev_0 f3anrev_1 f3anrev_2 w3a f3anrev_1 f3anrev_0 f3anrev_2 w3a f3anrev_2 f3anrev_1 f3anrev_0 w3a f3anrev_0 f3anrev_1 f3anrev_2 3ancoma f3anrev_2 f3anrev_1 f3anrev_0 3anrot bitr4i $.
$}
$( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anan32_0 $f wff ph $.
	f3anan32_1 $f wff ps $.
	f3anan32_2 $f wff ch $.
	3anan32 $p |- ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ch ) /\ ps ) ) $= f3anan32_0 f3anan32_1 f3anan32_2 w3a f3anan32_0 f3anan32_1 wa f3anan32_2 wa f3anan32_0 f3anan32_2 wa f3anan32_1 wa f3anan32_0 f3anan32_1 f3anan32_2 df-3an f3anan32_0 f3anan32_1 f3anan32_2 an32 bitri $.
$}
$( Convert triple conjunction to conjunction, then commute.  (Contributed by
     Jonathan Ben-Naim, 3-Jun-2011.)  (Proof shortened by Andrew Salmon,
     14-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anan12_0 $f wff ph $.
	f3anan12_1 $f wff ps $.
	f3anan12_2 $f wff ch $.
	3anan12 $p |- ( ( ph /\ ps /\ ch ) <-> ( ps /\ ( ph /\ ch ) ) ) $= f3anan12_0 f3anan12_1 f3anan12_2 w3a f3anan12_1 f3anan12_0 f3anan12_2 w3a f3anan12_1 f3anan12_0 f3anan12_2 wa wa f3anan12_0 f3anan12_1 f3anan12_2 3ancoma f3anan12_1 f3anan12_0 f3anan12_2 3anass bitri $.
$}
$( Triple conjunction expressed in terms of triple disjunction.  (Contributed
     by Jeff Hankins, 15-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anor_0 $f wff ph $.
	f3anor_1 $f wff ps $.
	f3anor_2 $f wff ch $.
	3anor $p |- ( ( ph /\ ps /\ ch ) <-> -. ( -. ph \/ -. ps \/ -. ch ) ) $= f3anor_0 f3anor_1 f3anor_2 w3a f3anor_0 f3anor_1 wa f3anor_2 wa f3anor_0 wn f3anor_1 wn f3anor_2 wn w3o wn f3anor_0 f3anor_1 f3anor_2 df-3an f3anor_0 f3anor_1 wa f3anor_2 wa f3anor_0 wn f3anor_1 wn wo f3anor_2 wn wo f3anor_0 wn f3anor_1 wn f3anor_2 wn w3o f3anor_0 f3anor_1 wa f3anor_2 wa f3anor_0 f3anor_1 wa wn f3anor_2 wn wo f3anor_0 wn f3anor_1 wn wo f3anor_2 wn wo f3anor_0 f3anor_1 wa f3anor_2 anor f3anor_0 f3anor_1 wa wn f3anor_0 wn f3anor_1 wn wo f3anor_2 wn f3anor_0 f3anor_1 ianor orbi1i xchbinx f3anor_0 wn f3anor_1 wn f3anor_2 wn df-3or xchbinxr bitri $.
$}
$( Negated triple conjunction expressed in terms of triple disjunction.
     (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3ianor_0 $f wff ph $.
	f3ianor_1 $f wff ps $.
	f3ianor_2 $f wff ch $.
	3ianor $p |- ( -. ( ph /\ ps /\ ch ) <-> ( -. ph \/ -. ps \/ -. ch ) ) $= f3ianor_0 wn f3ianor_1 wn f3ianor_2 wn w3o f3ianor_0 f3ianor_1 f3ianor_2 w3a wn f3ianor_0 f3ianor_1 f3ianor_2 w3a f3ianor_0 wn f3ianor_1 wn f3ianor_2 wn w3o f3ianor_0 f3ianor_1 f3ianor_2 3anor con2bii bicomi $.
$}
$( Negated triple disjunction as triple conjunction.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3ioran_0 $f wff ph $.
	f3ioran_1 $f wff ps $.
	f3ioran_2 $f wff ch $.
	3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $= f3ioran_0 f3ioran_1 wo wn f3ioran_2 wn wa f3ioran_0 wn f3ioran_1 wn wa f3ioran_2 wn wa f3ioran_0 f3ioran_1 f3ioran_2 w3o wn f3ioran_0 wn f3ioran_1 wn f3ioran_2 wn w3a f3ioran_0 f3ioran_1 wo wn f3ioran_0 wn f3ioran_1 wn wa f3ioran_2 wn f3ioran_0 f3ioran_1 ioran anbi1i f3ioran_0 f3ioran_1 wo f3ioran_2 wo f3ioran_0 f3ioran_1 wo wn f3ioran_2 wn wa f3ioran_0 f3ioran_1 f3ioran_2 w3o f3ioran_0 f3ioran_1 wo f3ioran_2 ioran f3ioran_0 f3ioran_1 f3ioran_2 df-3or xchnxbir f3ioran_0 wn f3ioran_1 wn f3ioran_2 wn df-3an 3bitr4i $.
$}
$( Triple disjunction in terms of triple conjunction.  (Contributed by NM,
     8-Oct-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3oran_0 $f wff ph $.
	f3oran_1 $f wff ps $.
	f3oran_2 $f wff ch $.
	3oran $p |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) ) $= f3oran_0 wn f3oran_1 wn f3oran_2 wn w3a wn f3oran_0 f3oran_1 f3oran_2 w3o f3oran_0 f3oran_1 f3oran_2 w3o f3oran_0 wn f3oran_1 wn f3oran_2 wn w3a f3oran_0 f3oran_1 f3oran_2 3ioran con1bii bicomi $.
$}
$( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3simpa_0 $f wff ph $.
	f3simpa_1 $f wff ps $.
	f3simpa_2 $f wff ch $.
	3simpa $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ps ) ) $= f3simpa_0 f3simpa_1 f3simpa_2 w3a f3simpa_0 f3simpa_1 wa f3simpa_2 f3simpa_0 f3simpa_1 f3simpa_2 df-3an simplbi $.
$}
$( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3simpb_0 $f wff ph $.
	f3simpb_1 $f wff ps $.
	f3simpb_2 $f wff ch $.
	3simpb $p |- ( ( ph /\ ps /\ ch ) -> ( ph /\ ch ) ) $= f3simpb_0 f3simpb_1 f3simpb_2 w3a f3simpb_0 f3simpb_2 f3simpb_1 w3a f3simpb_0 f3simpb_2 wa f3simpb_0 f3simpb_1 f3simpb_2 3ancomb f3simpb_0 f3simpb_2 f3simpb_1 3simpa sylbi $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 21-Apr-1994.)
     (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3simpc_0 $f wff ph $.
	f3simpc_1 $f wff ps $.
	f3simpc_2 $f wff ch $.
	3simpc $p |- ( ( ph /\ ps /\ ch ) -> ( ps /\ ch ) ) $= f3simpc_0 f3simpc_1 f3simpc_2 w3a f3simpc_1 f3simpc_2 f3simpc_0 w3a f3simpc_1 f3simpc_2 wa f3simpc_0 f3simpc_1 f3simpc_2 3anrot f3simpc_1 f3simpc_2 f3simpc_0 3simpa sylbi $.
$}
$( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp1_0 $f wff ph $.
	fsimp1_1 $f wff ps $.
	fsimp1_2 $f wff ch $.
	simp1 $p |- ( ( ph /\ ps /\ ch ) -> ph ) $= fsimp1_0 fsimp1_1 fsimp1_2 w3a fsimp1_0 fsimp1_1 fsimp1_0 fsimp1_1 fsimp1_2 3simpa simpld $.
$}
$( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp2_0 $f wff ph $.
	fsimp2_1 $f wff ps $.
	fsimp2_2 $f wff ch $.
	simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $= fsimp2_0 fsimp2_1 fsimp2_2 w3a fsimp2_0 fsimp2_1 fsimp2_0 fsimp2_1 fsimp2_2 3simpa simprd $.
$}
$( Simplification of triple conjunction.  (Contributed by NM,
     21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp3_0 $f wff ph $.
	fsimp3_1 $f wff ps $.
	fsimp3_2 $f wff ch $.
	simp3 $p |- ( ( ph /\ ps /\ ch ) -> ch ) $= fsimp3_0 fsimp3_1 fsimp3_2 w3a fsimp3_1 fsimp3_2 fsimp3_0 fsimp3_1 fsimp3_2 3simpc simprd $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpl1_0 $f wff ph $.
	fsimpl1_1 $f wff ps $.
	fsimpl1_2 $f wff ch $.
	fsimpl1_3 $f wff th $.
	simpl1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph ) $= fsimpl1_0 fsimpl1_1 fsimpl1_2 w3a fsimpl1_0 fsimpl1_3 fsimpl1_0 fsimpl1_1 fsimpl1_2 simp1 adantr $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpl2_0 $f wff ph $.
	fsimpl2_1 $f wff ps $.
	fsimpl2_2 $f wff ch $.
	fsimpl2_3 $f wff th $.
	simpl2 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps ) $= fsimpl2_0 fsimpl2_1 fsimpl2_2 w3a fsimpl2_1 fsimpl2_3 fsimpl2_0 fsimpl2_1 fsimpl2_2 simp2 adantr $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpl3_0 $f wff ph $.
	fsimpl3_1 $f wff ps $.
	fsimpl3_2 $f wff ch $.
	fsimpl3_3 $f wff th $.
	simpl3 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch ) $= fsimpl3_0 fsimpl3_1 fsimpl3_2 w3a fsimpl3_2 fsimpl3_3 fsimpl3_0 fsimpl3_1 fsimpl3_2 simp3 adantr $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpr1_0 $f wff ph $.
	fsimpr1_1 $f wff ps $.
	fsimpr1_2 $f wff ch $.
	fsimpr1_3 $f wff th $.
	simpr1 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps ) $= fsimpr1_1 fsimpr1_2 fsimpr1_3 w3a fsimpr1_1 fsimpr1_0 fsimpr1_1 fsimpr1_2 fsimpr1_3 simp1 adantl $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpr2_0 $f wff ph $.
	fsimpr2_1 $f wff ps $.
	fsimpr2_2 $f wff ch $.
	fsimpr2_3 $f wff th $.
	simpr2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch ) $= fsimpr2_1 fsimpr2_2 fsimpr2_3 w3a fsimpr2_2 fsimpr2_0 fsimpr2_1 fsimpr2_2 fsimpr2_3 simp2 adantl $.
$}
$( Simplification rule.  (Contributed by Jeff Hankins, 17-Nov-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimpr3_0 $f wff ph $.
	fsimpr3_1 $f wff ps $.
	fsimpr3_2 $f wff ch $.
	fsimpr3_3 $f wff th $.
	simpr3 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th ) $= fsimpr3_1 fsimpr3_2 fsimpr3_3 w3a fsimpr3_3 fsimpr3_0 fsimpr3_1 fsimpr3_2 fsimpr3_3 simp3 adantl $.
$}
$( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp1i_0 $f wff ph $.
	fsimp1i_1 $f wff ps $.
	fsimp1i_2 $f wff ch $.
	esimp1i_0 $e |- ( ph /\ ps /\ ch ) $.
	simp1i $p |- ph $= fsimp1i_0 fsimp1i_1 fsimp1i_2 w3a fsimp1i_0 esimp1i_0 fsimp1i_0 fsimp1i_1 fsimp1i_2 simp1 ax-mp $.
$}
$( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp2i_0 $f wff ph $.
	fsimp2i_1 $f wff ps $.
	fsimp2i_2 $f wff ch $.
	esimp2i_0 $e |- ( ph /\ ps /\ ch ) $.
	simp2i $p |- ps $= fsimp2i_0 fsimp2i_1 fsimp2i_2 w3a fsimp2i_1 esimp2i_0 fsimp2i_0 fsimp2i_1 fsimp2i_2 simp2 ax-mp $.
$}
$( Infer a conjunct from a triple conjunction.  (Contributed by NM,
       19-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fsimp3i_0 $f wff ph $.
	fsimp3i_1 $f wff ps $.
	fsimp3i_2 $f wff ch $.
	esimp3i_0 $e |- ( ph /\ ps /\ ch ) $.
	simp3i $p |- ch $= fsimp3i_0 fsimp3i_1 fsimp3i_2 w3a fsimp3i_2 esimp3i_0 fsimp3i_0 fsimp3i_1 fsimp3i_2 simp3 ax-mp $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp1d_0 $f wff ph $.
	fsimp1d_1 $f wff ps $.
	fsimp1d_2 $f wff ch $.
	fsimp1d_3 $f wff th $.
	esimp1d_0 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	simp1d $p |- ( ph -> ps ) $= fsimp1d_0 fsimp1d_1 fsimp1d_2 fsimp1d_3 w3a fsimp1d_1 esimp1d_0 fsimp1d_1 fsimp1d_2 fsimp1d_3 simp1 syl $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp2d_0 $f wff ph $.
	fsimp2d_1 $f wff ps $.
	fsimp2d_2 $f wff ch $.
	fsimp2d_3 $f wff th $.
	esimp2d_0 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	simp2d $p |- ( ph -> ch ) $= fsimp2d_0 fsimp2d_1 fsimp2d_2 fsimp2d_3 w3a fsimp2d_2 esimp2d_0 fsimp2d_1 fsimp2d_2 fsimp2d_3 simp2 syl $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by NM,
       4-Sep-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp3d_0 $f wff ph $.
	fsimp3d_1 $f wff ps $.
	fsimp3d_2 $f wff ch $.
	fsimp3d_3 $f wff th $.
	esimp3d_0 $e |- ( ph -> ( ps /\ ch /\ th ) ) $.
	simp3d $p |- ( ph -> th ) $= fsimp3d_0 fsimp3d_1 fsimp3d_2 fsimp3d_3 w3a fsimp3d_3 esimp3d_0 fsimp3d_1 fsimp3d_2 fsimp3d_3 simp3 syl $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp1bi_0 $f wff ph $.
	fsimp1bi_1 $f wff ps $.
	fsimp1bi_2 $f wff ch $.
	fsimp1bi_3 $f wff th $.
	esimp1bi_0 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	simp1bi $p |- ( ph -> ps ) $= fsimp1bi_0 fsimp1bi_1 fsimp1bi_2 fsimp1bi_3 fsimp1bi_0 fsimp1bi_1 fsimp1bi_2 fsimp1bi_3 w3a esimp1bi_0 biimpi simp1d $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp2bi_0 $f wff ph $.
	fsimp2bi_1 $f wff ps $.
	fsimp2bi_2 $f wff ch $.
	fsimp2bi_3 $f wff th $.
	esimp2bi_0 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	simp2bi $p |- ( ph -> ch ) $= fsimp2bi_0 fsimp2bi_1 fsimp2bi_2 fsimp2bi_3 fsimp2bi_0 fsimp2bi_1 fsimp2bi_2 fsimp2bi_3 w3a esimp2bi_0 biimpi simp2d $.
$}
$( Deduce a conjunct from a triple conjunction.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp3bi_0 $f wff ph $.
	fsimp3bi_1 $f wff ps $.
	fsimp3bi_2 $f wff ch $.
	fsimp3bi_3 $f wff th $.
	esimp3bi_0 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	simp3bi $p |- ( ph -> th ) $= fsimp3bi_0 fsimp3bi_1 fsimp3bi_2 fsimp3bi_3 fsimp3bi_0 fsimp3bi_1 fsimp3bi_2 fsimp3bi_3 w3a esimp3bi_0 biimpi simp3d $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3adant1_0 $f wff ph $.
	f3adant1_1 $f wff ps $.
	f3adant1_2 $f wff ch $.
	f3adant1_3 $f wff th $.
	e3adant1_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	3adant1 $p |- ( ( th /\ ph /\ ps ) -> ch ) $= f3adant1_3 f3adant1_0 f3adant1_1 w3a f3adant1_0 f3adant1_1 wa f3adant1_2 f3adant1_3 f3adant1_0 f3adant1_1 3simpc e3adant1_0 syl $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3adant2_0 $f wff ph $.
	f3adant2_1 $f wff ps $.
	f3adant2_2 $f wff ch $.
	f3adant2_3 $f wff th $.
	e3adant2_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	3adant2 $p |- ( ( ph /\ th /\ ps ) -> ch ) $= f3adant2_0 f3adant2_3 f3adant2_1 w3a f3adant2_0 f3adant2_1 wa f3adant2_2 f3adant2_0 f3adant2_3 f3adant2_1 3simpb e3adant2_0 syl $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Jul-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3adant3_0 $f wff ph $.
	f3adant3_1 $f wff ps $.
	f3adant3_2 $f wff ch $.
	f3adant3_3 $f wff th $.
	e3adant3_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	3adant3 $p |- ( ( ph /\ ps /\ th ) -> ch ) $= f3adant3_0 f3adant3_1 f3adant3_3 w3a f3adant3_0 f3adant3_1 wa f3adant3_2 f3adant3_0 f3adant3_1 f3adant3_3 3simpa e3adant3_0 syl $.
$}
$( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3ad2ant1_0 $f wff ph $.
	f3ad2ant1_1 $f wff ps $.
	f3ad2ant1_2 $f wff ch $.
	f3ad2ant1_3 $f wff th $.
	e3ad2ant1_0 $e |- ( ph -> ch ) $.
	3ad2ant1 $p |- ( ( ph /\ ps /\ th ) -> ch ) $= f3ad2ant1_0 f3ad2ant1_3 f3ad2ant1_2 f3ad2ant1_1 f3ad2ant1_0 f3ad2ant1_2 f3ad2ant1_3 e3ad2ant1_0 adantr 3adant2 $.
$}
$( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3ad2ant2_0 $f wff ph $.
	f3ad2ant2_1 $f wff ps $.
	f3ad2ant2_2 $f wff ch $.
	f3ad2ant2_3 $f wff th $.
	e3ad2ant2_0 $e |- ( ph -> ch ) $.
	3ad2ant2 $p |- ( ( ps /\ ph /\ th ) -> ch ) $= f3ad2ant2_0 f3ad2ant2_3 f3ad2ant2_2 f3ad2ant2_1 f3ad2ant2_0 f3ad2ant2_2 f3ad2ant2_3 e3ad2ant2_0 adantr 3adant1 $.
$}
$( Deduction adding conjuncts to an antecedent.  (Contributed by NM,
       21-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3ad2ant3_0 $f wff ph $.
	f3ad2ant3_1 $f wff ps $.
	f3ad2ant3_2 $f wff ch $.
	f3ad2ant3_3 $f wff th $.
	e3ad2ant3_0 $e |- ( ph -> ch ) $.
	3ad2ant3 $p |- ( ( ps /\ th /\ ph ) -> ch ) $= f3ad2ant3_3 f3ad2ant3_0 f3ad2ant3_2 f3ad2ant3_1 f3ad2ant3_0 f3ad2ant3_2 f3ad2ant3_3 e3ad2ant3_0 adantl 3adant1 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp1l_0 $f wff ph $.
	fsimp1l_1 $f wff ps $.
	fsimp1l_2 $f wff ch $.
	fsimp1l_3 $f wff th $.
	simp1l $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ph ) $= fsimp1l_0 fsimp1l_1 wa fsimp1l_2 fsimp1l_0 fsimp1l_3 fsimp1l_0 fsimp1l_1 simpl 3ad2ant1 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp1r_0 $f wff ph $.
	fsimp1r_1 $f wff ps $.
	fsimp1r_2 $f wff ch $.
	fsimp1r_3 $f wff th $.
	simp1r $p |- ( ( ( ph /\ ps ) /\ ch /\ th ) -> ps ) $= fsimp1r_0 fsimp1r_1 wa fsimp1r_2 fsimp1r_1 fsimp1r_3 fsimp1r_0 fsimp1r_1 simpr 3ad2ant1 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp2l_0 $f wff ph $.
	fsimp2l_1 $f wff ps $.
	fsimp2l_2 $f wff ch $.
	fsimp2l_3 $f wff th $.
	simp2l $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ps ) $= fsimp2l_1 fsimp2l_2 wa fsimp2l_0 fsimp2l_1 fsimp2l_3 fsimp2l_1 fsimp2l_2 simpl 3ad2ant2 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp2r_0 $f wff ph $.
	fsimp2r_1 $f wff ps $.
	fsimp2r_2 $f wff ch $.
	fsimp2r_3 $f wff th $.
	simp2r $p |- ( ( ph /\ ( ps /\ ch ) /\ th ) -> ch ) $= fsimp2r_1 fsimp2r_2 wa fsimp2r_0 fsimp2r_2 fsimp2r_3 fsimp2r_1 fsimp2r_2 simpr 3ad2ant2 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp3l_0 $f wff ph $.
	fsimp3l_1 $f wff ps $.
	fsimp3l_2 $f wff ch $.
	fsimp3l_3 $f wff th $.
	simp3l $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> ch ) $= fsimp3l_2 fsimp3l_3 wa fsimp3l_0 fsimp3l_2 fsimp3l_1 fsimp3l_2 fsimp3l_3 simpl 3ad2ant3 $.
$}
$( Simplification of triple conjunction.  (Contributed by NM, 9-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fsimp3r_0 $f wff ph $.
	fsimp3r_1 $f wff ps $.
	fsimp3r_2 $f wff ch $.
	fsimp3r_3 $f wff th $.
	simp3r $p |- ( ( ph /\ ps /\ ( ch /\ th ) ) -> th ) $= fsimp3r_2 fsimp3r_3 wa fsimp3r_0 fsimp3r_3 fsimp3r_1 fsimp3r_2 fsimp3r_3 simpr 3ad2ant3 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp11_0 $f wff ph $.
	fsimp11_1 $f wff ps $.
	fsimp11_2 $f wff ch $.
	fsimp11_3 $f wff th $.
	fsimp11_4 $f wff ta $.
	simp11 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph ) $= fsimp11_0 fsimp11_1 fsimp11_2 w3a fsimp11_3 fsimp11_0 fsimp11_4 fsimp11_0 fsimp11_1 fsimp11_2 simp1 3ad2ant1 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp12_0 $f wff ph $.
	fsimp12_1 $f wff ps $.
	fsimp12_2 $f wff ch $.
	fsimp12_3 $f wff th $.
	fsimp12_4 $f wff ta $.
	simp12 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ps ) $= fsimp12_0 fsimp12_1 fsimp12_2 w3a fsimp12_3 fsimp12_1 fsimp12_4 fsimp12_0 fsimp12_1 fsimp12_2 simp2 3ad2ant1 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp13_0 $f wff ph $.
	fsimp13_1 $f wff ps $.
	fsimp13_2 $f wff ch $.
	fsimp13_3 $f wff th $.
	fsimp13_4 $f wff ta $.
	simp13 $p |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch ) $= fsimp13_0 fsimp13_1 fsimp13_2 w3a fsimp13_3 fsimp13_2 fsimp13_4 fsimp13_0 fsimp13_1 fsimp13_2 simp3 3ad2ant1 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp21_0 $f wff ph $.
	fsimp21_1 $f wff ps $.
	fsimp21_2 $f wff ch $.
	fsimp21_3 $f wff th $.
	fsimp21_4 $f wff ta $.
	simp21 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps ) $= fsimp21_1 fsimp21_2 fsimp21_3 w3a fsimp21_0 fsimp21_1 fsimp21_4 fsimp21_1 fsimp21_2 fsimp21_3 simp1 3ad2ant2 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp22_0 $f wff ph $.
	fsimp22_1 $f wff ps $.
	fsimp22_2 $f wff ch $.
	fsimp22_3 $f wff th $.
	fsimp22_4 $f wff ta $.
	simp22 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch ) $= fsimp22_1 fsimp22_2 fsimp22_3 w3a fsimp22_0 fsimp22_2 fsimp22_4 fsimp22_1 fsimp22_2 fsimp22_3 simp2 3ad2ant2 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp23_0 $f wff ph $.
	fsimp23_1 $f wff ps $.
	fsimp23_2 $f wff ch $.
	fsimp23_3 $f wff th $.
	fsimp23_4 $f wff ta $.
	simp23 $p |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th ) $= fsimp23_1 fsimp23_2 fsimp23_3 w3a fsimp23_0 fsimp23_3 fsimp23_4 fsimp23_1 fsimp23_2 fsimp23_3 simp3 3ad2ant2 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp31_0 $f wff ph $.
	fsimp31_1 $f wff ps $.
	fsimp31_2 $f wff ch $.
	fsimp31_3 $f wff th $.
	fsimp31_4 $f wff ta $.
	simp31 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch ) $= fsimp31_2 fsimp31_3 fsimp31_4 w3a fsimp31_0 fsimp31_2 fsimp31_1 fsimp31_2 fsimp31_3 fsimp31_4 simp1 3ad2ant3 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp32_0 $f wff ph $.
	fsimp32_1 $f wff ps $.
	fsimp32_2 $f wff ch $.
	fsimp32_3 $f wff th $.
	fsimp32_4 $f wff ta $.
	simp32 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th ) $= fsimp32_2 fsimp32_3 fsimp32_4 w3a fsimp32_0 fsimp32_3 fsimp32_1 fsimp32_2 fsimp32_3 fsimp32_4 simp2 3ad2ant3 $.
$}
$( Simplification of doubly triple conjunction.  (Contributed by NM,
     17-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp33_0 $f wff ph $.
	fsimp33_1 $f wff ps $.
	fsimp33_2 $f wff ch $.
	fsimp33_3 $f wff th $.
	fsimp33_4 $f wff ta $.
	simp33 $p |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta ) $= fsimp33_2 fsimp33_3 fsimp33_4 w3a fsimp33_0 fsimp33_4 fsimp33_1 fsimp33_2 fsimp33_3 fsimp33_4 simp3 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpll1_0 $f wff ph $.
	fsimpll1_1 $f wff ps $.
	fsimpll1_2 $f wff ch $.
	fsimpll1_3 $f wff th $.
	fsimpll1_4 $f wff ta $.
	simpll1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph ) $= fsimpll1_0 fsimpll1_1 fsimpll1_2 w3a fsimpll1_3 wa fsimpll1_0 fsimpll1_4 fsimpll1_0 fsimpll1_1 fsimpll1_2 fsimpll1_3 simpl1 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpll2_0 $f wff ph $.
	fsimpll2_1 $f wff ps $.
	fsimpll2_2 $f wff ch $.
	fsimpll2_3 $f wff th $.
	fsimpll2_4 $f wff ta $.
	simpll2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps ) $= fsimpll2_0 fsimpll2_1 fsimpll2_2 w3a fsimpll2_3 wa fsimpll2_1 fsimpll2_4 fsimpll2_0 fsimpll2_1 fsimpll2_2 fsimpll2_3 simpl2 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpll3_0 $f wff ph $.
	fsimpll3_1 $f wff ps $.
	fsimpll3_2 $f wff ch $.
	fsimpll3_3 $f wff th $.
	fsimpll3_4 $f wff ta $.
	simpll3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch ) $= fsimpll3_0 fsimpll3_1 fsimpll3_2 w3a fsimpll3_3 wa fsimpll3_2 fsimpll3_4 fsimpll3_0 fsimpll3_1 fsimpll3_2 fsimpll3_3 simpl3 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimplr1_0 $f wff ph $.
	fsimplr1_1 $f wff ps $.
	fsimplr1_2 $f wff ch $.
	fsimplr1_3 $f wff th $.
	fsimplr1_4 $f wff ta $.
	simplr1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph ) $= fsimplr1_3 fsimplr1_0 fsimplr1_1 fsimplr1_2 w3a wa fsimplr1_0 fsimplr1_4 fsimplr1_3 fsimplr1_0 fsimplr1_1 fsimplr1_2 simpr1 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimplr2_0 $f wff ph $.
	fsimplr2_1 $f wff ps $.
	fsimplr2_2 $f wff ch $.
	fsimplr2_3 $f wff th $.
	fsimplr2_4 $f wff ta $.
	simplr2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps ) $= fsimplr2_3 fsimplr2_0 fsimplr2_1 fsimplr2_2 w3a wa fsimplr2_1 fsimplr2_4 fsimplr2_3 fsimplr2_0 fsimplr2_1 fsimplr2_2 simpr2 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimplr3_0 $f wff ph $.
	fsimplr3_1 $f wff ps $.
	fsimplr3_2 $f wff ch $.
	fsimplr3_3 $f wff th $.
	fsimplr3_4 $f wff ta $.
	simplr3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ch ) $= fsimplr3_3 fsimplr3_0 fsimplr3_1 fsimplr3_2 w3a wa fsimplr3_2 fsimplr3_4 fsimplr3_3 fsimplr3_0 fsimplr3_1 fsimplr3_2 simpr3 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprl1_0 $f wff ph $.
	fsimprl1_1 $f wff ps $.
	fsimprl1_2 $f wff ch $.
	fsimprl1_3 $f wff th $.
	fsimprl1_4 $f wff ta $.
	simprl1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $= fsimprl1_0 fsimprl1_1 fsimprl1_2 w3a fsimprl1_3 wa fsimprl1_0 fsimprl1_4 fsimprl1_0 fsimprl1_1 fsimprl1_2 fsimprl1_3 simpl1 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprl2_0 $f wff ph $.
	fsimprl2_1 $f wff ps $.
	fsimprl2_2 $f wff ch $.
	fsimprl2_3 $f wff th $.
	fsimprl2_4 $f wff ta $.
	simprl2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $= fsimprl2_0 fsimprl2_1 fsimprl2_2 w3a fsimprl2_3 wa fsimprl2_1 fsimprl2_4 fsimprl2_0 fsimprl2_1 fsimprl2_2 fsimprl2_3 simpl2 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprl3_0 $f wff ph $.
	fsimprl3_1 $f wff ps $.
	fsimprl3_2 $f wff ch $.
	fsimprl3_3 $f wff th $.
	fsimprl3_4 $f wff ta $.
	simprl3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $= fsimprl3_0 fsimprl3_1 fsimprl3_2 w3a fsimprl3_3 wa fsimprl3_2 fsimprl3_4 fsimprl3_0 fsimprl3_1 fsimprl3_2 fsimprl3_3 simpl3 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprr1_0 $f wff ph $.
	fsimprr1_1 $f wff ps $.
	fsimprr1_2 $f wff ch $.
	fsimprr1_3 $f wff th $.
	fsimprr1_4 $f wff ta $.
	simprr1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= fsimprr1_3 fsimprr1_0 fsimprr1_1 fsimprr1_2 w3a wa fsimprr1_0 fsimprr1_4 fsimprr1_3 fsimprr1_0 fsimprr1_1 fsimprr1_2 simpr1 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprr2_0 $f wff ph $.
	fsimprr2_1 $f wff ps $.
	fsimprr2_2 $f wff ch $.
	fsimprr2_3 $f wff th $.
	fsimprr2_4 $f wff ta $.
	simprr2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= fsimprr2_3 fsimprr2_0 fsimprr2_1 fsimprr2_2 w3a wa fsimprr2_1 fsimprr2_4 fsimprr2_3 fsimprr2_0 fsimprr2_1 fsimprr2_2 simpr2 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimprr3_0 $f wff ph $.
	fsimprr3_1 $f wff ps $.
	fsimprr3_2 $f wff ch $.
	fsimprr3_3 $f wff th $.
	fsimprr3_4 $f wff ta $.
	simprr3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= fsimprr3_3 fsimprr3_0 fsimprr3_1 fsimprr3_2 w3a wa fsimprr3_2 fsimprr3_4 fsimprr3_3 fsimprr3_0 fsimprr3_1 fsimprr3_2 simpr3 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl1l_0 $f wff ph $.
	fsimpl1l_1 $f wff ps $.
	fsimpl1l_2 $f wff ch $.
	fsimpl1l_3 $f wff th $.
	fsimpl1l_4 $f wff ta $.
	simpl1l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph ) $= fsimpl1l_0 fsimpl1l_1 wa fsimpl1l_2 fsimpl1l_3 w3a fsimpl1l_0 fsimpl1l_4 fsimpl1l_0 fsimpl1l_1 fsimpl1l_2 fsimpl1l_3 simp1l adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl1r_0 $f wff ph $.
	fsimpl1r_1 $f wff ps $.
	fsimpl1r_2 $f wff ch $.
	fsimpl1r_3 $f wff th $.
	fsimpl1r_4 $f wff ta $.
	simpl1r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps ) $= fsimpl1r_0 fsimpl1r_1 wa fsimpl1r_2 fsimpl1r_3 w3a fsimpl1r_1 fsimpl1r_4 fsimpl1r_0 fsimpl1r_1 fsimpl1r_2 fsimpl1r_3 simp1r adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl2l_0 $f wff ph $.
	fsimpl2l_1 $f wff ps $.
	fsimpl2l_2 $f wff ch $.
	fsimpl2l_3 $f wff th $.
	fsimpl2l_4 $f wff ta $.
	simpl2l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph ) $= fsimpl2l_2 fsimpl2l_0 fsimpl2l_1 wa fsimpl2l_3 w3a fsimpl2l_0 fsimpl2l_4 fsimpl2l_2 fsimpl2l_0 fsimpl2l_1 fsimpl2l_3 simp2l adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl2r_0 $f wff ph $.
	fsimpl2r_1 $f wff ps $.
	fsimpl2r_2 $f wff ch $.
	fsimpl2r_3 $f wff th $.
	fsimpl2r_4 $f wff ta $.
	simpl2r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps ) $= fsimpl2r_2 fsimpl2r_0 fsimpl2r_1 wa fsimpl2r_3 w3a fsimpl2r_1 fsimpl2r_4 fsimpl2r_2 fsimpl2r_0 fsimpl2r_1 fsimpl2r_3 simp2r adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl3l_0 $f wff ph $.
	fsimpl3l_1 $f wff ps $.
	fsimpl3l_2 $f wff ch $.
	fsimpl3l_3 $f wff th $.
	fsimpl3l_4 $f wff ta $.
	simpl3l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $= fsimpl3l_2 fsimpl3l_3 fsimpl3l_0 fsimpl3l_1 wa w3a fsimpl3l_0 fsimpl3l_4 fsimpl3l_2 fsimpl3l_3 fsimpl3l_0 fsimpl3l_1 simp3l adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpl3r_0 $f wff ph $.
	fsimpl3r_1 $f wff ps $.
	fsimpl3r_2 $f wff ch $.
	fsimpl3r_3 $f wff th $.
	fsimpl3r_4 $f wff ta $.
	simpl3r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $= fsimpl3r_2 fsimpl3r_3 fsimpl3r_0 fsimpl3r_1 wa w3a fsimpl3r_1 fsimpl3r_4 fsimpl3r_2 fsimpl3r_3 fsimpl3r_0 fsimpl3r_1 simp3r adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr1l_0 $f wff ph $.
	fsimpr1l_1 $f wff ps $.
	fsimpr1l_2 $f wff ch $.
	fsimpr1l_3 $f wff th $.
	fsimpr1l_4 $f wff ta $.
	simpr1l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $= fsimpr1l_0 fsimpr1l_1 wa fsimpr1l_2 fsimpr1l_3 w3a fsimpr1l_0 fsimpr1l_4 fsimpr1l_0 fsimpr1l_1 fsimpr1l_2 fsimpr1l_3 simp1l adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr1r_0 $f wff ph $.
	fsimpr1r_1 $f wff ps $.
	fsimpr1r_2 $f wff ch $.
	fsimpr1r_3 $f wff th $.
	fsimpr1r_4 $f wff ta $.
	simpr1r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $= fsimpr1r_0 fsimpr1r_1 wa fsimpr1r_2 fsimpr1r_3 w3a fsimpr1r_1 fsimpr1r_4 fsimpr1r_0 fsimpr1r_1 fsimpr1r_2 fsimpr1r_3 simp1r adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr2l_0 $f wff ph $.
	fsimpr2l_1 $f wff ps $.
	fsimpr2l_2 $f wff ch $.
	fsimpr2l_3 $f wff th $.
	fsimpr2l_4 $f wff ta $.
	simpr2l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $= fsimpr2l_2 fsimpr2l_0 fsimpr2l_1 wa fsimpr2l_3 w3a fsimpr2l_0 fsimpr2l_4 fsimpr2l_2 fsimpr2l_0 fsimpr2l_1 fsimpr2l_3 simp2l adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr2r_0 $f wff ph $.
	fsimpr2r_1 $f wff ps $.
	fsimpr2r_2 $f wff ch $.
	fsimpr2r_3 $f wff th $.
	fsimpr2r_4 $f wff ta $.
	simpr2r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $= fsimpr2r_2 fsimpr2r_0 fsimpr2r_1 wa fsimpr2r_3 w3a fsimpr2r_1 fsimpr2r_4 fsimpr2r_2 fsimpr2r_0 fsimpr2r_1 fsimpr2r_3 simp2r adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr3l_0 $f wff ph $.
	fsimpr3l_1 $f wff ps $.
	fsimpr3l_2 $f wff ch $.
	fsimpr3l_3 $f wff th $.
	fsimpr3l_4 $f wff ta $.
	simpr3l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $= fsimpr3l_2 fsimpr3l_3 fsimpr3l_0 fsimpr3l_1 wa w3a fsimpr3l_0 fsimpr3l_4 fsimpr3l_2 fsimpr3l_3 fsimpr3l_0 fsimpr3l_1 simp3l adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimpr3r_0 $f wff ph $.
	fsimpr3r_1 $f wff ps $.
	fsimpr3r_2 $f wff ch $.
	fsimpr3r_3 $f wff th $.
	fsimpr3r_4 $f wff ta $.
	simpr3r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $= fsimpr3r_2 fsimpr3r_3 fsimpr3r_0 fsimpr3r_1 wa w3a fsimpr3r_1 fsimpr3r_4 fsimpr3r_2 fsimpr3r_3 fsimpr3r_0 fsimpr3r_1 simp3r adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp1ll_0 $f wff ph $.
	fsimp1ll_1 $f wff ps $.
	fsimp1ll_2 $f wff ch $.
	fsimp1ll_3 $f wff th $.
	fsimp1ll_4 $f wff ta $.
	simp1ll $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ph ) $= fsimp1ll_0 fsimp1ll_1 wa fsimp1ll_2 wa fsimp1ll_3 fsimp1ll_0 fsimp1ll_4 fsimp1ll_0 fsimp1ll_1 fsimp1ll_2 simpll 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp1lr_0 $f wff ph $.
	fsimp1lr_1 $f wff ps $.
	fsimp1lr_2 $f wff ch $.
	fsimp1lr_3 $f wff th $.
	fsimp1lr_4 $f wff ta $.
	simp1lr $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th /\ ta ) -> ps ) $= fsimp1lr_0 fsimp1lr_1 wa fsimp1lr_2 wa fsimp1lr_3 fsimp1lr_1 fsimp1lr_4 fsimp1lr_0 fsimp1lr_1 fsimp1lr_2 simplr 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp1rl_0 $f wff ph $.
	fsimp1rl_1 $f wff ps $.
	fsimp1rl_2 $f wff ch $.
	fsimp1rl_3 $f wff th $.
	fsimp1rl_4 $f wff ta $.
	simp1rl $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ph ) $= fsimp1rl_2 fsimp1rl_0 fsimp1rl_1 wa wa fsimp1rl_3 fsimp1rl_0 fsimp1rl_4 fsimp1rl_2 fsimp1rl_0 fsimp1rl_1 simprl 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp1rr_0 $f wff ph $.
	fsimp1rr_1 $f wff ps $.
	fsimp1rr_2 $f wff ch $.
	fsimp1rr_3 $f wff th $.
	fsimp1rr_4 $f wff ta $.
	simp1rr $p |- ( ( ( ch /\ ( ph /\ ps ) ) /\ th /\ ta ) -> ps ) $= fsimp1rr_2 fsimp1rr_0 fsimp1rr_1 wa wa fsimp1rr_3 fsimp1rr_1 fsimp1rr_4 fsimp1rr_2 fsimp1rr_0 fsimp1rr_1 simprr 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp2ll_0 $f wff ph $.
	fsimp2ll_1 $f wff ps $.
	fsimp2ll_2 $f wff ch $.
	fsimp2ll_3 $f wff th $.
	fsimp2ll_4 $f wff ta $.
	simp2ll $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ph ) $= fsimp2ll_0 fsimp2ll_1 wa fsimp2ll_2 wa fsimp2ll_3 fsimp2ll_0 fsimp2ll_4 fsimp2ll_0 fsimp2ll_1 fsimp2ll_2 simpll 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp2lr_0 $f wff ph $.
	fsimp2lr_1 $f wff ps $.
	fsimp2lr_2 $f wff ch $.
	fsimp2lr_3 $f wff th $.
	fsimp2lr_4 $f wff ta $.
	simp2lr $p |- ( ( th /\ ( ( ph /\ ps ) /\ ch ) /\ ta ) -> ps ) $= fsimp2lr_0 fsimp2lr_1 wa fsimp2lr_2 wa fsimp2lr_3 fsimp2lr_1 fsimp2lr_4 fsimp2lr_0 fsimp2lr_1 fsimp2lr_2 simplr 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp2rl_0 $f wff ph $.
	fsimp2rl_1 $f wff ps $.
	fsimp2rl_2 $f wff ch $.
	fsimp2rl_3 $f wff th $.
	fsimp2rl_4 $f wff ta $.
	simp2rl $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ph ) $= fsimp2rl_2 fsimp2rl_0 fsimp2rl_1 wa wa fsimp2rl_3 fsimp2rl_0 fsimp2rl_4 fsimp2rl_2 fsimp2rl_0 fsimp2rl_1 simprl 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp2rr_0 $f wff ph $.
	fsimp2rr_1 $f wff ps $.
	fsimp2rr_2 $f wff ch $.
	fsimp2rr_3 $f wff th $.
	fsimp2rr_4 $f wff ta $.
	simp2rr $p |- ( ( th /\ ( ch /\ ( ph /\ ps ) ) /\ ta ) -> ps ) $= fsimp2rr_2 fsimp2rr_0 fsimp2rr_1 wa wa fsimp2rr_3 fsimp2rr_1 fsimp2rr_4 fsimp2rr_2 fsimp2rr_0 fsimp2rr_1 simprr 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp3ll_0 $f wff ph $.
	fsimp3ll_1 $f wff ps $.
	fsimp3ll_2 $f wff ch $.
	fsimp3ll_3 $f wff th $.
	fsimp3ll_4 $f wff ta $.
	simp3ll $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ph ) $= fsimp3ll_0 fsimp3ll_1 wa fsimp3ll_2 wa fsimp3ll_3 fsimp3ll_0 fsimp3ll_4 fsimp3ll_0 fsimp3ll_1 fsimp3ll_2 simpll 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp3lr_0 $f wff ph $.
	fsimp3lr_1 $f wff ps $.
	fsimp3lr_2 $f wff ch $.
	fsimp3lr_3 $f wff th $.
	fsimp3lr_4 $f wff ta $.
	simp3lr $p |- ( ( th /\ ta /\ ( ( ph /\ ps ) /\ ch ) ) -> ps ) $= fsimp3lr_0 fsimp3lr_1 wa fsimp3lr_2 wa fsimp3lr_3 fsimp3lr_1 fsimp3lr_4 fsimp3lr_0 fsimp3lr_1 fsimp3lr_2 simplr 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp3rl_0 $f wff ph $.
	fsimp3rl_1 $f wff ps $.
	fsimp3rl_2 $f wff ch $.
	fsimp3rl_3 $f wff th $.
	fsimp3rl_4 $f wff ta $.
	simp3rl $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ph ) $= fsimp3rl_2 fsimp3rl_0 fsimp3rl_1 wa wa fsimp3rl_3 fsimp3rl_0 fsimp3rl_4 fsimp3rl_2 fsimp3rl_0 fsimp3rl_1 simprl 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsimp3rr_0 $f wff ph $.
	fsimp3rr_1 $f wff ps $.
	fsimp3rr_2 $f wff ch $.
	fsimp3rr_3 $f wff th $.
	fsimp3rr_4 $f wff ta $.
	simp3rr $p |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps ) $= fsimp3rr_2 fsimp3rr_0 fsimp3rr_1 wa wa fsimp3rr_3 fsimp3rr_1 fsimp3rr_4 fsimp3rr_2 fsimp3rr_0 fsimp3rr_1 simprr 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl11_0 $f wff ph $.
	fsimpl11_1 $f wff ps $.
	fsimpl11_2 $f wff ch $.
	fsimpl11_3 $f wff th $.
	fsimpl11_4 $f wff ta $.
	fsimpl11_5 $f wff et $.
	simpl11 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph ) $= fsimpl11_0 fsimpl11_1 fsimpl11_2 w3a fsimpl11_3 fsimpl11_4 w3a fsimpl11_0 fsimpl11_5 fsimpl11_0 fsimpl11_1 fsimpl11_2 fsimpl11_3 fsimpl11_4 simp11 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl12_0 $f wff ph $.
	fsimpl12_1 $f wff ps $.
	fsimpl12_2 $f wff ch $.
	fsimpl12_3 $f wff th $.
	fsimpl12_4 $f wff ta $.
	fsimpl12_5 $f wff et $.
	simpl12 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps ) $= fsimpl12_0 fsimpl12_1 fsimpl12_2 w3a fsimpl12_3 fsimpl12_4 w3a fsimpl12_1 fsimpl12_5 fsimpl12_0 fsimpl12_1 fsimpl12_2 fsimpl12_3 fsimpl12_4 simp12 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl13_0 $f wff ph $.
	fsimpl13_1 $f wff ps $.
	fsimpl13_2 $f wff ch $.
	fsimpl13_3 $f wff th $.
	fsimpl13_4 $f wff ta $.
	fsimpl13_5 $f wff et $.
	simpl13 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch ) $= fsimpl13_0 fsimpl13_1 fsimpl13_2 w3a fsimpl13_3 fsimpl13_4 w3a fsimpl13_2 fsimpl13_5 fsimpl13_0 fsimpl13_1 fsimpl13_2 fsimpl13_3 fsimpl13_4 simp13 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl21_0 $f wff ph $.
	fsimpl21_1 $f wff ps $.
	fsimpl21_2 $f wff ch $.
	fsimpl21_3 $f wff th $.
	fsimpl21_4 $f wff ta $.
	fsimpl21_5 $f wff et $.
	simpl21 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph ) $= fsimpl21_3 fsimpl21_0 fsimpl21_1 fsimpl21_2 w3a fsimpl21_4 w3a fsimpl21_0 fsimpl21_5 fsimpl21_3 fsimpl21_0 fsimpl21_1 fsimpl21_2 fsimpl21_4 simp21 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl22_0 $f wff ph $.
	fsimpl22_1 $f wff ps $.
	fsimpl22_2 $f wff ch $.
	fsimpl22_3 $f wff th $.
	fsimpl22_4 $f wff ta $.
	fsimpl22_5 $f wff et $.
	simpl22 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps ) $= fsimpl22_3 fsimpl22_0 fsimpl22_1 fsimpl22_2 w3a fsimpl22_4 w3a fsimpl22_1 fsimpl22_5 fsimpl22_3 fsimpl22_0 fsimpl22_1 fsimpl22_2 fsimpl22_4 simp22 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl23_0 $f wff ph $.
	fsimpl23_1 $f wff ps $.
	fsimpl23_2 $f wff ch $.
	fsimpl23_3 $f wff th $.
	fsimpl23_4 $f wff ta $.
	fsimpl23_5 $f wff et $.
	simpl23 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch ) $= fsimpl23_3 fsimpl23_0 fsimpl23_1 fsimpl23_2 w3a fsimpl23_4 w3a fsimpl23_2 fsimpl23_5 fsimpl23_3 fsimpl23_0 fsimpl23_1 fsimpl23_2 fsimpl23_4 simp23 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl31_0 $f wff ph $.
	fsimpl31_1 $f wff ps $.
	fsimpl31_2 $f wff ch $.
	fsimpl31_3 $f wff th $.
	fsimpl31_4 $f wff ta $.
	fsimpl31_5 $f wff et $.
	simpl31 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $= fsimpl31_3 fsimpl31_4 fsimpl31_0 fsimpl31_1 fsimpl31_2 w3a w3a fsimpl31_0 fsimpl31_5 fsimpl31_3 fsimpl31_4 fsimpl31_0 fsimpl31_1 fsimpl31_2 simp31 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl32_0 $f wff ph $.
	fsimpl32_1 $f wff ps $.
	fsimpl32_2 $f wff ch $.
	fsimpl32_3 $f wff th $.
	fsimpl32_4 $f wff ta $.
	fsimpl32_5 $f wff et $.
	simpl32 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $= fsimpl32_3 fsimpl32_4 fsimpl32_0 fsimpl32_1 fsimpl32_2 w3a w3a fsimpl32_1 fsimpl32_5 fsimpl32_3 fsimpl32_4 fsimpl32_0 fsimpl32_1 fsimpl32_2 simp32 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpl33_0 $f wff ph $.
	fsimpl33_1 $f wff ps $.
	fsimpl33_2 $f wff ch $.
	fsimpl33_3 $f wff th $.
	fsimpl33_4 $f wff ta $.
	fsimpl33_5 $f wff et $.
	simpl33 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $= fsimpl33_3 fsimpl33_4 fsimpl33_0 fsimpl33_1 fsimpl33_2 w3a w3a fsimpl33_2 fsimpl33_5 fsimpl33_3 fsimpl33_4 fsimpl33_0 fsimpl33_1 fsimpl33_2 simp33 adantr $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr11_0 $f wff ph $.
	fsimpr11_1 $f wff ps $.
	fsimpr11_2 $f wff ch $.
	fsimpr11_3 $f wff th $.
	fsimpr11_4 $f wff ta $.
	fsimpr11_5 $f wff et $.
	simpr11 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $= fsimpr11_0 fsimpr11_1 fsimpr11_2 w3a fsimpr11_3 fsimpr11_4 w3a fsimpr11_0 fsimpr11_5 fsimpr11_0 fsimpr11_1 fsimpr11_2 fsimpr11_3 fsimpr11_4 simp11 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr12_0 $f wff ph $.
	fsimpr12_1 $f wff ps $.
	fsimpr12_2 $f wff ch $.
	fsimpr12_3 $f wff th $.
	fsimpr12_4 $f wff ta $.
	fsimpr12_5 $f wff et $.
	simpr12 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $= fsimpr12_0 fsimpr12_1 fsimpr12_2 w3a fsimpr12_3 fsimpr12_4 w3a fsimpr12_1 fsimpr12_5 fsimpr12_0 fsimpr12_1 fsimpr12_2 fsimpr12_3 fsimpr12_4 simp12 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr13_0 $f wff ph $.
	fsimpr13_1 $f wff ps $.
	fsimpr13_2 $f wff ch $.
	fsimpr13_3 $f wff th $.
	fsimpr13_4 $f wff ta $.
	fsimpr13_5 $f wff et $.
	simpr13 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $= fsimpr13_0 fsimpr13_1 fsimpr13_2 w3a fsimpr13_3 fsimpr13_4 w3a fsimpr13_2 fsimpr13_5 fsimpr13_0 fsimpr13_1 fsimpr13_2 fsimpr13_3 fsimpr13_4 simp13 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr21_0 $f wff ph $.
	fsimpr21_1 $f wff ps $.
	fsimpr21_2 $f wff ch $.
	fsimpr21_3 $f wff th $.
	fsimpr21_4 $f wff ta $.
	fsimpr21_5 $f wff et $.
	simpr21 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $= fsimpr21_3 fsimpr21_0 fsimpr21_1 fsimpr21_2 w3a fsimpr21_4 w3a fsimpr21_0 fsimpr21_5 fsimpr21_3 fsimpr21_0 fsimpr21_1 fsimpr21_2 fsimpr21_4 simp21 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr22_0 $f wff ph $.
	fsimpr22_1 $f wff ps $.
	fsimpr22_2 $f wff ch $.
	fsimpr22_3 $f wff th $.
	fsimpr22_4 $f wff ta $.
	fsimpr22_5 $f wff et $.
	simpr22 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $= fsimpr22_3 fsimpr22_0 fsimpr22_1 fsimpr22_2 w3a fsimpr22_4 w3a fsimpr22_1 fsimpr22_5 fsimpr22_3 fsimpr22_0 fsimpr22_1 fsimpr22_2 fsimpr22_4 simp22 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr23_0 $f wff ph $.
	fsimpr23_1 $f wff ps $.
	fsimpr23_2 $f wff ch $.
	fsimpr23_3 $f wff th $.
	fsimpr23_4 $f wff ta $.
	fsimpr23_5 $f wff et $.
	simpr23 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $= fsimpr23_3 fsimpr23_0 fsimpr23_1 fsimpr23_2 w3a fsimpr23_4 w3a fsimpr23_2 fsimpr23_5 fsimpr23_3 fsimpr23_0 fsimpr23_1 fsimpr23_2 fsimpr23_4 simp23 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr31_0 $f wff ph $.
	fsimpr31_1 $f wff ps $.
	fsimpr31_2 $f wff ch $.
	fsimpr31_3 $f wff th $.
	fsimpr31_4 $f wff ta $.
	fsimpr31_5 $f wff et $.
	simpr31 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= fsimpr31_3 fsimpr31_4 fsimpr31_0 fsimpr31_1 fsimpr31_2 w3a w3a fsimpr31_0 fsimpr31_5 fsimpr31_3 fsimpr31_4 fsimpr31_0 fsimpr31_1 fsimpr31_2 simp31 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr32_0 $f wff ph $.
	fsimpr32_1 $f wff ps $.
	fsimpr32_2 $f wff ch $.
	fsimpr32_3 $f wff th $.
	fsimpr32_4 $f wff ta $.
	fsimpr32_5 $f wff et $.
	simpr32 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= fsimpr32_3 fsimpr32_4 fsimpr32_0 fsimpr32_1 fsimpr32_2 w3a w3a fsimpr32_1 fsimpr32_5 fsimpr32_3 fsimpr32_4 fsimpr32_0 fsimpr32_1 fsimpr32_2 simp32 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimpr33_0 $f wff ph $.
	fsimpr33_1 $f wff ps $.
	fsimpr33_2 $f wff ch $.
	fsimpr33_3 $f wff th $.
	fsimpr33_4 $f wff ta $.
	fsimpr33_5 $f wff et $.
	simpr33 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= fsimpr33_3 fsimpr33_4 fsimpr33_0 fsimpr33_1 fsimpr33_2 w3a w3a fsimpr33_2 fsimpr33_5 fsimpr33_3 fsimpr33_4 fsimpr33_0 fsimpr33_1 fsimpr33_2 simp33 adantl $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1l1_0 $f wff ph $.
	fsimp1l1_1 $f wff ps $.
	fsimp1l1_2 $f wff ch $.
	fsimp1l1_3 $f wff th $.
	fsimp1l1_4 $f wff ta $.
	fsimp1l1_5 $f wff et $.
	simp1l1 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ph ) $= fsimp1l1_0 fsimp1l1_1 fsimp1l1_2 w3a fsimp1l1_3 wa fsimp1l1_4 fsimp1l1_0 fsimp1l1_5 fsimp1l1_0 fsimp1l1_1 fsimp1l1_2 fsimp1l1_3 simpl1 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1l2_0 $f wff ph $.
	fsimp1l2_1 $f wff ps $.
	fsimp1l2_2 $f wff ch $.
	fsimp1l2_3 $f wff th $.
	fsimp1l2_4 $f wff ta $.
	fsimp1l2_5 $f wff et $.
	simp1l2 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ps ) $= fsimp1l2_0 fsimp1l2_1 fsimp1l2_2 w3a fsimp1l2_3 wa fsimp1l2_4 fsimp1l2_1 fsimp1l2_5 fsimp1l2_0 fsimp1l2_1 fsimp1l2_2 fsimp1l2_3 simpl2 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1l3_0 $f wff ph $.
	fsimp1l3_1 $f wff ps $.
	fsimp1l3_2 $f wff ch $.
	fsimp1l3_3 $f wff th $.
	fsimp1l3_4 $f wff ta $.
	fsimp1l3_5 $f wff et $.
	simp1l3 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta /\ et ) -> ch ) $= fsimp1l3_0 fsimp1l3_1 fsimp1l3_2 w3a fsimp1l3_3 wa fsimp1l3_4 fsimp1l3_2 fsimp1l3_5 fsimp1l3_0 fsimp1l3_1 fsimp1l3_2 fsimp1l3_3 simpl3 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1r1_0 $f wff ph $.
	fsimp1r1_1 $f wff ps $.
	fsimp1r1_2 $f wff ch $.
	fsimp1r1_3 $f wff th $.
	fsimp1r1_4 $f wff ta $.
	fsimp1r1_5 $f wff et $.
	simp1r1 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ph ) $= fsimp1r1_3 fsimp1r1_0 fsimp1r1_1 fsimp1r1_2 w3a wa fsimp1r1_4 fsimp1r1_0 fsimp1r1_5 fsimp1r1_3 fsimp1r1_0 fsimp1r1_1 fsimp1r1_2 simpr1 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1r2_0 $f wff ph $.
	fsimp1r2_1 $f wff ps $.
	fsimp1r2_2 $f wff ch $.
	fsimp1r2_3 $f wff th $.
	fsimp1r2_4 $f wff ta $.
	fsimp1r2_5 $f wff et $.
	simp1r2 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ps ) $= fsimp1r2_3 fsimp1r2_0 fsimp1r2_1 fsimp1r2_2 w3a wa fsimp1r2_4 fsimp1r2_1 fsimp1r2_5 fsimp1r2_3 fsimp1r2_0 fsimp1r2_1 fsimp1r2_2 simpr2 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp1r3_0 $f wff ph $.
	fsimp1r3_1 $f wff ps $.
	fsimp1r3_2 $f wff ch $.
	fsimp1r3_3 $f wff th $.
	fsimp1r3_4 $f wff ta $.
	fsimp1r3_5 $f wff et $.
	simp1r3 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch ) $= fsimp1r3_3 fsimp1r3_0 fsimp1r3_1 fsimp1r3_2 w3a wa fsimp1r3_4 fsimp1r3_2 fsimp1r3_5 fsimp1r3_3 fsimp1r3_0 fsimp1r3_1 fsimp1r3_2 simpr3 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2l1_0 $f wff ph $.
	fsimp2l1_1 $f wff ps $.
	fsimp2l1_2 $f wff ch $.
	fsimp2l1_3 $f wff th $.
	fsimp2l1_4 $f wff ta $.
	fsimp2l1_5 $f wff et $.
	simp2l1 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ph ) $= fsimp2l1_0 fsimp2l1_1 fsimp2l1_2 w3a fsimp2l1_3 wa fsimp2l1_4 fsimp2l1_0 fsimp2l1_5 fsimp2l1_0 fsimp2l1_1 fsimp2l1_2 fsimp2l1_3 simpl1 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2l2_0 $f wff ph $.
	fsimp2l2_1 $f wff ps $.
	fsimp2l2_2 $f wff ch $.
	fsimp2l2_3 $f wff th $.
	fsimp2l2_4 $f wff ta $.
	fsimp2l2_5 $f wff et $.
	simp2l2 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ps ) $= fsimp2l2_0 fsimp2l2_1 fsimp2l2_2 w3a fsimp2l2_3 wa fsimp2l2_4 fsimp2l2_1 fsimp2l2_5 fsimp2l2_0 fsimp2l2_1 fsimp2l2_2 fsimp2l2_3 simpl2 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2l3_0 $f wff ph $.
	fsimp2l3_1 $f wff ps $.
	fsimp2l3_2 $f wff ch $.
	fsimp2l3_3 $f wff th $.
	fsimp2l3_4 $f wff ta $.
	fsimp2l3_5 $f wff et $.
	simp2l3 $p |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) /\ et ) -> ch ) $= fsimp2l3_0 fsimp2l3_1 fsimp2l3_2 w3a fsimp2l3_3 wa fsimp2l3_4 fsimp2l3_2 fsimp2l3_5 fsimp2l3_0 fsimp2l3_1 fsimp2l3_2 fsimp2l3_3 simpl3 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2r1_0 $f wff ph $.
	fsimp2r1_1 $f wff ps $.
	fsimp2r1_2 $f wff ch $.
	fsimp2r1_3 $f wff th $.
	fsimp2r1_4 $f wff ta $.
	fsimp2r1_5 $f wff et $.
	simp2r1 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph ) $= fsimp2r1_3 fsimp2r1_0 fsimp2r1_1 fsimp2r1_2 w3a wa fsimp2r1_4 fsimp2r1_0 fsimp2r1_5 fsimp2r1_3 fsimp2r1_0 fsimp2r1_1 fsimp2r1_2 simpr1 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2r2_0 $f wff ph $.
	fsimp2r2_1 $f wff ps $.
	fsimp2r2_2 $f wff ch $.
	fsimp2r2_3 $f wff th $.
	fsimp2r2_4 $f wff ta $.
	fsimp2r2_5 $f wff et $.
	simp2r2 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps ) $= fsimp2r2_3 fsimp2r2_0 fsimp2r2_1 fsimp2r2_2 w3a wa fsimp2r2_4 fsimp2r2_1 fsimp2r2_5 fsimp2r2_3 fsimp2r2_0 fsimp2r2_1 fsimp2r2_2 simpr2 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp2r3_0 $f wff ph $.
	fsimp2r3_1 $f wff ps $.
	fsimp2r3_2 $f wff ch $.
	fsimp2r3_3 $f wff th $.
	fsimp2r3_4 $f wff ta $.
	fsimp2r3_5 $f wff et $.
	simp2r3 $p |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch ) $= fsimp2r3_3 fsimp2r3_0 fsimp2r3_1 fsimp2r3_2 w3a wa fsimp2r3_4 fsimp2r3_2 fsimp2r3_5 fsimp2r3_3 fsimp2r3_0 fsimp2r3_1 fsimp2r3_2 simpr3 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3l1_0 $f wff ph $.
	fsimp3l1_1 $f wff ps $.
	fsimp3l1_2 $f wff ch $.
	fsimp3l1_3 $f wff th $.
	fsimp3l1_4 $f wff ta $.
	fsimp3l1_5 $f wff et $.
	simp3l1 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph ) $= fsimp3l1_0 fsimp3l1_1 fsimp3l1_2 w3a fsimp3l1_3 wa fsimp3l1_4 fsimp3l1_0 fsimp3l1_5 fsimp3l1_0 fsimp3l1_1 fsimp3l1_2 fsimp3l1_3 simpl1 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3l2_0 $f wff ph $.
	fsimp3l2_1 $f wff ps $.
	fsimp3l2_2 $f wff ch $.
	fsimp3l2_3 $f wff th $.
	fsimp3l2_4 $f wff ta $.
	fsimp3l2_5 $f wff et $.
	simp3l2 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps ) $= fsimp3l2_0 fsimp3l2_1 fsimp3l2_2 w3a fsimp3l2_3 wa fsimp3l2_4 fsimp3l2_1 fsimp3l2_5 fsimp3l2_0 fsimp3l2_1 fsimp3l2_2 fsimp3l2_3 simpl2 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3l3_0 $f wff ph $.
	fsimp3l3_1 $f wff ps $.
	fsimp3l3_2 $f wff ch $.
	fsimp3l3_3 $f wff th $.
	fsimp3l3_4 $f wff ta $.
	fsimp3l3_5 $f wff et $.
	simp3l3 $p |- ( ( ta /\ et /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch ) $= fsimp3l3_0 fsimp3l3_1 fsimp3l3_2 w3a fsimp3l3_3 wa fsimp3l3_4 fsimp3l3_2 fsimp3l3_5 fsimp3l3_0 fsimp3l3_1 fsimp3l3_2 fsimp3l3_3 simpl3 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3r1_0 $f wff ph $.
	fsimp3r1_1 $f wff ps $.
	fsimp3r1_2 $f wff ch $.
	fsimp3r1_3 $f wff th $.
	fsimp3r1_4 $f wff ta $.
	fsimp3r1_5 $f wff et $.
	simp3r1 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= fsimp3r1_3 fsimp3r1_0 fsimp3r1_1 fsimp3r1_2 w3a wa fsimp3r1_4 fsimp3r1_0 fsimp3r1_5 fsimp3r1_3 fsimp3r1_0 fsimp3r1_1 fsimp3r1_2 simpr1 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3r2_0 $f wff ph $.
	fsimp3r2_1 $f wff ps $.
	fsimp3r2_2 $f wff ch $.
	fsimp3r2_3 $f wff th $.
	fsimp3r2_4 $f wff ta $.
	fsimp3r2_5 $f wff et $.
	simp3r2 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= fsimp3r2_3 fsimp3r2_0 fsimp3r2_1 fsimp3r2_2 w3a wa fsimp3r2_4 fsimp3r2_1 fsimp3r2_5 fsimp3r2_3 fsimp3r2_0 fsimp3r2_1 fsimp3r2_2 simpr2 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp3r3_0 $f wff ph $.
	fsimp3r3_1 $f wff ps $.
	fsimp3r3_2 $f wff ch $.
	fsimp3r3_3 $f wff th $.
	fsimp3r3_4 $f wff ta $.
	fsimp3r3_5 $f wff et $.
	simp3r3 $p |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= fsimp3r3_3 fsimp3r3_0 fsimp3r3_1 fsimp3r3_2 w3a wa fsimp3r3_4 fsimp3r3_2 fsimp3r3_5 fsimp3r3_3 fsimp3r3_0 fsimp3r3_1 fsimp3r3_2 simpr3 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp11l_0 $f wff ph $.
	fsimp11l_1 $f wff ps $.
	fsimp11l_2 $f wff ch $.
	fsimp11l_3 $f wff th $.
	fsimp11l_4 $f wff ta $.
	fsimp11l_5 $f wff et $.
	simp11l $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ph ) $= fsimp11l_0 fsimp11l_1 wa fsimp11l_2 fsimp11l_3 w3a fsimp11l_4 fsimp11l_0 fsimp11l_5 fsimp11l_0 fsimp11l_1 fsimp11l_2 fsimp11l_3 simp1l 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp11r_0 $f wff ph $.
	fsimp11r_1 $f wff ps $.
	fsimp11r_2 $f wff ch $.
	fsimp11r_3 $f wff th $.
	fsimp11r_4 $f wff ta $.
	fsimp11r_5 $f wff et $.
	simp11r $p |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta /\ et ) -> ps ) $= fsimp11r_0 fsimp11r_1 wa fsimp11r_2 fsimp11r_3 w3a fsimp11r_4 fsimp11r_1 fsimp11r_5 fsimp11r_0 fsimp11r_1 fsimp11r_2 fsimp11r_3 simp1r 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp12l_0 $f wff ph $.
	fsimp12l_1 $f wff ps $.
	fsimp12l_2 $f wff ch $.
	fsimp12l_3 $f wff th $.
	fsimp12l_4 $f wff ta $.
	fsimp12l_5 $f wff et $.
	simp12l $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ph ) $= fsimp12l_2 fsimp12l_0 fsimp12l_1 wa fsimp12l_3 w3a fsimp12l_4 fsimp12l_0 fsimp12l_5 fsimp12l_2 fsimp12l_0 fsimp12l_1 fsimp12l_3 simp2l 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp12r_0 $f wff ph $.
	fsimp12r_1 $f wff ps $.
	fsimp12r_2 $f wff ch $.
	fsimp12r_3 $f wff th $.
	fsimp12r_4 $f wff ta $.
	fsimp12r_5 $f wff et $.
	simp12r $p |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps ) $= fsimp12r_2 fsimp12r_0 fsimp12r_1 wa fsimp12r_3 w3a fsimp12r_4 fsimp12r_1 fsimp12r_5 fsimp12r_2 fsimp12r_0 fsimp12r_1 fsimp12r_3 simp2r 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp13l_0 $f wff ph $.
	fsimp13l_1 $f wff ps $.
	fsimp13l_2 $f wff ch $.
	fsimp13l_3 $f wff th $.
	fsimp13l_4 $f wff ta $.
	fsimp13l_5 $f wff et $.
	simp13l $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ph ) $= fsimp13l_2 fsimp13l_3 fsimp13l_0 fsimp13l_1 wa w3a fsimp13l_4 fsimp13l_0 fsimp13l_5 fsimp13l_2 fsimp13l_3 fsimp13l_0 fsimp13l_1 simp3l 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp13r_0 $f wff ph $.
	fsimp13r_1 $f wff ps $.
	fsimp13r_2 $f wff ch $.
	fsimp13r_3 $f wff th $.
	fsimp13r_4 $f wff ta $.
	fsimp13r_5 $f wff et $.
	simp13r $p |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps ) $= fsimp13r_2 fsimp13r_3 fsimp13r_0 fsimp13r_1 wa w3a fsimp13r_4 fsimp13r_1 fsimp13r_5 fsimp13r_2 fsimp13r_3 fsimp13r_0 fsimp13r_1 simp3r 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp21l_0 $f wff ph $.
	fsimp21l_1 $f wff ps $.
	fsimp21l_2 $f wff ch $.
	fsimp21l_3 $f wff th $.
	fsimp21l_4 $f wff ta $.
	fsimp21l_5 $f wff et $.
	simp21l $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ph ) $= fsimp21l_0 fsimp21l_1 wa fsimp21l_2 fsimp21l_3 w3a fsimp21l_4 fsimp21l_0 fsimp21l_5 fsimp21l_0 fsimp21l_1 fsimp21l_2 fsimp21l_3 simp1l 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp21r_0 $f wff ph $.
	fsimp21r_1 $f wff ps $.
	fsimp21r_2 $f wff ch $.
	fsimp21r_3 $f wff th $.
	fsimp21r_4 $f wff ta $.
	fsimp21r_5 $f wff et $.
	simp21r $p |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) /\ et ) -> ps ) $= fsimp21r_0 fsimp21r_1 wa fsimp21r_2 fsimp21r_3 w3a fsimp21r_4 fsimp21r_1 fsimp21r_5 fsimp21r_0 fsimp21r_1 fsimp21r_2 fsimp21r_3 simp1r 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp22l_0 $f wff ph $.
	fsimp22l_1 $f wff ps $.
	fsimp22l_2 $f wff ch $.
	fsimp22l_3 $f wff th $.
	fsimp22l_4 $f wff ta $.
	fsimp22l_5 $f wff et $.
	simp22l $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph ) $= fsimp22l_2 fsimp22l_0 fsimp22l_1 wa fsimp22l_3 w3a fsimp22l_4 fsimp22l_0 fsimp22l_5 fsimp22l_2 fsimp22l_0 fsimp22l_1 fsimp22l_3 simp2l 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp22r_0 $f wff ph $.
	fsimp22r_1 $f wff ps $.
	fsimp22r_2 $f wff ch $.
	fsimp22r_3 $f wff th $.
	fsimp22r_4 $f wff ta $.
	fsimp22r_5 $f wff et $.
	simp22r $p |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ps ) $= fsimp22r_2 fsimp22r_0 fsimp22r_1 wa fsimp22r_3 w3a fsimp22r_4 fsimp22r_1 fsimp22r_5 fsimp22r_2 fsimp22r_0 fsimp22r_1 fsimp22r_3 simp2r 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp23l_0 $f wff ph $.
	fsimp23l_1 $f wff ps $.
	fsimp23l_2 $f wff ch $.
	fsimp23l_3 $f wff th $.
	fsimp23l_4 $f wff ta $.
	fsimp23l_5 $f wff et $.
	simp23l $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph ) $= fsimp23l_2 fsimp23l_3 fsimp23l_0 fsimp23l_1 wa w3a fsimp23l_4 fsimp23l_0 fsimp23l_5 fsimp23l_2 fsimp23l_3 fsimp23l_0 fsimp23l_1 simp3l 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp23r_0 $f wff ph $.
	fsimp23r_1 $f wff ps $.
	fsimp23r_2 $f wff ch $.
	fsimp23r_3 $f wff th $.
	fsimp23r_4 $f wff ta $.
	fsimp23r_5 $f wff et $.
	simp23r $p |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps ) $= fsimp23r_2 fsimp23r_3 fsimp23r_0 fsimp23r_1 wa w3a fsimp23r_4 fsimp23r_1 fsimp23r_5 fsimp23r_2 fsimp23r_3 fsimp23r_0 fsimp23r_1 simp3r 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp31l_0 $f wff ph $.
	fsimp31l_1 $f wff ps $.
	fsimp31l_2 $f wff ch $.
	fsimp31l_3 $f wff th $.
	fsimp31l_4 $f wff ta $.
	fsimp31l_5 $f wff et $.
	simp31l $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph ) $= fsimp31l_0 fsimp31l_1 wa fsimp31l_2 fsimp31l_3 w3a fsimp31l_4 fsimp31l_0 fsimp31l_5 fsimp31l_0 fsimp31l_1 fsimp31l_2 fsimp31l_3 simp1l 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp31r_0 $f wff ph $.
	fsimp31r_1 $f wff ps $.
	fsimp31r_2 $f wff ch $.
	fsimp31r_3 $f wff th $.
	fsimp31r_4 $f wff ta $.
	fsimp31r_5 $f wff et $.
	simp31r $p |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps ) $= fsimp31r_0 fsimp31r_1 wa fsimp31r_2 fsimp31r_3 w3a fsimp31r_4 fsimp31r_1 fsimp31r_5 fsimp31r_0 fsimp31r_1 fsimp31r_2 fsimp31r_3 simp1r 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp32l_0 $f wff ph $.
	fsimp32l_1 $f wff ps $.
	fsimp32l_2 $f wff ch $.
	fsimp32l_3 $f wff th $.
	fsimp32l_4 $f wff ta $.
	fsimp32l_5 $f wff et $.
	simp32l $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph ) $= fsimp32l_2 fsimp32l_0 fsimp32l_1 wa fsimp32l_3 w3a fsimp32l_4 fsimp32l_0 fsimp32l_5 fsimp32l_2 fsimp32l_0 fsimp32l_1 fsimp32l_3 simp2l 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp32r_0 $f wff ph $.
	fsimp32r_1 $f wff ps $.
	fsimp32r_2 $f wff ch $.
	fsimp32r_3 $f wff th $.
	fsimp32r_4 $f wff ta $.
	fsimp32r_5 $f wff et $.
	simp32r $p |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps ) $= fsimp32r_2 fsimp32r_0 fsimp32r_1 wa fsimp32r_3 w3a fsimp32r_4 fsimp32r_1 fsimp32r_5 fsimp32r_2 fsimp32r_0 fsimp32r_1 fsimp32r_3 simp2r 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp33l_0 $f wff ph $.
	fsimp33l_1 $f wff ps $.
	fsimp33l_2 $f wff ch $.
	fsimp33l_3 $f wff th $.
	fsimp33l_4 $f wff ta $.
	fsimp33l_5 $f wff et $.
	simp33l $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph ) $= fsimp33l_2 fsimp33l_3 fsimp33l_0 fsimp33l_1 wa w3a fsimp33l_4 fsimp33l_0 fsimp33l_5 fsimp33l_2 fsimp33l_3 fsimp33l_0 fsimp33l_1 simp3l 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsimp33r_0 $f wff ph $.
	fsimp33r_1 $f wff ps $.
	fsimp33r_2 $f wff ch $.
	fsimp33r_3 $f wff th $.
	fsimp33r_4 $f wff ta $.
	fsimp33r_5 $f wff et $.
	simp33r $p |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps ) $= fsimp33r_2 fsimp33r_3 fsimp33r_0 fsimp33r_1 wa w3a fsimp33r_4 fsimp33r_1 fsimp33r_5 fsimp33r_2 fsimp33r_3 fsimp33r_0 fsimp33r_1 simp3r 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp111_0 $f wff ph $.
	fsimp111_1 $f wff ps $.
	fsimp111_2 $f wff ch $.
	fsimp111_3 $f wff th $.
	fsimp111_4 $f wff ta $.
	fsimp111_5 $f wff et $.
	fsimp111_6 $f wff ze $.
	simp111 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ph ) $= fsimp111_0 fsimp111_1 fsimp111_2 w3a fsimp111_3 fsimp111_4 w3a fsimp111_5 fsimp111_0 fsimp111_6 fsimp111_0 fsimp111_1 fsimp111_2 fsimp111_3 fsimp111_4 simp11 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp112_0 $f wff ph $.
	fsimp112_1 $f wff ps $.
	fsimp112_2 $f wff ch $.
	fsimp112_3 $f wff th $.
	fsimp112_4 $f wff ta $.
	fsimp112_5 $f wff et $.
	fsimp112_6 $f wff ze $.
	simp112 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps ) $= fsimp112_0 fsimp112_1 fsimp112_2 w3a fsimp112_3 fsimp112_4 w3a fsimp112_5 fsimp112_1 fsimp112_6 fsimp112_0 fsimp112_1 fsimp112_2 fsimp112_3 fsimp112_4 simp12 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp113_0 $f wff ph $.
	fsimp113_1 $f wff ps $.
	fsimp113_2 $f wff ch $.
	fsimp113_3 $f wff th $.
	fsimp113_4 $f wff ta $.
	fsimp113_5 $f wff et $.
	fsimp113_6 $f wff ze $.
	simp113 $p |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch ) $= fsimp113_0 fsimp113_1 fsimp113_2 w3a fsimp113_3 fsimp113_4 w3a fsimp113_5 fsimp113_2 fsimp113_6 fsimp113_0 fsimp113_1 fsimp113_2 fsimp113_3 fsimp113_4 simp13 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp121_0 $f wff ph $.
	fsimp121_1 $f wff ps $.
	fsimp121_2 $f wff ch $.
	fsimp121_3 $f wff th $.
	fsimp121_4 $f wff ta $.
	fsimp121_5 $f wff et $.
	fsimp121_6 $f wff ze $.
	simp121 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ph ) $= fsimp121_3 fsimp121_0 fsimp121_1 fsimp121_2 w3a fsimp121_4 w3a fsimp121_5 fsimp121_0 fsimp121_6 fsimp121_3 fsimp121_0 fsimp121_1 fsimp121_2 fsimp121_4 simp21 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp122_0 $f wff ph $.
	fsimp122_1 $f wff ps $.
	fsimp122_2 $f wff ch $.
	fsimp122_3 $f wff th $.
	fsimp122_4 $f wff ta $.
	fsimp122_5 $f wff et $.
	fsimp122_6 $f wff ze $.
	simp122 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ps ) $= fsimp122_3 fsimp122_0 fsimp122_1 fsimp122_2 w3a fsimp122_4 w3a fsimp122_5 fsimp122_1 fsimp122_6 fsimp122_3 fsimp122_0 fsimp122_1 fsimp122_2 fsimp122_4 simp22 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp123_0 $f wff ph $.
	fsimp123_1 $f wff ps $.
	fsimp123_2 $f wff ch $.
	fsimp123_3 $f wff th $.
	fsimp123_4 $f wff ta $.
	fsimp123_5 $f wff et $.
	fsimp123_6 $f wff ze $.
	simp123 $p |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et /\ ze ) -> ch ) $= fsimp123_3 fsimp123_0 fsimp123_1 fsimp123_2 w3a fsimp123_4 w3a fsimp123_5 fsimp123_2 fsimp123_6 fsimp123_3 fsimp123_0 fsimp123_1 fsimp123_2 fsimp123_4 simp23 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp131_0 $f wff ph $.
	fsimp131_1 $f wff ps $.
	fsimp131_2 $f wff ch $.
	fsimp131_3 $f wff th $.
	fsimp131_4 $f wff ta $.
	fsimp131_5 $f wff et $.
	fsimp131_6 $f wff ze $.
	simp131 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ph ) $= fsimp131_3 fsimp131_4 fsimp131_0 fsimp131_1 fsimp131_2 w3a w3a fsimp131_5 fsimp131_0 fsimp131_6 fsimp131_3 fsimp131_4 fsimp131_0 fsimp131_1 fsimp131_2 simp31 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp132_0 $f wff ph $.
	fsimp132_1 $f wff ps $.
	fsimp132_2 $f wff ch $.
	fsimp132_3 $f wff th $.
	fsimp132_4 $f wff ta $.
	fsimp132_5 $f wff et $.
	fsimp132_6 $f wff ze $.
	simp132 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ps ) $= fsimp132_3 fsimp132_4 fsimp132_0 fsimp132_1 fsimp132_2 w3a w3a fsimp132_5 fsimp132_1 fsimp132_6 fsimp132_3 fsimp132_4 fsimp132_0 fsimp132_1 fsimp132_2 simp32 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp133_0 $f wff ph $.
	fsimp133_1 $f wff ps $.
	fsimp133_2 $f wff ch $.
	fsimp133_3 $f wff th $.
	fsimp133_4 $f wff ta $.
	fsimp133_5 $f wff et $.
	fsimp133_6 $f wff ze $.
	simp133 $p |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et /\ ze ) -> ch ) $= fsimp133_3 fsimp133_4 fsimp133_0 fsimp133_1 fsimp133_2 w3a w3a fsimp133_5 fsimp133_2 fsimp133_6 fsimp133_3 fsimp133_4 fsimp133_0 fsimp133_1 fsimp133_2 simp33 3ad2ant1 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp211_0 $f wff ph $.
	fsimp211_1 $f wff ps $.
	fsimp211_2 $f wff ch $.
	fsimp211_3 $f wff th $.
	fsimp211_4 $f wff ta $.
	fsimp211_5 $f wff et $.
	fsimp211_6 $f wff ze $.
	simp211 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ph ) $= fsimp211_0 fsimp211_1 fsimp211_2 w3a fsimp211_3 fsimp211_4 w3a fsimp211_5 fsimp211_0 fsimp211_6 fsimp211_0 fsimp211_1 fsimp211_2 fsimp211_3 fsimp211_4 simp11 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp212_0 $f wff ph $.
	fsimp212_1 $f wff ps $.
	fsimp212_2 $f wff ch $.
	fsimp212_3 $f wff th $.
	fsimp212_4 $f wff ta $.
	fsimp212_5 $f wff et $.
	fsimp212_6 $f wff ze $.
	simp212 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ps ) $= fsimp212_0 fsimp212_1 fsimp212_2 w3a fsimp212_3 fsimp212_4 w3a fsimp212_5 fsimp212_1 fsimp212_6 fsimp212_0 fsimp212_1 fsimp212_2 fsimp212_3 fsimp212_4 simp12 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp213_0 $f wff ph $.
	fsimp213_1 $f wff ps $.
	fsimp213_2 $f wff ch $.
	fsimp213_3 $f wff th $.
	fsimp213_4 $f wff ta $.
	fsimp213_5 $f wff et $.
	fsimp213_6 $f wff ze $.
	simp213 $p |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch ) $= fsimp213_0 fsimp213_1 fsimp213_2 w3a fsimp213_3 fsimp213_4 w3a fsimp213_5 fsimp213_2 fsimp213_6 fsimp213_0 fsimp213_1 fsimp213_2 fsimp213_3 fsimp213_4 simp13 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp221_0 $f wff ph $.
	fsimp221_1 $f wff ps $.
	fsimp221_2 $f wff ch $.
	fsimp221_3 $f wff th $.
	fsimp221_4 $f wff ta $.
	fsimp221_5 $f wff et $.
	fsimp221_6 $f wff ze $.
	simp221 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ph ) $= fsimp221_3 fsimp221_0 fsimp221_1 fsimp221_2 w3a fsimp221_4 w3a fsimp221_5 fsimp221_0 fsimp221_6 fsimp221_3 fsimp221_0 fsimp221_1 fsimp221_2 fsimp221_4 simp21 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp222_0 $f wff ph $.
	fsimp222_1 $f wff ps $.
	fsimp222_2 $f wff ch $.
	fsimp222_3 $f wff th $.
	fsimp222_4 $f wff ta $.
	fsimp222_5 $f wff et $.
	fsimp222_6 $f wff ze $.
	simp222 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps ) $= fsimp222_3 fsimp222_0 fsimp222_1 fsimp222_2 w3a fsimp222_4 w3a fsimp222_5 fsimp222_1 fsimp222_6 fsimp222_3 fsimp222_0 fsimp222_1 fsimp222_2 fsimp222_4 simp22 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp223_0 $f wff ph $.
	fsimp223_1 $f wff ps $.
	fsimp223_2 $f wff ch $.
	fsimp223_3 $f wff th $.
	fsimp223_4 $f wff ta $.
	fsimp223_5 $f wff et $.
	fsimp223_6 $f wff ze $.
	simp223 $p |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ch ) $= fsimp223_3 fsimp223_0 fsimp223_1 fsimp223_2 w3a fsimp223_4 w3a fsimp223_5 fsimp223_2 fsimp223_6 fsimp223_3 fsimp223_0 fsimp223_1 fsimp223_2 fsimp223_4 simp23 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp231_0 $f wff ph $.
	fsimp231_1 $f wff ps $.
	fsimp231_2 $f wff ch $.
	fsimp231_3 $f wff th $.
	fsimp231_4 $f wff ta $.
	fsimp231_5 $f wff et $.
	fsimp231_6 $f wff ze $.
	simp231 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ph ) $= fsimp231_3 fsimp231_4 fsimp231_0 fsimp231_1 fsimp231_2 w3a w3a fsimp231_5 fsimp231_0 fsimp231_6 fsimp231_3 fsimp231_4 fsimp231_0 fsimp231_1 fsimp231_2 simp31 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp232_0 $f wff ph $.
	fsimp232_1 $f wff ps $.
	fsimp232_2 $f wff ch $.
	fsimp232_3 $f wff th $.
	fsimp232_4 $f wff ta $.
	fsimp232_5 $f wff et $.
	fsimp232_6 $f wff ze $.
	simp232 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps ) $= fsimp232_3 fsimp232_4 fsimp232_0 fsimp232_1 fsimp232_2 w3a w3a fsimp232_5 fsimp232_1 fsimp232_6 fsimp232_3 fsimp232_4 fsimp232_0 fsimp232_1 fsimp232_2 simp32 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp233_0 $f wff ph $.
	fsimp233_1 $f wff ps $.
	fsimp233_2 $f wff ch $.
	fsimp233_3 $f wff th $.
	fsimp233_4 $f wff ta $.
	fsimp233_5 $f wff et $.
	fsimp233_6 $f wff ze $.
	simp233 $p |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ch ) $= fsimp233_3 fsimp233_4 fsimp233_0 fsimp233_1 fsimp233_2 w3a w3a fsimp233_5 fsimp233_2 fsimp233_6 fsimp233_3 fsimp233_4 fsimp233_0 fsimp233_1 fsimp233_2 simp33 3ad2ant2 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp311_0 $f wff ph $.
	fsimp311_1 $f wff ps $.
	fsimp311_2 $f wff ch $.
	fsimp311_3 $f wff th $.
	fsimp311_4 $f wff ta $.
	fsimp311_5 $f wff et $.
	fsimp311_6 $f wff ze $.
	simp311 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ph ) $= fsimp311_0 fsimp311_1 fsimp311_2 w3a fsimp311_3 fsimp311_4 w3a fsimp311_5 fsimp311_0 fsimp311_6 fsimp311_0 fsimp311_1 fsimp311_2 fsimp311_3 fsimp311_4 simp11 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp312_0 $f wff ph $.
	fsimp312_1 $f wff ps $.
	fsimp312_2 $f wff ch $.
	fsimp312_3 $f wff th $.
	fsimp312_4 $f wff ta $.
	fsimp312_5 $f wff et $.
	fsimp312_6 $f wff ze $.
	simp312 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ps ) $= fsimp312_0 fsimp312_1 fsimp312_2 w3a fsimp312_3 fsimp312_4 w3a fsimp312_5 fsimp312_1 fsimp312_6 fsimp312_0 fsimp312_1 fsimp312_2 fsimp312_3 fsimp312_4 simp12 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp313_0 $f wff ph $.
	fsimp313_1 $f wff ps $.
	fsimp313_2 $f wff ch $.
	fsimp313_3 $f wff th $.
	fsimp313_4 $f wff ta $.
	fsimp313_5 $f wff et $.
	fsimp313_6 $f wff ze $.
	simp313 $p |- ( ( et /\ ze /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch ) $= fsimp313_0 fsimp313_1 fsimp313_2 w3a fsimp313_3 fsimp313_4 w3a fsimp313_5 fsimp313_2 fsimp313_6 fsimp313_0 fsimp313_1 fsimp313_2 fsimp313_3 fsimp313_4 simp13 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp321_0 $f wff ph $.
	fsimp321_1 $f wff ps $.
	fsimp321_2 $f wff ch $.
	fsimp321_3 $f wff th $.
	fsimp321_4 $f wff ta $.
	fsimp321_5 $f wff et $.
	fsimp321_6 $f wff ze $.
	simp321 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ph ) $= fsimp321_3 fsimp321_0 fsimp321_1 fsimp321_2 w3a fsimp321_4 w3a fsimp321_5 fsimp321_0 fsimp321_6 fsimp321_3 fsimp321_0 fsimp321_1 fsimp321_2 fsimp321_4 simp21 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp322_0 $f wff ph $.
	fsimp322_1 $f wff ps $.
	fsimp322_2 $f wff ch $.
	fsimp322_3 $f wff th $.
	fsimp322_4 $f wff ta $.
	fsimp322_5 $f wff et $.
	fsimp322_6 $f wff ze $.
	simp322 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ps ) $= fsimp322_3 fsimp322_0 fsimp322_1 fsimp322_2 w3a fsimp322_4 w3a fsimp322_5 fsimp322_1 fsimp322_6 fsimp322_3 fsimp322_0 fsimp322_1 fsimp322_2 fsimp322_4 simp22 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp323_0 $f wff ph $.
	fsimp323_1 $f wff ps $.
	fsimp323_2 $f wff ch $.
	fsimp323_3 $f wff th $.
	fsimp323_4 $f wff ta $.
	fsimp323_5 $f wff et $.
	fsimp323_6 $f wff ze $.
	simp323 $p |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch ) $= fsimp323_3 fsimp323_0 fsimp323_1 fsimp323_2 w3a fsimp323_4 w3a fsimp323_5 fsimp323_2 fsimp323_6 fsimp323_3 fsimp323_0 fsimp323_1 fsimp323_2 fsimp323_4 simp23 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp331_0 $f wff ph $.
	fsimp331_1 $f wff ps $.
	fsimp331_2 $f wff ch $.
	fsimp331_3 $f wff th $.
	fsimp331_4 $f wff ta $.
	fsimp331_5 $f wff et $.
	fsimp331_6 $f wff ze $.
	simp331 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph ) $= fsimp331_3 fsimp331_4 fsimp331_0 fsimp331_1 fsimp331_2 w3a w3a fsimp331_5 fsimp331_0 fsimp331_6 fsimp331_3 fsimp331_4 fsimp331_0 fsimp331_1 fsimp331_2 simp31 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp332_0 $f wff ph $.
	fsimp332_1 $f wff ps $.
	fsimp332_2 $f wff ch $.
	fsimp332_3 $f wff th $.
	fsimp332_4 $f wff ta $.
	fsimp332_5 $f wff et $.
	fsimp332_6 $f wff ze $.
	simp332 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps ) $= fsimp332_3 fsimp332_4 fsimp332_0 fsimp332_1 fsimp332_2 w3a w3a fsimp332_5 fsimp332_1 fsimp332_6 fsimp332_3 fsimp332_4 fsimp332_0 fsimp332_1 fsimp332_2 simp32 3ad2ant3 $.
$}
$( Simplification of conjunction.  (Contributed by NM, 9-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsimp333_0 $f wff ph $.
	fsimp333_1 $f wff ps $.
	fsimp333_2 $f wff ch $.
	fsimp333_3 $f wff th $.
	fsimp333_4 $f wff ta $.
	fsimp333_5 $f wff et $.
	fsimp333_6 $f wff ze $.
	simp333 $p |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch ) $= fsimp333_3 fsimp333_4 fsimp333_0 fsimp333_1 fsimp333_2 w3a w3a fsimp333_5 fsimp333_2 fsimp333_6 fsimp333_3 fsimp333_4 fsimp333_0 fsimp333_1 fsimp333_2 simp33 3ad2ant3 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantl1_0 $f wff ph $.
	f3adantl1_1 $f wff ps $.
	f3adantl1_2 $f wff ch $.
	f3adantl1_3 $f wff th $.
	f3adantl1_4 $f wff ta $.
	e3adantl1_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	3adantl1 $p |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th ) $= f3adantl1_4 f3adantl1_0 f3adantl1_1 w3a f3adantl1_0 f3adantl1_1 wa f3adantl1_2 f3adantl1_3 f3adantl1_4 f3adantl1_0 f3adantl1_1 3simpc e3adantl1_0 sylan $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantl2_0 $f wff ph $.
	f3adantl2_1 $f wff ps $.
	f3adantl2_2 $f wff ch $.
	f3adantl2_3 $f wff th $.
	f3adantl2_4 $f wff ta $.
	e3adantl2_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	3adantl2 $p |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th ) $= f3adantl2_0 f3adantl2_4 f3adantl2_1 w3a f3adantl2_0 f3adantl2_1 wa f3adantl2_2 f3adantl2_3 f3adantl2_0 f3adantl2_4 f3adantl2_1 3simpb e3adantl2_0 sylan $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantl3_0 $f wff ph $.
	f3adantl3_1 $f wff ps $.
	f3adantl3_2 $f wff ch $.
	f3adantl3_3 $f wff th $.
	f3adantl3_4 $f wff ta $.
	e3adantl3_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	3adantl3 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $= f3adantl3_0 f3adantl3_1 f3adantl3_4 w3a f3adantl3_0 f3adantl3_1 wa f3adantl3_2 f3adantl3_3 f3adantl3_0 f3adantl3_1 f3adantl3_4 3simpa e3adantl3_0 sylan $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantr1_0 $f wff ph $.
	f3adantr1_1 $f wff ps $.
	f3adantr1_2 $f wff ch $.
	f3adantr1_3 $f wff th $.
	f3adantr1_4 $f wff ta $.
	e3adantr1_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	3adantr1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $= f3adantr1_4 f3adantr1_1 f3adantr1_2 w3a f3adantr1_0 f3adantr1_1 f3adantr1_2 wa f3adantr1_3 f3adantr1_4 f3adantr1_1 f3adantr1_2 3simpc e3adantr1_0 sylan2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantr2_0 $f wff ph $.
	f3adantr2_1 $f wff ps $.
	f3adantr2_2 $f wff ch $.
	f3adantr2_3 $f wff th $.
	f3adantr2_4 $f wff ta $.
	e3adantr2_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	3adantr2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= f3adantr2_1 f3adantr2_4 f3adantr2_2 w3a f3adantr2_0 f3adantr2_1 f3adantr2_2 wa f3adantr2_3 f3adantr2_1 f3adantr2_4 f3adantr2_2 3simpb e3adantr2_0 sylan2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       27-Apr-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adantr3_0 $f wff ph $.
	f3adantr3_1 $f wff ps $.
	f3adantr3_2 $f wff ch $.
	f3adantr3_3 $f wff th $.
	f3adantr3_4 $f wff ta $.
	e3adantr3_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	3adantr3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= f3adantr3_1 f3adantr3_2 f3adantr3_4 w3a f3adantr3_0 f3adantr3_1 f3adantr3_2 wa f3adantr3_3 f3adantr3_1 f3adantr3_2 f3adantr3_4 3simpa e3adantr3_0 sylan2 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antl1_0 $f wff ph $.
	f3ad2antl1_1 $f wff ps $.
	f3ad2antl1_2 $f wff ch $.
	f3ad2antl1_3 $f wff th $.
	f3ad2antl1_4 $f wff ta $.
	e3ad2antl1_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antl1 $p |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th ) $= f3ad2antl1_0 f3ad2antl1_4 f3ad2antl1_2 f3ad2antl1_3 f3ad2antl1_1 f3ad2antl1_0 f3ad2antl1_2 f3ad2antl1_3 f3ad2antl1_4 e3ad2antl1_0 adantlr 3adantl2 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antl2_0 $f wff ph $.
	f3ad2antl2_1 $f wff ps $.
	f3ad2antl2_2 $f wff ch $.
	f3ad2antl2_3 $f wff th $.
	f3ad2antl2_4 $f wff ta $.
	e3ad2antl2_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antl2 $p |- ( ( ( ps /\ ph /\ ta ) /\ ch ) -> th ) $= f3ad2antl2_0 f3ad2antl2_4 f3ad2antl2_2 f3ad2antl2_3 f3ad2antl2_1 f3ad2antl2_0 f3ad2antl2_2 f3ad2antl2_3 f3ad2antl2_4 e3ad2antl2_0 adantlr 3adantl1 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       4-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antl3_0 $f wff ph $.
	f3ad2antl3_1 $f wff ps $.
	f3ad2antl3_2 $f wff ch $.
	f3ad2antl3_3 $f wff th $.
	f3ad2antl3_4 $f wff ta $.
	e3ad2antl3_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antl3 $p |- ( ( ( ps /\ ta /\ ph ) /\ ch ) -> th ) $= f3ad2antl3_4 f3ad2antl3_0 f3ad2antl3_2 f3ad2antl3_3 f3ad2antl3_1 f3ad2antl3_0 f3ad2antl3_2 f3ad2antl3_3 f3ad2antl3_4 e3ad2antl3_0 adantll 3adantl1 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       25-Dec-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antr1_0 $f wff ph $.
	f3ad2antr1_1 $f wff ps $.
	f3ad2antr1_2 $f wff ch $.
	f3ad2antr1_3 $f wff th $.
	f3ad2antr1_4 $f wff ta $.
	e3ad2antr1_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antr1 $p |- ( ( ph /\ ( ch /\ ps /\ ta ) ) -> th ) $= f3ad2antr1_0 f3ad2antr1_2 f3ad2antr1_1 f3ad2antr1_3 f3ad2antr1_4 f3ad2antr1_0 f3ad2antr1_2 f3ad2antr1_3 f3ad2antr1_1 e3ad2antr1_0 adantrr 3adantr3 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       27-Dec-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antr2_0 $f wff ph $.
	f3ad2antr2_1 $f wff ps $.
	f3ad2antr2_2 $f wff ch $.
	f3ad2antr2_3 $f wff th $.
	f3ad2antr2_4 $f wff ta $.
	e3ad2antr2_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antr2 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= f3ad2antr2_0 f3ad2antr2_1 f3ad2antr2_2 f3ad2antr2_3 f3ad2antr2_4 f3ad2antr2_0 f3ad2antr2_2 f3ad2antr2_3 f3ad2antr2_1 e3ad2antr2_0 adantrl 3adantr3 $.
$}
$( Deduction adding conjuncts to antecedent.  (Contributed by NM,
       30-Dec-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3ad2antr3_0 $f wff ph $.
	f3ad2antr3_1 $f wff ps $.
	f3ad2antr3_2 $f wff ch $.
	f3ad2antr3_3 $f wff th $.
	f3ad2antr3_4 $f wff ta $.
	e3ad2antr3_0 $e |- ( ( ph /\ ch ) -> th ) $.
	3ad2antr3 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= f3ad2antr3_0 f3ad2antr3_4 f3ad2antr3_2 f3ad2antr3_3 f3ad2antr3_1 f3ad2antr3_0 f3ad2antr3_2 f3ad2antr3_3 f3ad2antr3_4 e3ad2antr3_0 adantrl 3adantr1 $.
$}
$( Remove a hypothesis from the second member of a biimplication.
       (Contributed by FL, 22-Jul-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anibar_0 $f wff ph $.
	f3anibar_1 $f wff ps $.
	f3anibar_2 $f wff ch $.
	f3anibar_3 $f wff th $.
	f3anibar_4 $f wff ta $.
	e3anibar_0 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ( ch /\ ta ) ) ) $.
	3anibar $p |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $= f3anibar_0 f3anibar_1 f3anibar_2 w3a f3anibar_3 f3anibar_2 f3anibar_4 wa f3anibar_4 e3anibar_0 f3anibar_0 f3anibar_1 f3anibar_2 w3a f3anibar_2 f3anibar_4 f3anibar_0 f3anibar_1 f3anibar_2 simp3 biantrurd bitr4d $.
$}
$( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix1_0 $f wff ph $.
	f3mix1_1 $f wff ps $.
	f3mix1_2 $f wff ch $.
	3mix1 $p |- ( ph -> ( ph \/ ps \/ ch ) ) $= f3mix1_0 f3mix1_0 f3mix1_1 f3mix1_2 wo wo f3mix1_0 f3mix1_1 f3mix1_2 w3o f3mix1_0 f3mix1_1 f3mix1_2 wo orc f3mix1_0 f3mix1_1 f3mix1_2 3orass sylibr $.
$}
$( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix2_0 $f wff ph $.
	f3mix2_1 $f wff ps $.
	f3mix2_2 $f wff ch $.
	3mix2 $p |- ( ph -> ( ps \/ ph \/ ch ) ) $= f3mix2_0 f3mix2_0 f3mix2_2 f3mix2_1 w3o f3mix2_1 f3mix2_0 f3mix2_2 w3o f3mix2_0 f3mix2_2 f3mix2_1 3mix1 f3mix2_1 f3mix2_0 f3mix2_2 3orrot sylibr $.
$}
$( Introduction in triple disjunction.  (Contributed by NM, 4-Apr-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix3_0 $f wff ph $.
	f3mix3_1 $f wff ps $.
	f3mix3_2 $f wff ch $.
	3mix3 $p |- ( ph -> ( ps \/ ch \/ ph ) ) $= f3mix3_0 f3mix3_0 f3mix3_1 f3mix3_2 w3o f3mix3_1 f3mix3_2 f3mix3_0 w3o f3mix3_0 f3mix3_1 f3mix3_2 3mix1 f3mix3_0 f3mix3_1 f3mix3_2 3orrot sylib $.
$}
$( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix1i_0 $f wff ph $.
	f3mix1i_1 $f wff ps $.
	f3mix1i_2 $f wff ch $.
	e3mix1i_0 $e |- ph $.
	3mix1i $p |- ( ph \/ ps \/ ch ) $= f3mix1i_0 f3mix1i_0 f3mix1i_1 f3mix1i_2 w3o e3mix1i_0 f3mix1i_0 f3mix1i_1 f3mix1i_2 3mix1 ax-mp $.
$}
$( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix2i_0 $f wff ph $.
	f3mix2i_1 $f wff ps $.
	f3mix2i_2 $f wff ch $.
	e3mix2i_0 $e |- ph $.
	3mix2i $p |- ( ps \/ ph \/ ch ) $= f3mix2i_0 f3mix2i_1 f3mix2i_0 f3mix2i_2 w3o e3mix2i_0 f3mix2i_0 f3mix2i_1 f3mix2i_2 3mix2 ax-mp $.
$}
$( Introduction in triple disjunction.  (Contributed by Mario Carneiro,
       6-Oct-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3mix3i_0 $f wff ph $.
	f3mix3i_1 $f wff ps $.
	f3mix3i_2 $f wff ch $.
	e3mix3i_0 $e |- ph $.
	3mix3i $p |- ( ps \/ ch \/ ph ) $= f3mix3i_0 f3mix3i_1 f3mix3i_2 f3mix3i_0 w3o e3mix3i_0 f3mix3i_0 f3mix3i_1 f3mix3i_2 3mix3 ax-mp $.
$}
$( Infer conjunction of premises.  (Contributed by NM, 10-Feb-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3pm3.2i_0 $f wff ph $.
	f3pm3.2i_1 $f wff ps $.
	f3pm3.2i_2 $f wff ch $.
	e3pm3.2i_0 $e |- ph $.
	e3pm3.2i_1 $e |- ps $.
	e3pm3.2i_2 $e |- ch $.
	3pm3.2i $p |- ( ph /\ ps /\ ch ) $= f3pm3.2i_0 f3pm3.2i_1 f3pm3.2i_2 w3a f3pm3.2i_0 f3pm3.2i_1 wa f3pm3.2i_2 f3pm3.2i_0 f3pm3.2i_1 e3pm3.2i_0 e3pm3.2i_1 pm3.2i e3pm3.2i_2 f3pm3.2i_0 f3pm3.2i_1 f3pm3.2i_2 df-3an mpbir2an $.
$}
$( ~ pm3.2 for a triple conjunction.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fpm3.2an3_0 $f wff ph $.
	fpm3.2an3_1 $f wff ps $.
	fpm3.2an3_2 $f wff ch $.
	pm3.2an3 $p |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ) $= fpm3.2an3_0 fpm3.2an3_1 fpm3.2an3_2 fpm3.2an3_0 fpm3.2an3_1 wa fpm3.2an3_2 wa fpm3.2an3_0 fpm3.2an3_1 fpm3.2an3_2 w3a fpm3.2an3_0 fpm3.2an3_1 fpm3.2an3_2 fpm3.2an3_0 fpm3.2an3_1 wa fpm3.2an3_2 wa wi fpm3.2an3_0 fpm3.2an3_1 wa fpm3.2an3_2 pm3.2 ex fpm3.2an3_0 fpm3.2an3_1 fpm3.2an3_2 w3a fpm3.2an3_0 fpm3.2an3_1 wa fpm3.2an3_2 wa fpm3.2an3_0 fpm3.2an3_1 fpm3.2an3_2 df-3an bicomi syl8ib $.
$}
$( Join consequents with conjunction.  (Contributed by NM, 9-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3jca_0 $f wff ph $.
	f3jca_1 $f wff ps $.
	f3jca_2 $f wff ch $.
	f3jca_3 $f wff th $.
	e3jca_0 $e |- ( ph -> ps ) $.
	e3jca_1 $e |- ( ph -> ch ) $.
	e3jca_2 $e |- ( ph -> th ) $.
	3jca $p |- ( ph -> ( ps /\ ch /\ th ) ) $= f3jca_0 f3jca_1 f3jca_2 wa f3jca_3 wa f3jca_1 f3jca_2 f3jca_3 w3a f3jca_0 f3jca_1 f3jca_2 f3jca_3 e3jca_0 e3jca_1 e3jca_2 jca31 f3jca_1 f3jca_2 f3jca_3 df-3an sylibr $.
$}
$( Deduction conjoining the consequents of three implications.
       (Contributed by NM, 25-Sep-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3jcad_0 $f wff ph $.
	f3jcad_1 $f wff ps $.
	f3jcad_2 $f wff ch $.
	f3jcad_3 $f wff th $.
	f3jcad_4 $f wff ta $.
	e3jcad_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3jcad_1 $e |- ( ph -> ( ps -> th ) ) $.
	e3jcad_2 $e |- ( ph -> ( ps -> ta ) ) $.
	3jcad $p |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ) $= f3jcad_0 f3jcad_1 f3jcad_2 f3jcad_3 f3jcad_4 w3a f3jcad_0 f3jcad_1 wa f3jcad_2 f3jcad_3 f3jcad_4 f3jcad_0 f3jcad_1 f3jcad_2 e3jcad_0 imp f3jcad_0 f3jcad_1 f3jcad_3 e3jcad_1 imp f3jcad_0 f3jcad_1 f3jcad_4 e3jcad_2 imp 3jca ex $.
$}
$( Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       16-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpbir3an_0 $f wff ph $.
	fmpbir3an_1 $f wff ps $.
	fmpbir3an_2 $f wff ch $.
	fmpbir3an_3 $f wff th $.
	empbir3an_0 $e |- ps $.
	empbir3an_1 $e |- ch $.
	empbir3an_2 $e |- th $.
	empbir3an_3 $e |- ( ph <-> ( ps /\ ch /\ th ) ) $.
	mpbir3an $p |- ph $= fmpbir3an_0 fmpbir3an_1 fmpbir3an_2 fmpbir3an_3 w3a fmpbir3an_1 fmpbir3an_2 fmpbir3an_3 empbir3an_0 empbir3an_1 empbir3an_2 3pm3.2i empbir3an_3 mpbir $.
$}
$( Detach a conjunction of truths in a biconditional.  (Contributed by
       Mario Carneiro, 11-May-2014.)  (Revised by Mario Carneiro,
       9-Jan-2015.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmpbir3and_0 $f wff ph $.
	fmpbir3and_1 $f wff ps $.
	fmpbir3and_2 $f wff ch $.
	fmpbir3and_3 $f wff th $.
	fmpbir3and_4 $f wff ta $.
	empbir3and_0 $e |- ( ph -> ch ) $.
	empbir3and_1 $e |- ( ph -> th ) $.
	empbir3and_2 $e |- ( ph -> ta ) $.
	empbir3and_3 $e |- ( ph -> ( ps <-> ( ch /\ th /\ ta ) ) ) $.
	mpbir3and $p |- ( ph -> ps ) $= fmpbir3and_0 fmpbir3and_1 fmpbir3and_2 fmpbir3and_3 fmpbir3and_4 w3a fmpbir3and_0 fmpbir3and_2 fmpbir3and_3 fmpbir3and_4 empbir3and_0 empbir3and_1 empbir3and_2 3jca empbir3and_3 mpbird $.
$}
$( Syllogism inference.  (Contributed by Mario Carneiro, 11-May-2014.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3anbrc_0 $f wff ph $.
	fsyl3anbrc_1 $f wff ps $.
	fsyl3anbrc_2 $f wff ch $.
	fsyl3anbrc_3 $f wff th $.
	fsyl3anbrc_4 $f wff ta $.
	esyl3anbrc_0 $e |- ( ph -> ps ) $.
	esyl3anbrc_1 $e |- ( ph -> ch ) $.
	esyl3anbrc_2 $e |- ( ph -> th ) $.
	esyl3anbrc_3 $e |- ( ta <-> ( ps /\ ch /\ th ) ) $.
	syl3anbrc $p |- ( ph -> ta ) $= fsyl3anbrc_0 fsyl3anbrc_1 fsyl3anbrc_2 fsyl3anbrc_3 w3a fsyl3anbrc_4 fsyl3anbrc_0 fsyl3anbrc_1 fsyl3anbrc_2 fsyl3anbrc_3 esyl3anbrc_0 esyl3anbrc_1 esyl3anbrc_2 3jca esyl3anbrc_3 sylibr $.
$}
$( Join antecedents and consequents with conjunction.  (Contributed by NM,
       8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3anim123i_0 $f wff ph $.
	f3anim123i_1 $f wff ps $.
	f3anim123i_2 $f wff ch $.
	f3anim123i_3 $f wff th $.
	f3anim123i_4 $f wff ta $.
	f3anim123i_5 $f wff et $.
	e3anim123i_0 $e |- ( ph -> ps ) $.
	e3anim123i_1 $e |- ( ch -> th ) $.
	e3anim123i_2 $e |- ( ta -> et ) $.
	3anim123i $p |- ( ( ph /\ ch /\ ta ) -> ( ps /\ th /\ et ) ) $= f3anim123i_0 f3anim123i_2 f3anim123i_4 w3a f3anim123i_1 f3anim123i_3 f3anim123i_5 f3anim123i_0 f3anim123i_2 f3anim123i_1 f3anim123i_4 e3anim123i_0 3ad2ant1 f3anim123i_2 f3anim123i_0 f3anim123i_3 f3anim123i_4 e3anim123i_1 3ad2ant2 f3anim123i_4 f3anim123i_0 f3anim123i_5 f3anim123i_2 e3anim123i_2 3ad2ant3 3jca $.
$}
$( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 16-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3anim1i_0 $f wff ph $.
	f3anim1i_1 $f wff ps $.
	f3anim1i_2 $f wff ch $.
	f3anim1i_3 $f wff th $.
	e3anim1i_0 $e |- ( ph -> ps ) $.
	3anim1i $p |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) ) $= f3anim1i_0 f3anim1i_1 f3anim1i_2 f3anim1i_2 f3anim1i_3 f3anim1i_3 e3anim1i_0 f3anim1i_2 id f3anim1i_3 id 3anim123i $.
$}
$( Add two conjuncts to antecedent and consequent.  (Contributed by Jeff
       Hankins, 19-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3anim3i_0 $f wff ph $.
	f3anim3i_1 $f wff ps $.
	f3anim3i_2 $f wff ch $.
	f3anim3i_3 $f wff th $.
	e3anim3i_0 $e |- ( ph -> ps ) $.
	3anim3i $p |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) ) $= f3anim3i_2 f3anim3i_2 f3anim3i_3 f3anim3i_3 f3anim3i_0 f3anim3i_1 f3anim3i_2 id f3anim3i_3 id e3anim3i_0 3anim123i $.
$}
$( Join 3 biconditionals with conjunction.  (Contributed by NM,
       21-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3anbi123i_0 $f wff ph $.
	f3anbi123i_1 $f wff ps $.
	f3anbi123i_2 $f wff ch $.
	f3anbi123i_3 $f wff th $.
	f3anbi123i_4 $f wff ta $.
	f3anbi123i_5 $f wff et $.
	e3anbi123i_0 $e |- ( ph <-> ps ) $.
	e3anbi123i_1 $e |- ( ch <-> th ) $.
	e3anbi123i_2 $e |- ( ta <-> et ) $.
	3anbi123i $p |- ( ( ph /\ ch /\ ta ) <-> ( ps /\ th /\ et ) ) $= f3anbi123i_0 f3anbi123i_2 wa f3anbi123i_4 wa f3anbi123i_1 f3anbi123i_3 wa f3anbi123i_5 wa f3anbi123i_0 f3anbi123i_2 f3anbi123i_4 w3a f3anbi123i_1 f3anbi123i_3 f3anbi123i_5 w3a f3anbi123i_0 f3anbi123i_2 wa f3anbi123i_1 f3anbi123i_3 wa f3anbi123i_4 f3anbi123i_5 f3anbi123i_0 f3anbi123i_1 f3anbi123i_2 f3anbi123i_3 e3anbi123i_0 e3anbi123i_1 anbi12i e3anbi123i_2 anbi12i f3anbi123i_0 f3anbi123i_2 f3anbi123i_4 df-3an f3anbi123i_1 f3anbi123i_3 f3anbi123i_5 df-3an 3bitr4i $.
$}
$( Join 3 biconditionals with disjunction.  (Contributed by NM,
       17-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3orbi123i_0 $f wff ph $.
	f3orbi123i_1 $f wff ps $.
	f3orbi123i_2 $f wff ch $.
	f3orbi123i_3 $f wff th $.
	f3orbi123i_4 $f wff ta $.
	f3orbi123i_5 $f wff et $.
	e3orbi123i_0 $e |- ( ph <-> ps ) $.
	e3orbi123i_1 $e |- ( ch <-> th ) $.
	e3orbi123i_2 $e |- ( ta <-> et ) $.
	3orbi123i $p |- ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) $= f3orbi123i_0 f3orbi123i_2 wo f3orbi123i_4 wo f3orbi123i_1 f3orbi123i_3 wo f3orbi123i_5 wo f3orbi123i_0 f3orbi123i_2 f3orbi123i_4 w3o f3orbi123i_1 f3orbi123i_3 f3orbi123i_5 w3o f3orbi123i_0 f3orbi123i_2 wo f3orbi123i_1 f3orbi123i_3 wo f3orbi123i_4 f3orbi123i_5 f3orbi123i_0 f3orbi123i_1 f3orbi123i_2 f3orbi123i_3 e3orbi123i_0 e3orbi123i_1 orbi12i e3orbi123i_2 orbi12i f3orbi123i_0 f3orbi123i_2 f3orbi123i_4 df-3or f3orbi123i_1 f3orbi123i_3 f3orbi123i_5 df-3or 3bitr4i $.
$}
$( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3anbi1i_0 $f wff ph $.
	f3anbi1i_1 $f wff ps $.
	f3anbi1i_2 $f wff ch $.
	f3anbi1i_3 $f wff th $.
	e3anbi1i_0 $e |- ( ph <-> ps ) $.
	3anbi1i $p |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) ) $= f3anbi1i_0 f3anbi1i_1 f3anbi1i_2 f3anbi1i_2 f3anbi1i_3 f3anbi1i_3 e3anbi1i_0 f3anbi1i_2 biid f3anbi1i_3 biid 3anbi123i $.
$}
$( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3anbi2i_0 $f wff ph $.
	f3anbi2i_1 $f wff ps $.
	f3anbi2i_2 $f wff ch $.
	f3anbi2i_3 $f wff th $.
	e3anbi2i_0 $e |- ( ph <-> ps ) $.
	3anbi2i $p |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) ) $= f3anbi2i_2 f3anbi2i_2 f3anbi2i_0 f3anbi2i_1 f3anbi2i_3 f3anbi2i_3 f3anbi2i_2 biid e3anbi2i_0 f3anbi2i_3 biid 3anbi123i $.
$}
$( Inference adding two conjuncts to each side of a biconditional.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3anbi3i_0 $f wff ph $.
	f3anbi3i_1 $f wff ps $.
	f3anbi3i_2 $f wff ch $.
	f3anbi3i_3 $f wff th $.
	e3anbi3i_0 $e |- ( ph <-> ps ) $.
	3anbi3i $p |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) ) $= f3anbi3i_2 f3anbi3i_2 f3anbi3i_3 f3anbi3i_3 f3anbi3i_0 f3anbi3i_1 f3anbi3i_2 biid f3anbi3i_3 biid e3anbi3i_0 3anbi123i $.
$}
$( Importation inference.  (Contributed by NM, 8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3imp_0 $f wff ph $.
	f3imp_1 $f wff ps $.
	f3imp_2 $f wff ch $.
	f3imp_3 $f wff th $.
	e3imp_0 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
	3imp $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3imp_0 f3imp_1 f3imp_2 w3a f3imp_0 f3imp_1 wa f3imp_2 wa f3imp_3 f3imp_0 f3imp_1 f3imp_2 df-3an f3imp_0 f3imp_1 f3imp_2 f3imp_3 e3imp_0 imp31 sylbi $.
$}
$( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impa_0 $f wff ph $.
	f3impa_1 $f wff ps $.
	f3impa_2 $f wff ch $.
	f3impa_3 $f wff th $.
	e3impa_0 $e |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $.
	3impa $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3impa_0 f3impa_1 f3impa_2 f3impa_3 f3impa_0 f3impa_1 f3impa_2 f3impa_3 e3impa_0 exp31 3imp $.
$}
$( Importation from double to triple conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impb_0 $f wff ph $.
	f3impb_1 $f wff ps $.
	f3impb_2 $f wff ch $.
	f3impb_3 $f wff th $.
	e3impb_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	3impb $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3impb_0 f3impb_1 f3impb_2 f3impb_3 f3impb_0 f3impb_1 f3impb_2 f3impb_3 e3impb_0 exp32 3imp $.
$}
$( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impia_0 $f wff ph $.
	f3impia_1 $f wff ps $.
	f3impia_2 $f wff ch $.
	f3impia_3 $f wff th $.
	e3impia_0 $e |- ( ( ph /\ ps ) -> ( ch -> th ) ) $.
	3impia $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3impia_0 f3impia_1 f3impia_2 f3impia_3 f3impia_0 f3impia_1 f3impia_2 f3impia_3 wi e3impia_0 ex 3imp $.
$}
$( Importation to triple conjunction.  (Contributed by NM, 13-Jun-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impib_0 $f wff ph $.
	f3impib_1 $f wff ps $.
	f3impib_2 $f wff ch $.
	f3impib_3 $f wff th $.
	e3impib_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	3impib $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3impib_0 f3impib_1 f3impib_2 f3impib_3 f3impib_0 f3impib_1 f3impib_2 f3impib_3 e3impib_0 exp3a 3imp $.
$}
$( Exportation inference.  (Contributed by NM, 30-May-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3exp_0 $f wff ph $.
	f3exp_1 $f wff ps $.
	f3exp_2 $f wff ch $.
	f3exp_3 $f wff th $.
	e3exp_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3exp $p |- ( ph -> ( ps -> ( ch -> th ) ) ) $= f3exp_0 f3exp_1 f3exp_2 f3exp_0 f3exp_1 f3exp_2 w3a f3exp_3 f3exp_0 f3exp_1 f3exp_2 pm3.2an3 e3exp_0 syl8 $.
$}
$( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3expa_0 $f wff ph $.
	f3expa_1 $f wff ps $.
	f3expa_2 $f wff ch $.
	f3expa_3 $f wff th $.
	e3expa_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3expa $p |- ( ( ( ph /\ ps ) /\ ch ) -> th ) $= f3expa_0 f3expa_1 f3expa_2 f3expa_3 f3expa_0 f3expa_1 f3expa_2 f3expa_3 e3expa_0 3exp imp31 $.
$}
$( Exportation from triple to double conjunction.  (Contributed by NM,
       20-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3expb_0 $f wff ph $.
	f3expb_1 $f wff ps $.
	f3expb_2 $f wff ch $.
	f3expb_3 $f wff th $.
	e3expb_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3expb $p |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $= f3expb_0 f3expb_1 f3expb_2 f3expb_3 f3expb_0 f3expb_1 f3expb_2 f3expb_3 e3expb_0 3exp imp32 $.
$}
$( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3expia_0 $f wff ph $.
	f3expia_1 $f wff ps $.
	f3expia_2 $f wff ch $.
	f3expia_3 $f wff th $.
	e3expia_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3expia $p |- ( ( ph /\ ps ) -> ( ch -> th ) ) $= f3expia_0 f3expia_1 f3expia_2 f3expia_3 wi f3expia_0 f3expia_1 f3expia_2 f3expia_3 e3expia_0 3exp imp $.
$}
$( Exportation from triple conjunction.  (Contributed by NM,
       19-May-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3expib_0 $f wff ph $.
	f3expib_1 $f wff ps $.
	f3expib_2 $f wff ch $.
	f3expib_3 $f wff th $.
	e3expib_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3expib $p |- ( ph -> ( ( ps /\ ch ) -> th ) ) $= f3expib_0 f3expib_1 f3expib_2 f3expib_3 f3expib_0 f3expib_1 f3expib_2 f3expib_3 e3expib_0 3exp imp3a $.
$}
$( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3com12_0 $f wff ph $.
	f3com12_1 $f wff ps $.
	f3com12_2 $f wff ch $.
	f3com12_3 $f wff th $.
	e3com12_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3com12 $p |- ( ( ps /\ ph /\ ch ) -> th ) $= f3com12_1 f3com12_0 f3com12_2 w3a f3com12_0 f3com12_1 f3com12_2 w3a f3com12_3 f3com12_1 f3com12_0 f3com12_2 3ancoma e3com12_0 sylbi $.
$}
$( Commutation in antecedent.  Swap 1st and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3com13_0 $f wff ph $.
	f3com13_1 $f wff ps $.
	f3com13_2 $f wff ch $.
	f3com13_3 $f wff th $.
	e3com13_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3com13 $p |- ( ( ch /\ ps /\ ph ) -> th ) $= f3com13_2 f3com13_1 f3com13_0 w3a f3com13_0 f3com13_1 f3com13_2 w3a f3com13_3 f3com13_2 f3com13_1 f3com13_0 3anrev e3com13_0 sylbi $.
$}
$( Commutation in antecedent.  Swap 2nd and 3rd.  (Contributed by NM,
       28-Jan-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3com23_0 $f wff ph $.
	f3com23_1 $f wff ps $.
	f3com23_2 $f wff ch $.
	f3com23_3 $f wff th $.
	e3com23_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3com23 $p |- ( ( ph /\ ch /\ ps ) -> th ) $= f3com23_0 f3com23_2 f3com23_1 f3com23_3 f3com23_0 f3com23_1 f3com23_2 f3com23_3 f3com23_0 f3com23_1 f3com23_2 f3com23_3 e3com23_0 3exp com23 3imp $.
$}
$( Commutation in antecedent.  Rotate left.  (Contributed by NM,
       28-Jan-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3coml_0 $f wff ph $.
	f3coml_1 $f wff ps $.
	f3coml_2 $f wff ch $.
	f3coml_3 $f wff th $.
	e3coml_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3coml $p |- ( ( ps /\ ch /\ ph ) -> th ) $= f3coml_0 f3coml_2 f3coml_1 f3coml_3 f3coml_0 f3coml_1 f3coml_2 f3coml_3 e3coml_0 3com23 3com13 $.
$}
$( Commutation in antecedent.  Rotate right.  (Contributed by NM,
       28-Jan-1996.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3comr_0 $f wff ph $.
	f3comr_1 $f wff ps $.
	f3comr_2 $f wff ch $.
	f3comr_3 $f wff th $.
	e3comr_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3comr $p |- ( ( ch /\ ph /\ ps ) -> th ) $= f3comr_1 f3comr_2 f3comr_0 f3comr_3 f3comr_0 f3comr_1 f3comr_2 f3comr_3 e3comr_0 3coml 3coml $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       16-Feb-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant3r1_0 $f wff ph $.
	f3adant3r1_1 $f wff ps $.
	f3adant3r1_2 $f wff ch $.
	f3adant3r1_3 $f wff th $.
	f3adant3r1_4 $f wff ta $.
	e3adant3r1_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant3r1 $p |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th ) $= f3adant3r1_0 f3adant3r1_1 f3adant3r1_2 f3adant3r1_3 f3adant3r1_4 f3adant3r1_0 f3adant3r1_1 f3adant3r1_2 f3adant3r1_3 e3adant3r1_0 3expb 3adantr1 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       17-Feb-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant3r2_0 $f wff ph $.
	f3adant3r2_1 $f wff ps $.
	f3adant3r2_2 $f wff ch $.
	f3adant3r2_3 $f wff th $.
	f3adant3r2_4 $f wff ta $.
	e3adant3r2_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant3r2 $p |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th ) $= f3adant3r2_0 f3adant3r2_1 f3adant3r2_2 f3adant3r2_3 f3adant3r2_4 f3adant3r2_0 f3adant3r2_1 f3adant3r2_2 f3adant3r2_3 e3adant3r2_0 3expb 3adantr2 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       18-Feb-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant3r3_0 $f wff ph $.
	f3adant3r3_1 $f wff ps $.
	f3adant3r3_2 $f wff ch $.
	f3adant3r3_3 $f wff th $.
	f3adant3r3_4 $f wff ta $.
	e3adant3r3_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant3r3 $p |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th ) $= f3adant3r3_0 f3adant3r3_1 f3adant3r3_2 f3adant3r3_3 f3adant3r3_4 f3adant3r3_0 f3adant3r3_1 f3adant3r3_2 f3adant3r3_3 e3adant3r3_0 3expb 3adantr3 $.
$}
$( Swap conjuncts.  (Contributed by NM, 16-Dec-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3an1rs_0 $f wff ph $.
	f3an1rs_1 $f wff ps $.
	f3an1rs_2 $f wff ch $.
	f3an1rs_3 $f wff th $.
	f3an1rs_4 $f wff ta $.
	e3an1rs_0 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	3an1rs $p |- ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ) $= f3an1rs_0 f3an1rs_1 f3an1rs_3 w3a f3an1rs_2 f3an1rs_4 f3an1rs_0 f3an1rs_1 f3an1rs_3 f3an1rs_2 f3an1rs_4 wi f3an1rs_0 f3an1rs_1 f3an1rs_2 f3an1rs_3 f3an1rs_4 f3an1rs_0 f3an1rs_1 f3an1rs_2 f3an1rs_3 f3an1rs_4 wi f3an1rs_0 f3an1rs_1 f3an1rs_2 w3a f3an1rs_3 f3an1rs_4 e3an1rs_0 ex 3exp com34 3imp imp $.
$}
$( Importation to left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3imp1_0 $f wff ph $.
	f3imp1_1 $f wff ps $.
	f3imp1_2 $f wff ch $.
	f3imp1_3 $f wff th $.
	f3imp1_4 $f wff ta $.
	e3imp1_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	3imp1 $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $= f3imp1_0 f3imp1_1 f3imp1_2 w3a f3imp1_3 f3imp1_4 f3imp1_0 f3imp1_1 f3imp1_2 f3imp1_3 f3imp1_4 wi e3imp1_0 3imp imp $.
$}
$( Importation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3impd_0 $f wff ph $.
	f3impd_1 $f wff ps $.
	f3impd_2 $f wff ch $.
	f3impd_3 $f wff th $.
	f3impd_4 $f wff ta $.
	e3impd_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	3impd $p |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $= f3impd_1 f3impd_2 f3impd_3 w3a f3impd_0 f3impd_4 f3impd_1 f3impd_2 f3impd_3 f3impd_0 f3impd_4 wi f3impd_0 f3impd_1 f3impd_2 f3impd_3 f3impd_4 e3impd_0 com4l 3imp com12 $.
$}
$( Importation to right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3imp2_0 $f wff ph $.
	f3imp2_1 $f wff ps $.
	f3imp2_2 $f wff ch $.
	f3imp2_3 $f wff th $.
	f3imp2_4 $f wff ta $.
	e3imp2_0 $e |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $.
	3imp2 $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $= f3imp2_0 f3imp2_1 f3imp2_2 f3imp2_3 w3a f3imp2_4 f3imp2_0 f3imp2_1 f3imp2_2 f3imp2_3 f3imp2_4 e3imp2_0 3impd imp $.
$}
$( Exportation from left triple conjunction.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3exp1_0 $f wff ph $.
	f3exp1_1 $f wff ps $.
	f3exp1_2 $f wff ch $.
	f3exp1_3 $f wff th $.
	f3exp1_4 $f wff ta $.
	e3exp1_0 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	3exp1 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= f3exp1_0 f3exp1_1 f3exp1_2 f3exp1_3 f3exp1_4 wi f3exp1_0 f3exp1_1 f3exp1_2 w3a f3exp1_3 f3exp1_4 e3exp1_0 ex 3exp $.
$}
$( Exportation deduction for triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3expd_0 $f wff ph $.
	f3expd_1 $f wff ps $.
	f3expd_2 $f wff ch $.
	f3expd_3 $f wff th $.
	f3expd_4 $f wff ta $.
	e3expd_0 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	3expd $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= f3expd_1 f3expd_2 f3expd_3 f3expd_0 f3expd_4 f3expd_1 f3expd_2 f3expd_3 f3expd_0 f3expd_4 wi f3expd_0 f3expd_1 f3expd_2 f3expd_3 w3a f3expd_4 e3expd_0 com12 3exp com4r $.
$}
$( Exportation from right triple conjunction.  (Contributed by NM,
       26-Oct-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3exp2_0 $f wff ph $.
	f3exp2_1 $f wff ps $.
	f3exp2_2 $f wff ch $.
	f3exp2_3 $f wff th $.
	f3exp2_4 $f wff ta $.
	e3exp2_0 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	3exp2 $p |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) $= f3exp2_0 f3exp2_1 f3exp2_2 f3exp2_3 f3exp2_4 f3exp2_0 f3exp2_1 f3exp2_2 f3exp2_3 w3a f3exp2_4 e3exp2_0 ex 3expd $.
$}
$( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fexp5o_0 $f wff ph $.
	fexp5o_1 $f wff ps $.
	fexp5o_2 $f wff ch $.
	fexp5o_3 $f wff th $.
	fexp5o_4 $f wff ta $.
	fexp5o_5 $f wff et $.
	eexp5o_0 $e |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) $.
	exp5o $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= fexp5o_0 fexp5o_1 fexp5o_2 fexp5o_3 fexp5o_4 fexp5o_5 wi wi fexp5o_0 fexp5o_1 fexp5o_2 w3a fexp5o_3 fexp5o_4 fexp5o_5 eexp5o_0 exp3a 3exp $.
$}
$( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fexp516_0 $f wff ph $.
	fexp516_1 $f wff ps $.
	fexp516_2 $f wff ch $.
	fexp516_3 $f wff th $.
	fexp516_4 $f wff ta $.
	fexp516_5 $f wff et $.
	eexp516_0 $e |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ) $.
	exp516 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= fexp516_0 fexp516_1 fexp516_2 fexp516_3 fexp516_4 fexp516_5 wi fexp516_0 fexp516_1 fexp516_2 fexp516_3 w3a fexp516_4 fexp516_5 eexp516_0 exp31 3expd $.
$}
$( A triple exportation inference.  (Contributed by Jeff Hankins,
       8-Jul-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fexp520_0 $f wff ph $.
	fexp520_1 $f wff ps $.
	fexp520_2 $f wff ch $.
	fexp520_3 $f wff th $.
	fexp520_4 $f wff ta $.
	fexp520_5 $f wff et $.
	eexp520_0 $e |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
	exp520 $p |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) $= fexp520_0 fexp520_1 fexp520_2 fexp520_3 fexp520_4 fexp520_5 fexp520_0 fexp520_1 fexp520_2 w3a fexp520_3 fexp520_4 wa fexp520_5 eexp520_0 ex exp5o $.
$}
$( Associative law for conjunction applied to antecedent (eliminates
       syllogism).  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anassrs_0 $f wff ph $.
	f3anassrs_1 $f wff ps $.
	f3anassrs_2 $f wff ch $.
	f3anassrs_3 $f wff th $.
	f3anassrs_4 $f wff ta $.
	e3anassrs_0 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	3anassrs $p |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ) $= f3anassrs_0 f3anassrs_1 f3anassrs_2 f3anassrs_3 f3anassrs_4 f3anassrs_0 f3anassrs_1 f3anassrs_2 f3anassrs_3 f3anassrs_4 e3anassrs_0 3exp2 imp41 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant1l_0 $f wff ph $.
	f3adant1l_1 $f wff ps $.
	f3adant1l_2 $f wff ch $.
	f3adant1l_3 $f wff th $.
	f3adant1l_4 $f wff ta $.
	e3adant1l_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant1l $p |- ( ( ( ta /\ ph ) /\ ps /\ ch ) -> th ) $= f3adant1l_4 f3adant1l_0 wa f3adant1l_1 f3adant1l_2 f3adant1l_3 f3adant1l_0 f3adant1l_1 f3adant1l_2 wa f3adant1l_3 f3adant1l_4 f3adant1l_0 f3adant1l_1 f3adant1l_2 f3adant1l_3 e3adant1l_0 3expb adantll 3impb $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant1r_0 $f wff ph $.
	f3adant1r_1 $f wff ps $.
	f3adant1r_2 $f wff ch $.
	f3adant1r_3 $f wff th $.
	f3adant1r_4 $f wff ta $.
	e3adant1r_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant1r $p |- ( ( ( ph /\ ta ) /\ ps /\ ch ) -> th ) $= f3adant1r_0 f3adant1r_4 wa f3adant1r_1 f3adant1r_2 f3adant1r_3 f3adant1r_0 f3adant1r_1 f3adant1r_2 wa f3adant1r_3 f3adant1r_4 f3adant1r_0 f3adant1r_1 f3adant1r_2 f3adant1r_3 e3adant1r_0 3expb adantlr 3impb $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant2l_0 $f wff ph $.
	f3adant2l_1 $f wff ps $.
	f3adant2l_2 $f wff ch $.
	f3adant2l_3 $f wff th $.
	f3adant2l_4 $f wff ta $.
	e3adant2l_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant2l $p |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th ) $= f3adant2l_4 f3adant2l_1 wa f3adant2l_0 f3adant2l_2 f3adant2l_3 f3adant2l_1 f3adant2l_0 f3adant2l_2 f3adant2l_3 f3adant2l_4 f3adant2l_0 f3adant2l_1 f3adant2l_2 f3adant2l_3 e3adant2l_0 3com12 3adant1l 3com12 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant2r_0 $f wff ph $.
	f3adant2r_1 $f wff ps $.
	f3adant2r_2 $f wff ch $.
	f3adant2r_3 $f wff th $.
	f3adant2r_4 $f wff ta $.
	e3adant2r_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant2r $p |- ( ( ph /\ ( ps /\ ta ) /\ ch ) -> th ) $= f3adant2r_1 f3adant2r_4 wa f3adant2r_0 f3adant2r_2 f3adant2r_3 f3adant2r_1 f3adant2r_0 f3adant2r_2 f3adant2r_3 f3adant2r_4 f3adant2r_0 f3adant2r_1 f3adant2r_2 f3adant2r_3 e3adant2r_0 3com12 3adant1r 3com12 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant3l_0 $f wff ph $.
	f3adant3l_1 $f wff ps $.
	f3adant3l_2 $f wff ch $.
	f3adant3l_3 $f wff th $.
	f3adant3l_4 $f wff ta $.
	e3adant3l_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant3l $p |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th ) $= f3adant3l_4 f3adant3l_2 wa f3adant3l_1 f3adant3l_0 f3adant3l_3 f3adant3l_2 f3adant3l_1 f3adant3l_0 f3adant3l_3 f3adant3l_4 f3adant3l_0 f3adant3l_1 f3adant3l_2 f3adant3l_3 e3adant3l_0 3com13 3adant1l 3com13 $.
$}
$( Deduction adding a conjunct to antecedent.  (Contributed by NM,
       8-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3adant3r_0 $f wff ph $.
	f3adant3r_1 $f wff ps $.
	f3adant3r_2 $f wff ch $.
	f3adant3r_3 $f wff th $.
	f3adant3r_4 $f wff ta $.
	e3adant3r_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3adant3r $p |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th ) $= f3adant3r_2 f3adant3r_4 wa f3adant3r_1 f3adant3r_0 f3adant3r_3 f3adant3r_2 f3adant3r_1 f3adant3r_0 f3adant3r_3 f3adant3r_4 f3adant3r_0 f3adant3r_1 f3adant3r_2 f3adant3r_3 e3adant3r_0 3com13 3adant1r 3com13 $.
$}
$( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl12anc_0 $f wff ph $.
	fsyl12anc_1 $f wff ps $.
	fsyl12anc_2 $f wff ch $.
	fsyl12anc_3 $f wff th $.
	fsyl12anc_4 $f wff ta $.
	esyl12anc_0 $e |- ( ph -> ps ) $.
	esyl12anc_1 $e |- ( ph -> ch ) $.
	esyl12anc_2 $e |- ( ph -> th ) $.
	esyl12anc_3 $e |- ( ( ps /\ ( ch /\ th ) ) -> ta ) $.
	syl12anc $p |- ( ph -> ta ) $= fsyl12anc_0 fsyl12anc_1 fsyl12anc_2 fsyl12anc_3 wa wa fsyl12anc_4 fsyl12anc_0 fsyl12anc_1 fsyl12anc_2 fsyl12anc_3 esyl12anc_0 esyl12anc_1 esyl12anc_2 jca32 esyl12anc_3 syl $.
$}
$( Syllogism combined with contraction.  (Contributed by Jeff Hankins,
         1-Aug-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl21anc_0 $f wff ph $.
	fsyl21anc_1 $f wff ps $.
	fsyl21anc_2 $f wff ch $.
	fsyl21anc_3 $f wff th $.
	fsyl21anc_4 $f wff ta $.
	esyl21anc_0 $e |- ( ph -> ps ) $.
	esyl21anc_1 $e |- ( ph -> ch ) $.
	esyl21anc_2 $e |- ( ph -> th ) $.
	esyl21anc_3 $e |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $.
	syl21anc $p |- ( ph -> ta ) $= fsyl21anc_0 fsyl21anc_1 fsyl21anc_2 wa fsyl21anc_3 wa fsyl21anc_4 fsyl21anc_0 fsyl21anc_1 fsyl21anc_2 fsyl21anc_3 esyl21anc_0 esyl21anc_1 esyl21anc_2 jca31 esyl21anc_3 syl $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3anc_0 $f wff ph $.
	fsyl3anc_1 $f wff ps $.
	fsyl3anc_2 $f wff ch $.
	fsyl3anc_3 $f wff th $.
	fsyl3anc_4 $f wff ta $.
	esyl3anc_0 $e |- ( ph -> ps ) $.
	esyl3anc_1 $e |- ( ph -> ch ) $.
	esyl3anc_2 $e |- ( ph -> th ) $.
	esyl3anc_3 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3anc $p |- ( ph -> ta ) $= fsyl3anc_0 fsyl3anc_1 fsyl3anc_2 fsyl3anc_3 w3a fsyl3anc_4 fsyl3anc_0 fsyl3anc_1 fsyl3anc_2 fsyl3anc_3 esyl3anc_0 esyl3anc_1 esyl3anc_2 3jca esyl3anc_3 syl $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl22anc_0 $f wff ph $.
	fsyl22anc_1 $f wff ps $.
	fsyl22anc_2 $f wff ch $.
	fsyl22anc_3 $f wff th $.
	fsyl22anc_4 $f wff ta $.
	fsyl22anc_5 $f wff et $.
	esyl22anc_0 $e |- ( ph -> ps ) $.
	esyl22anc_1 $e |- ( ph -> ch ) $.
	esyl22anc_2 $e |- ( ph -> th ) $.
	esyl22anc_3 $e |- ( ph -> ta ) $.
	esyl22anc_4 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) $.
	syl22anc $p |- ( ph -> et ) $= fsyl22anc_0 fsyl22anc_1 fsyl22anc_2 wa fsyl22anc_3 fsyl22anc_4 fsyl22anc_5 fsyl22anc_0 fsyl22anc_1 fsyl22anc_2 esyl22anc_0 esyl22anc_1 jca esyl22anc_2 esyl22anc_3 esyl22anc_4 syl12anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl13anc_0 $f wff ph $.
	fsyl13anc_1 $f wff ps $.
	fsyl13anc_2 $f wff ch $.
	fsyl13anc_3 $f wff th $.
	fsyl13anc_4 $f wff ta $.
	fsyl13anc_5 $f wff et $.
	esyl13anc_0 $e |- ( ph -> ps ) $.
	esyl13anc_1 $e |- ( ph -> ch ) $.
	esyl13anc_2 $e |- ( ph -> th ) $.
	esyl13anc_3 $e |- ( ph -> ta ) $.
	esyl13anc_4 $e |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et ) $.
	syl13anc $p |- ( ph -> et ) $= fsyl13anc_0 fsyl13anc_1 fsyl13anc_2 fsyl13anc_3 fsyl13anc_4 w3a fsyl13anc_5 esyl13anc_0 fsyl13anc_0 fsyl13anc_2 fsyl13anc_3 fsyl13anc_4 esyl13anc_1 esyl13anc_2 esyl13anc_3 3jca esyl13anc_4 syl2anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl31anc_0 $f wff ph $.
	fsyl31anc_1 $f wff ps $.
	fsyl31anc_2 $f wff ch $.
	fsyl31anc_3 $f wff th $.
	fsyl31anc_4 $f wff ta $.
	fsyl31anc_5 $f wff et $.
	esyl31anc_0 $e |- ( ph -> ps ) $.
	esyl31anc_1 $e |- ( ph -> ch ) $.
	esyl31anc_2 $e |- ( ph -> th ) $.
	esyl31anc_3 $e |- ( ph -> ta ) $.
	esyl31anc_4 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	syl31anc $p |- ( ph -> et ) $= fsyl31anc_0 fsyl31anc_1 fsyl31anc_2 fsyl31anc_3 w3a fsyl31anc_4 fsyl31anc_5 fsyl31anc_0 fsyl31anc_1 fsyl31anc_2 fsyl31anc_3 esyl31anc_0 esyl31anc_1 esyl31anc_2 3jca esyl31anc_3 esyl31anc_4 syl2anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl112anc_0 $f wff ph $.
	fsyl112anc_1 $f wff ps $.
	fsyl112anc_2 $f wff ch $.
	fsyl112anc_3 $f wff th $.
	fsyl112anc_4 $f wff ta $.
	fsyl112anc_5 $f wff et $.
	esyl112anc_0 $e |- ( ph -> ps ) $.
	esyl112anc_1 $e |- ( ph -> ch ) $.
	esyl112anc_2 $e |- ( ph -> th ) $.
	esyl112anc_3 $e |- ( ph -> ta ) $.
	esyl112anc_4 $e |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et ) $.
	syl112anc $p |- ( ph -> et ) $= fsyl112anc_0 fsyl112anc_1 fsyl112anc_2 fsyl112anc_3 fsyl112anc_4 wa fsyl112anc_5 esyl112anc_0 esyl112anc_1 fsyl112anc_0 fsyl112anc_3 fsyl112anc_4 esyl112anc_2 esyl112anc_3 jca esyl112anc_4 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl121anc_0 $f wff ph $.
	fsyl121anc_1 $f wff ps $.
	fsyl121anc_2 $f wff ch $.
	fsyl121anc_3 $f wff th $.
	fsyl121anc_4 $f wff ta $.
	fsyl121anc_5 $f wff et $.
	esyl121anc_0 $e |- ( ph -> ps ) $.
	esyl121anc_1 $e |- ( ph -> ch ) $.
	esyl121anc_2 $e |- ( ph -> th ) $.
	esyl121anc_3 $e |- ( ph -> ta ) $.
	esyl121anc_4 $e |- ( ( ps /\ ( ch /\ th ) /\ ta ) -> et ) $.
	syl121anc $p |- ( ph -> et ) $= fsyl121anc_0 fsyl121anc_1 fsyl121anc_2 fsyl121anc_3 wa fsyl121anc_4 fsyl121anc_5 esyl121anc_0 fsyl121anc_0 fsyl121anc_2 fsyl121anc_3 esyl121anc_1 esyl121anc_2 jca esyl121anc_3 esyl121anc_4 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl211anc_0 $f wff ph $.
	fsyl211anc_1 $f wff ps $.
	fsyl211anc_2 $f wff ch $.
	fsyl211anc_3 $f wff th $.
	fsyl211anc_4 $f wff ta $.
	fsyl211anc_5 $f wff et $.
	esyl211anc_0 $e |- ( ph -> ps ) $.
	esyl211anc_1 $e |- ( ph -> ch ) $.
	esyl211anc_2 $e |- ( ph -> th ) $.
	esyl211anc_3 $e |- ( ph -> ta ) $.
	esyl211anc_4 $e |- ( ( ( ps /\ ch ) /\ th /\ ta ) -> et ) $.
	syl211anc $p |- ( ph -> et ) $= fsyl211anc_0 fsyl211anc_1 fsyl211anc_2 wa fsyl211anc_3 fsyl211anc_4 fsyl211anc_5 fsyl211anc_0 fsyl211anc_1 fsyl211anc_2 esyl211anc_0 esyl211anc_1 jca esyl211anc_2 esyl211anc_3 esyl211anc_4 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl23anc_0 $f wff ph $.
	fsyl23anc_1 $f wff ps $.
	fsyl23anc_2 $f wff ch $.
	fsyl23anc_3 $f wff th $.
	fsyl23anc_4 $f wff ta $.
	fsyl23anc_5 $f wff et $.
	fsyl23anc_6 $f wff ze $.
	esyl23anc_0 $e |- ( ph -> ps ) $.
	esyl23anc_1 $e |- ( ph -> ch ) $.
	esyl23anc_2 $e |- ( ph -> th ) $.
	esyl23anc_3 $e |- ( ph -> ta ) $.
	esyl23anc_4 $e |- ( ph -> et ) $.
	esyl23anc_5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze ) $.
	syl23anc $p |- ( ph -> ze ) $= fsyl23anc_0 fsyl23anc_1 fsyl23anc_2 wa fsyl23anc_3 fsyl23anc_4 fsyl23anc_5 fsyl23anc_6 fsyl23anc_0 fsyl23anc_1 fsyl23anc_2 esyl23anc_0 esyl23anc_1 jca esyl23anc_2 esyl23anc_3 esyl23anc_4 esyl23anc_5 syl13anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl32anc_0 $f wff ph $.
	fsyl32anc_1 $f wff ps $.
	fsyl32anc_2 $f wff ch $.
	fsyl32anc_3 $f wff th $.
	fsyl32anc_4 $f wff ta $.
	fsyl32anc_5 $f wff et $.
	fsyl32anc_6 $f wff ze $.
	esyl32anc_0 $e |- ( ph -> ps ) $.
	esyl32anc_1 $e |- ( ph -> ch ) $.
	esyl32anc_2 $e |- ( ph -> th ) $.
	esyl32anc_3 $e |- ( ph -> ta ) $.
	esyl32anc_4 $e |- ( ph -> et ) $.
	esyl32anc_5 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
	syl32anc $p |- ( ph -> ze ) $= fsyl32anc_0 fsyl32anc_1 fsyl32anc_2 fsyl32anc_3 fsyl32anc_4 fsyl32anc_5 wa fsyl32anc_6 esyl32anc_0 esyl32anc_1 esyl32anc_2 fsyl32anc_0 fsyl32anc_4 fsyl32anc_5 esyl32anc_3 esyl32anc_4 jca esyl32anc_5 syl31anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl122anc_0 $f wff ph $.
	fsyl122anc_1 $f wff ps $.
	fsyl122anc_2 $f wff ch $.
	fsyl122anc_3 $f wff th $.
	fsyl122anc_4 $f wff ta $.
	fsyl122anc_5 $f wff et $.
	fsyl122anc_6 $f wff ze $.
	esyl122anc_0 $e |- ( ph -> ps ) $.
	esyl122anc_1 $e |- ( ph -> ch ) $.
	esyl122anc_2 $e |- ( ph -> th ) $.
	esyl122anc_3 $e |- ( ph -> ta ) $.
	esyl122anc_4 $e |- ( ph -> et ) $.
	esyl122anc_5 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze ) $.
	syl122anc $p |- ( ph -> ze ) $= fsyl122anc_0 fsyl122anc_1 fsyl122anc_2 fsyl122anc_3 fsyl122anc_4 fsyl122anc_5 wa fsyl122anc_6 esyl122anc_0 esyl122anc_1 esyl122anc_2 fsyl122anc_0 fsyl122anc_4 fsyl122anc_5 esyl122anc_3 esyl122anc_4 jca esyl122anc_5 syl121anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl212anc_0 $f wff ph $.
	fsyl212anc_1 $f wff ps $.
	fsyl212anc_2 $f wff ch $.
	fsyl212anc_3 $f wff th $.
	fsyl212anc_4 $f wff ta $.
	fsyl212anc_5 $f wff et $.
	fsyl212anc_6 $f wff ze $.
	esyl212anc_0 $e |- ( ph -> ps ) $.
	esyl212anc_1 $e |- ( ph -> ch ) $.
	esyl212anc_2 $e |- ( ph -> th ) $.
	esyl212anc_3 $e |- ( ph -> ta ) $.
	esyl212anc_4 $e |- ( ph -> et ) $.
	esyl212anc_5 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze ) $.
	syl212anc $p |- ( ph -> ze ) $= fsyl212anc_0 fsyl212anc_1 fsyl212anc_2 fsyl212anc_3 fsyl212anc_4 fsyl212anc_5 wa fsyl212anc_6 esyl212anc_0 esyl212anc_1 esyl212anc_2 fsyl212anc_0 fsyl212anc_4 fsyl212anc_5 esyl212anc_3 esyl212anc_4 jca esyl212anc_5 syl211anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl221anc_0 $f wff ph $.
	fsyl221anc_1 $f wff ps $.
	fsyl221anc_2 $f wff ch $.
	fsyl221anc_3 $f wff th $.
	fsyl221anc_4 $f wff ta $.
	fsyl221anc_5 $f wff et $.
	fsyl221anc_6 $f wff ze $.
	esyl221anc_0 $e |- ( ph -> ps ) $.
	esyl221anc_1 $e |- ( ph -> ch ) $.
	esyl221anc_2 $e |- ( ph -> th ) $.
	esyl221anc_3 $e |- ( ph -> ta ) $.
	esyl221anc_4 $e |- ( ph -> et ) $.
	esyl221anc_5 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze ) $.
	syl221anc $p |- ( ph -> ze ) $= fsyl221anc_0 fsyl221anc_1 fsyl221anc_2 fsyl221anc_3 fsyl221anc_4 wa fsyl221anc_5 fsyl221anc_6 esyl221anc_0 esyl221anc_1 fsyl221anc_0 fsyl221anc_3 fsyl221anc_4 esyl221anc_2 esyl221anc_3 jca esyl221anc_4 esyl221anc_5 syl211anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl113anc_0 $f wff ph $.
	fsyl113anc_1 $f wff ps $.
	fsyl113anc_2 $f wff ch $.
	fsyl113anc_3 $f wff th $.
	fsyl113anc_4 $f wff ta $.
	fsyl113anc_5 $f wff et $.
	fsyl113anc_6 $f wff ze $.
	esyl113anc_0 $e |- ( ph -> ps ) $.
	esyl113anc_1 $e |- ( ph -> ch ) $.
	esyl113anc_2 $e |- ( ph -> th ) $.
	esyl113anc_3 $e |- ( ph -> ta ) $.
	esyl113anc_4 $e |- ( ph -> et ) $.
	esyl113anc_5 $e |- ( ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze ) $.
	syl113anc $p |- ( ph -> ze ) $= fsyl113anc_0 fsyl113anc_1 fsyl113anc_2 fsyl113anc_3 fsyl113anc_4 fsyl113anc_5 w3a fsyl113anc_6 esyl113anc_0 esyl113anc_1 fsyl113anc_0 fsyl113anc_3 fsyl113anc_4 fsyl113anc_5 esyl113anc_2 esyl113anc_3 esyl113anc_4 3jca esyl113anc_5 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl131anc_0 $f wff ph $.
	fsyl131anc_1 $f wff ps $.
	fsyl131anc_2 $f wff ch $.
	fsyl131anc_3 $f wff th $.
	fsyl131anc_4 $f wff ta $.
	fsyl131anc_5 $f wff et $.
	fsyl131anc_6 $f wff ze $.
	esyl131anc_0 $e |- ( ph -> ps ) $.
	esyl131anc_1 $e |- ( ph -> ch ) $.
	esyl131anc_2 $e |- ( ph -> th ) $.
	esyl131anc_3 $e |- ( ph -> ta ) $.
	esyl131anc_4 $e |- ( ph -> et ) $.
	esyl131anc_5 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze ) $.
	syl131anc $p |- ( ph -> ze ) $= fsyl131anc_0 fsyl131anc_1 fsyl131anc_2 fsyl131anc_3 fsyl131anc_4 w3a fsyl131anc_5 fsyl131anc_6 esyl131anc_0 fsyl131anc_0 fsyl131anc_2 fsyl131anc_3 fsyl131anc_4 esyl131anc_1 esyl131anc_2 esyl131anc_3 3jca esyl131anc_4 esyl131anc_5 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl311anc_0 $f wff ph $.
	fsyl311anc_1 $f wff ps $.
	fsyl311anc_2 $f wff ch $.
	fsyl311anc_3 $f wff th $.
	fsyl311anc_4 $f wff ta $.
	fsyl311anc_5 $f wff et $.
	fsyl311anc_6 $f wff ze $.
	esyl311anc_0 $e |- ( ph -> ps ) $.
	esyl311anc_1 $e |- ( ph -> ch ) $.
	esyl311anc_2 $e |- ( ph -> th ) $.
	esyl311anc_3 $e |- ( ph -> ta ) $.
	esyl311anc_4 $e |- ( ph -> et ) $.
	esyl311anc_5 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze ) $.
	syl311anc $p |- ( ph -> ze ) $= fsyl311anc_0 fsyl311anc_1 fsyl311anc_2 fsyl311anc_3 w3a fsyl311anc_4 fsyl311anc_5 fsyl311anc_6 fsyl311anc_0 fsyl311anc_1 fsyl311anc_2 fsyl311anc_3 esyl311anc_0 esyl311anc_1 esyl311anc_2 3jca esyl311anc_3 esyl311anc_4 esyl311anc_5 syl3anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl33anc_0 $f wff ph $.
	fsyl33anc_1 $f wff ps $.
	fsyl33anc_2 $f wff ch $.
	fsyl33anc_3 $f wff th $.
	fsyl33anc_4 $f wff ta $.
	fsyl33anc_5 $f wff et $.
	fsyl33anc_6 $f wff ze $.
	fsyl33anc_7 $f wff si $.
	esyl33anc_0 $e |- ( ph -> ps ) $.
	esyl33anc_1 $e |- ( ph -> ch ) $.
	esyl33anc_2 $e |- ( ph -> th ) $.
	esyl33anc_3 $e |- ( ph -> ta ) $.
	esyl33anc_4 $e |- ( ph -> et ) $.
	esyl33anc_5 $e |- ( ph -> ze ) $.
	esyl33anc_6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si ) $.
	syl33anc $p |- ( ph -> si ) $= fsyl33anc_0 fsyl33anc_1 fsyl33anc_2 fsyl33anc_3 w3a fsyl33anc_4 fsyl33anc_5 fsyl33anc_6 fsyl33anc_7 fsyl33anc_0 fsyl33anc_1 fsyl33anc_2 fsyl33anc_3 esyl33anc_0 esyl33anc_1 esyl33anc_2 3jca esyl33anc_3 esyl33anc_4 esyl33anc_5 esyl33anc_6 syl13anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl222anc_0 $f wff ph $.
	fsyl222anc_1 $f wff ps $.
	fsyl222anc_2 $f wff ch $.
	fsyl222anc_3 $f wff th $.
	fsyl222anc_4 $f wff ta $.
	fsyl222anc_5 $f wff et $.
	fsyl222anc_6 $f wff ze $.
	fsyl222anc_7 $f wff si $.
	esyl222anc_0 $e |- ( ph -> ps ) $.
	esyl222anc_1 $e |- ( ph -> ch ) $.
	esyl222anc_2 $e |- ( ph -> th ) $.
	esyl222anc_3 $e |- ( ph -> ta ) $.
	esyl222anc_4 $e |- ( ph -> et ) $.
	esyl222anc_5 $e |- ( ph -> ze ) $.
	esyl222anc_6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) ) -> si ) $.
	syl222anc $p |- ( ph -> si ) $= fsyl222anc_0 fsyl222anc_1 fsyl222anc_2 fsyl222anc_3 fsyl222anc_4 fsyl222anc_5 fsyl222anc_6 wa fsyl222anc_7 esyl222anc_0 esyl222anc_1 esyl222anc_2 esyl222anc_3 fsyl222anc_0 fsyl222anc_5 fsyl222anc_6 esyl222anc_4 esyl222anc_5 jca esyl222anc_6 syl221anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl123anc_0 $f wff ph $.
	fsyl123anc_1 $f wff ps $.
	fsyl123anc_2 $f wff ch $.
	fsyl123anc_3 $f wff th $.
	fsyl123anc_4 $f wff ta $.
	fsyl123anc_5 $f wff et $.
	fsyl123anc_6 $f wff ze $.
	fsyl123anc_7 $f wff si $.
	esyl123anc_0 $e |- ( ph -> ps ) $.
	esyl123anc_1 $e |- ( ph -> ch ) $.
	esyl123anc_2 $e |- ( ph -> th ) $.
	esyl123anc_3 $e |- ( ph -> ta ) $.
	esyl123anc_4 $e |- ( ph -> et ) $.
	esyl123anc_5 $e |- ( ph -> ze ) $.
	esyl123anc_6 $e |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si ) $.
	syl123anc $p |- ( ph -> si ) $= fsyl123anc_0 fsyl123anc_1 fsyl123anc_2 fsyl123anc_3 wa fsyl123anc_4 fsyl123anc_5 fsyl123anc_6 fsyl123anc_7 esyl123anc_0 fsyl123anc_0 fsyl123anc_2 fsyl123anc_3 esyl123anc_1 esyl123anc_2 jca esyl123anc_3 esyl123anc_4 esyl123anc_5 esyl123anc_6 syl113anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl132anc_0 $f wff ph $.
	fsyl132anc_1 $f wff ps $.
	fsyl132anc_2 $f wff ch $.
	fsyl132anc_3 $f wff th $.
	fsyl132anc_4 $f wff ta $.
	fsyl132anc_5 $f wff et $.
	fsyl132anc_6 $f wff ze $.
	fsyl132anc_7 $f wff si $.
	esyl132anc_0 $e |- ( ph -> ps ) $.
	esyl132anc_1 $e |- ( ph -> ch ) $.
	esyl132anc_2 $e |- ( ph -> th ) $.
	esyl132anc_3 $e |- ( ph -> ta ) $.
	esyl132anc_4 $e |- ( ph -> et ) $.
	esyl132anc_5 $e |- ( ph -> ze ) $.
	esyl132anc_6 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) ) -> si ) $.
	syl132anc $p |- ( ph -> si ) $= fsyl132anc_0 fsyl132anc_1 fsyl132anc_2 fsyl132anc_3 fsyl132anc_4 fsyl132anc_5 fsyl132anc_6 wa fsyl132anc_7 esyl132anc_0 esyl132anc_1 esyl132anc_2 esyl132anc_3 fsyl132anc_0 fsyl132anc_5 fsyl132anc_6 esyl132anc_4 esyl132anc_5 jca esyl132anc_6 syl131anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl213anc_0 $f wff ph $.
	fsyl213anc_1 $f wff ps $.
	fsyl213anc_2 $f wff ch $.
	fsyl213anc_3 $f wff th $.
	fsyl213anc_4 $f wff ta $.
	fsyl213anc_5 $f wff et $.
	fsyl213anc_6 $f wff ze $.
	fsyl213anc_7 $f wff si $.
	esyl213anc_0 $e |- ( ph -> ps ) $.
	esyl213anc_1 $e |- ( ph -> ch ) $.
	esyl213anc_2 $e |- ( ph -> th ) $.
	esyl213anc_3 $e |- ( ph -> ta ) $.
	esyl213anc_4 $e |- ( ph -> et ) $.
	esyl213anc_5 $e |- ( ph -> ze ) $.
	esyl213anc_6 $e |- ( ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) ) -> si ) $.
	syl213anc $p |- ( ph -> si ) $= fsyl213anc_0 fsyl213anc_1 fsyl213anc_2 wa fsyl213anc_3 fsyl213anc_4 fsyl213anc_5 fsyl213anc_6 fsyl213anc_7 fsyl213anc_0 fsyl213anc_1 fsyl213anc_2 esyl213anc_0 esyl213anc_1 jca esyl213anc_2 esyl213anc_3 esyl213anc_4 esyl213anc_5 esyl213anc_6 syl113anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl231anc_0 $f wff ph $.
	fsyl231anc_1 $f wff ps $.
	fsyl231anc_2 $f wff ch $.
	fsyl231anc_3 $f wff th $.
	fsyl231anc_4 $f wff ta $.
	fsyl231anc_5 $f wff et $.
	fsyl231anc_6 $f wff ze $.
	fsyl231anc_7 $f wff si $.
	esyl231anc_0 $e |- ( ph -> ps ) $.
	esyl231anc_1 $e |- ( ph -> ch ) $.
	esyl231anc_2 $e |- ( ph -> th ) $.
	esyl231anc_3 $e |- ( ph -> ta ) $.
	esyl231anc_4 $e |- ( ph -> et ) $.
	esyl231anc_5 $e |- ( ph -> ze ) $.
	esyl231anc_6 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze ) -> si ) $.
	syl231anc $p |- ( ph -> si ) $= fsyl231anc_0 fsyl231anc_1 fsyl231anc_2 wa fsyl231anc_3 fsyl231anc_4 fsyl231anc_5 fsyl231anc_6 fsyl231anc_7 fsyl231anc_0 fsyl231anc_1 fsyl231anc_2 esyl231anc_0 esyl231anc_1 jca esyl231anc_2 esyl231anc_3 esyl231anc_4 esyl231anc_5 esyl231anc_6 syl131anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl312anc_0 $f wff ph $.
	fsyl312anc_1 $f wff ps $.
	fsyl312anc_2 $f wff ch $.
	fsyl312anc_3 $f wff th $.
	fsyl312anc_4 $f wff ta $.
	fsyl312anc_5 $f wff et $.
	fsyl312anc_6 $f wff ze $.
	fsyl312anc_7 $f wff si $.
	esyl312anc_0 $e |- ( ph -> ps ) $.
	esyl312anc_1 $e |- ( ph -> ch ) $.
	esyl312anc_2 $e |- ( ph -> th ) $.
	esyl312anc_3 $e |- ( ph -> ta ) $.
	esyl312anc_4 $e |- ( ph -> et ) $.
	esyl312anc_5 $e |- ( ph -> ze ) $.
	esyl312anc_6 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) ) -> si ) $.
	syl312anc $p |- ( ph -> si ) $= fsyl312anc_0 fsyl312anc_1 fsyl312anc_2 fsyl312anc_3 fsyl312anc_4 fsyl312anc_5 fsyl312anc_6 wa fsyl312anc_7 esyl312anc_0 esyl312anc_1 esyl312anc_2 esyl312anc_3 fsyl312anc_0 fsyl312anc_5 fsyl312anc_6 esyl312anc_4 esyl312anc_5 jca esyl312anc_6 syl311anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Jul-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl321anc_0 $f wff ph $.
	fsyl321anc_1 $f wff ps $.
	fsyl321anc_2 $f wff ch $.
	fsyl321anc_3 $f wff th $.
	fsyl321anc_4 $f wff ta $.
	fsyl321anc_5 $f wff et $.
	fsyl321anc_6 $f wff ze $.
	fsyl321anc_7 $f wff si $.
	esyl321anc_0 $e |- ( ph -> ps ) $.
	esyl321anc_1 $e |- ( ph -> ch ) $.
	esyl321anc_2 $e |- ( ph -> th ) $.
	esyl321anc_3 $e |- ( ph -> ta ) $.
	esyl321anc_4 $e |- ( ph -> et ) $.
	esyl321anc_5 $e |- ( ph -> ze ) $.
	esyl321anc_6 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze ) -> si ) $.
	syl321anc $p |- ( ph -> si ) $= fsyl321anc_0 fsyl321anc_1 fsyl321anc_2 fsyl321anc_3 fsyl321anc_4 fsyl321anc_5 wa fsyl321anc_6 fsyl321anc_7 esyl321anc_0 esyl321anc_1 esyl321anc_2 fsyl321anc_0 fsyl321anc_4 fsyl321anc_5 esyl321anc_3 esyl321anc_4 jca esyl321anc_5 esyl321anc_6 syl311anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl133anc_0 $f wff ph $.
	fsyl133anc_1 $f wff ps $.
	fsyl133anc_2 $f wff ch $.
	fsyl133anc_3 $f wff th $.
	fsyl133anc_4 $f wff ta $.
	fsyl133anc_5 $f wff et $.
	fsyl133anc_6 $f wff ze $.
	fsyl133anc_7 $f wff si $.
	fsyl133anc_8 $f wff rh $.
	esyl133anc_0 $e |- ( ph -> ps ) $.
	esyl133anc_1 $e |- ( ph -> ch ) $.
	esyl133anc_2 $e |- ( ph -> th ) $.
	esyl133anc_3 $e |- ( ph -> ta ) $.
	esyl133anc_4 $e |- ( ph -> et ) $.
	esyl133anc_5 $e |- ( ph -> ze ) $.
	esyl133anc_6 $e |- ( ph -> si ) $.
	esyl133anc_7 $e |- ( ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh ) $.
	syl133anc $p |- ( ph -> rh ) $= fsyl133anc_0 fsyl133anc_1 fsyl133anc_2 fsyl133anc_3 fsyl133anc_4 fsyl133anc_5 fsyl133anc_6 fsyl133anc_7 w3a fsyl133anc_8 esyl133anc_0 esyl133anc_1 esyl133anc_2 esyl133anc_3 fsyl133anc_0 fsyl133anc_5 fsyl133anc_6 fsyl133anc_7 esyl133anc_4 esyl133anc_5 esyl133anc_6 3jca esyl133anc_7 syl131anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl313anc_0 $f wff ph $.
	fsyl313anc_1 $f wff ps $.
	fsyl313anc_2 $f wff ch $.
	fsyl313anc_3 $f wff th $.
	fsyl313anc_4 $f wff ta $.
	fsyl313anc_5 $f wff et $.
	fsyl313anc_6 $f wff ze $.
	fsyl313anc_7 $f wff si $.
	fsyl313anc_8 $f wff rh $.
	esyl313anc_0 $e |- ( ph -> ps ) $.
	esyl313anc_1 $e |- ( ph -> ch ) $.
	esyl313anc_2 $e |- ( ph -> th ) $.
	esyl313anc_3 $e |- ( ph -> ta ) $.
	esyl313anc_4 $e |- ( ph -> et ) $.
	esyl313anc_5 $e |- ( ph -> ze ) $.
	esyl313anc_6 $e |- ( ph -> si ) $.
	esyl313anc_7 $e |- ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) ) -> rh ) $.
	syl313anc $p |- ( ph -> rh ) $= fsyl313anc_0 fsyl313anc_1 fsyl313anc_2 fsyl313anc_3 fsyl313anc_4 fsyl313anc_5 fsyl313anc_6 fsyl313anc_7 w3a fsyl313anc_8 esyl313anc_0 esyl313anc_1 esyl313anc_2 esyl313anc_3 fsyl313anc_0 fsyl313anc_5 fsyl313anc_6 fsyl313anc_7 esyl313anc_4 esyl313anc_5 esyl313anc_6 3jca esyl313anc_7 syl311anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl331anc_0 $f wff ph $.
	fsyl331anc_1 $f wff ps $.
	fsyl331anc_2 $f wff ch $.
	fsyl331anc_3 $f wff th $.
	fsyl331anc_4 $f wff ta $.
	fsyl331anc_5 $f wff et $.
	fsyl331anc_6 $f wff ze $.
	fsyl331anc_7 $f wff si $.
	fsyl331anc_8 $f wff rh $.
	esyl331anc_0 $e |- ( ph -> ps ) $.
	esyl331anc_1 $e |- ( ph -> ch ) $.
	esyl331anc_2 $e |- ( ph -> th ) $.
	esyl331anc_3 $e |- ( ph -> ta ) $.
	esyl331anc_4 $e |- ( ph -> et ) $.
	esyl331anc_5 $e |- ( ph -> ze ) $.
	esyl331anc_6 $e |- ( ph -> si ) $.
	esyl331anc_7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si ) -> rh ) $.
	syl331anc $p |- ( ph -> rh ) $= fsyl331anc_0 fsyl331anc_1 fsyl331anc_2 fsyl331anc_3 fsyl331anc_4 fsyl331anc_5 fsyl331anc_6 w3a fsyl331anc_7 fsyl331anc_8 esyl331anc_0 esyl331anc_1 esyl331anc_2 fsyl331anc_0 fsyl331anc_4 fsyl331anc_5 fsyl331anc_6 esyl331anc_3 esyl331anc_4 esyl331anc_5 3jca esyl331anc_6 esyl331anc_7 syl311anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl223anc_0 $f wff ph $.
	fsyl223anc_1 $f wff ps $.
	fsyl223anc_2 $f wff ch $.
	fsyl223anc_3 $f wff th $.
	fsyl223anc_4 $f wff ta $.
	fsyl223anc_5 $f wff et $.
	fsyl223anc_6 $f wff ze $.
	fsyl223anc_7 $f wff si $.
	fsyl223anc_8 $f wff rh $.
	esyl223anc_0 $e |- ( ph -> ps ) $.
	esyl223anc_1 $e |- ( ph -> ch ) $.
	esyl223anc_2 $e |- ( ph -> th ) $.
	esyl223anc_3 $e |- ( ph -> ta ) $.
	esyl223anc_4 $e |- ( ph -> et ) $.
	esyl223anc_5 $e |- ( ph -> ze ) $.
	esyl223anc_6 $e |- ( ph -> si ) $.
	esyl223anc_7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh ) $.
	syl223anc $p |- ( ph -> rh ) $= fsyl223anc_0 fsyl223anc_1 fsyl223anc_2 fsyl223anc_3 fsyl223anc_4 wa fsyl223anc_5 fsyl223anc_6 fsyl223anc_7 fsyl223anc_8 esyl223anc_0 esyl223anc_1 fsyl223anc_0 fsyl223anc_3 fsyl223anc_4 esyl223anc_2 esyl223anc_3 jca esyl223anc_4 esyl223anc_5 esyl223anc_6 esyl223anc_7 syl213anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl232anc_0 $f wff ph $.
	fsyl232anc_1 $f wff ps $.
	fsyl232anc_2 $f wff ch $.
	fsyl232anc_3 $f wff th $.
	fsyl232anc_4 $f wff ta $.
	fsyl232anc_5 $f wff et $.
	fsyl232anc_6 $f wff ze $.
	fsyl232anc_7 $f wff si $.
	fsyl232anc_8 $f wff rh $.
	esyl232anc_0 $e |- ( ph -> ps ) $.
	esyl232anc_1 $e |- ( ph -> ch ) $.
	esyl232anc_2 $e |- ( ph -> th ) $.
	esyl232anc_3 $e |- ( ph -> ta ) $.
	esyl232anc_4 $e |- ( ph -> et ) $.
	esyl232anc_5 $e |- ( ph -> ze ) $.
	esyl232anc_6 $e |- ( ph -> si ) $.
	esyl232anc_7 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si ) ) -> rh ) $.
	syl232anc $p |- ( ph -> rh ) $= fsyl232anc_0 fsyl232anc_1 fsyl232anc_2 fsyl232anc_3 fsyl232anc_4 fsyl232anc_5 fsyl232anc_6 fsyl232anc_7 wa fsyl232anc_8 esyl232anc_0 esyl232anc_1 esyl232anc_2 esyl232anc_3 esyl232anc_4 fsyl232anc_0 fsyl232anc_6 fsyl232anc_7 esyl232anc_5 esyl232anc_6 jca esyl232anc_7 syl231anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	fsyl322anc_0 $f wff ph $.
	fsyl322anc_1 $f wff ps $.
	fsyl322anc_2 $f wff ch $.
	fsyl322anc_3 $f wff th $.
	fsyl322anc_4 $f wff ta $.
	fsyl322anc_5 $f wff et $.
	fsyl322anc_6 $f wff ze $.
	fsyl322anc_7 $f wff si $.
	fsyl322anc_8 $f wff rh $.
	esyl322anc_0 $e |- ( ph -> ps ) $.
	esyl322anc_1 $e |- ( ph -> ch ) $.
	esyl322anc_2 $e |- ( ph -> th ) $.
	esyl322anc_3 $e |- ( ph -> ta ) $.
	esyl322anc_4 $e |- ( ph -> et ) $.
	esyl322anc_5 $e |- ( ph -> ze ) $.
	esyl322anc_6 $e |- ( ph -> si ) $.
	esyl322anc_7 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si ) ) -> rh ) $.
	syl322anc $p |- ( ph -> rh ) $= fsyl322anc_0 fsyl322anc_1 fsyl322anc_2 fsyl322anc_3 fsyl322anc_4 fsyl322anc_5 fsyl322anc_6 fsyl322anc_7 wa fsyl322anc_8 esyl322anc_0 esyl322anc_1 esyl322anc_2 esyl322anc_3 esyl322anc_4 fsyl322anc_0 fsyl322anc_6 fsyl322anc_7 esyl322anc_5 esyl322anc_6 jca esyl322anc_7 syl321anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fsyl233anc_0 $f wff ph $.
	fsyl233anc_1 $f wff ps $.
	fsyl233anc_2 $f wff ch $.
	fsyl233anc_3 $f wff th $.
	fsyl233anc_4 $f wff ta $.
	fsyl233anc_5 $f wff et $.
	fsyl233anc_6 $f wff ze $.
	fsyl233anc_7 $f wff si $.
	fsyl233anc_8 $f wff rh $.
	fsyl233anc_9 $f wff mu $.
	esyl233anc_0 $e |- ( ph -> ps ) $.
	esyl233anc_1 $e |- ( ph -> ch ) $.
	esyl233anc_2 $e |- ( ph -> th ) $.
	esyl233anc_3 $e |- ( ph -> ta ) $.
	esyl233anc_4 $e |- ( ph -> et ) $.
	esyl233anc_5 $e |- ( ph -> ze ) $.
	esyl233anc_6 $e |- ( ph -> si ) $.
	esyl233anc_7 $e |- ( ph -> rh ) $.
	esyl233anc_8 $e |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu ) $.
	syl233anc $p |- ( ph -> mu ) $= fsyl233anc_0 fsyl233anc_1 fsyl233anc_2 wa fsyl233anc_3 fsyl233anc_4 fsyl233anc_5 fsyl233anc_6 fsyl233anc_7 fsyl233anc_8 fsyl233anc_9 fsyl233anc_0 fsyl233anc_1 fsyl233anc_2 esyl233anc_0 esyl233anc_1 jca esyl233anc_2 esyl233anc_3 esyl233anc_4 esyl233anc_5 esyl233anc_6 esyl233anc_7 esyl233anc_8 syl133anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fsyl323anc_0 $f wff ph $.
	fsyl323anc_1 $f wff ps $.
	fsyl323anc_2 $f wff ch $.
	fsyl323anc_3 $f wff th $.
	fsyl323anc_4 $f wff ta $.
	fsyl323anc_5 $f wff et $.
	fsyl323anc_6 $f wff ze $.
	fsyl323anc_7 $f wff si $.
	fsyl323anc_8 $f wff rh $.
	fsyl323anc_9 $f wff mu $.
	esyl323anc_0 $e |- ( ph -> ps ) $.
	esyl323anc_1 $e |- ( ph -> ch ) $.
	esyl323anc_2 $e |- ( ph -> th ) $.
	esyl323anc_3 $e |- ( ph -> ta ) $.
	esyl323anc_4 $e |- ( ph -> et ) $.
	esyl323anc_5 $e |- ( ph -> ze ) $.
	esyl323anc_6 $e |- ( ph -> si ) $.
	esyl323anc_7 $e |- ( ph -> rh ) $.
	esyl323anc_8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu ) $.
	syl323anc $p |- ( ph -> mu ) $= fsyl323anc_0 fsyl323anc_1 fsyl323anc_2 fsyl323anc_3 fsyl323anc_4 fsyl323anc_5 wa fsyl323anc_6 fsyl323anc_7 fsyl323anc_8 fsyl323anc_9 esyl323anc_0 esyl323anc_1 esyl323anc_2 fsyl323anc_0 fsyl323anc_4 fsyl323anc_5 esyl323anc_3 esyl323anc_4 jca esyl323anc_5 esyl323anc_6 esyl323anc_7 esyl323anc_8 syl313anc $.
$}
$( Syllogism combined with contraction.  (Contributed by NM,
         11-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	fsyl332anc_0 $f wff ph $.
	fsyl332anc_1 $f wff ps $.
	fsyl332anc_2 $f wff ch $.
	fsyl332anc_3 $f wff th $.
	fsyl332anc_4 $f wff ta $.
	fsyl332anc_5 $f wff et $.
	fsyl332anc_6 $f wff ze $.
	fsyl332anc_7 $f wff si $.
	fsyl332anc_8 $f wff rh $.
	fsyl332anc_9 $f wff mu $.
	esyl332anc_0 $e |- ( ph -> ps ) $.
	esyl332anc_1 $e |- ( ph -> ch ) $.
	esyl332anc_2 $e |- ( ph -> th ) $.
	esyl332anc_3 $e |- ( ph -> ta ) $.
	esyl332anc_4 $e |- ( ph -> et ) $.
	esyl332anc_5 $e |- ( ph -> ze ) $.
	esyl332anc_6 $e |- ( ph -> si ) $.
	esyl332anc_7 $e |- ( ph -> rh ) $.
	esyl332anc_8 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh ) ) -> mu ) $.
	syl332anc $p |- ( ph -> mu ) $= fsyl332anc_0 fsyl332anc_1 fsyl332anc_2 fsyl332anc_3 fsyl332anc_4 fsyl332anc_5 fsyl332anc_6 fsyl332anc_7 fsyl332anc_8 wa fsyl332anc_9 esyl332anc_0 esyl332anc_1 esyl332anc_2 esyl332anc_3 esyl332anc_4 esyl332anc_5 fsyl332anc_0 fsyl332anc_7 fsyl332anc_8 esyl332anc_6 esyl332anc_7 jca esyl332anc_8 syl331anc $.
$}
$( A syllogism inference combined with contraction.  (Contributed by NM,
         10-Mar-2012.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	$v rh $.
	$v mu $.
	$v la $.
	fsyl333anc_0 $f wff ph $.
	fsyl333anc_1 $f wff ps $.
	fsyl333anc_2 $f wff ch $.
	fsyl333anc_3 $f wff th $.
	fsyl333anc_4 $f wff ta $.
	fsyl333anc_5 $f wff et $.
	fsyl333anc_6 $f wff ze $.
	fsyl333anc_7 $f wff si $.
	fsyl333anc_8 $f wff rh $.
	fsyl333anc_9 $f wff mu $.
	fsyl333anc_10 $f wff la $.
	esyl333anc_0 $e |- ( ph -> ps ) $.
	esyl333anc_1 $e |- ( ph -> ch ) $.
	esyl333anc_2 $e |- ( ph -> th ) $.
	esyl333anc_3 $e |- ( ph -> ta ) $.
	esyl333anc_4 $e |- ( ph -> et ) $.
	esyl333anc_5 $e |- ( ph -> ze ) $.
	esyl333anc_6 $e |- ( ph -> si ) $.
	esyl333anc_7 $e |- ( ph -> rh ) $.
	esyl333anc_8 $e |- ( ph -> mu ) $.
	esyl333anc_9 $e |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh /\ mu ) ) -> la ) $.
	syl333anc $p |- ( ph -> la ) $= fsyl333anc_0 fsyl333anc_1 fsyl333anc_2 fsyl333anc_3 fsyl333anc_4 fsyl333anc_5 fsyl333anc_6 fsyl333anc_7 fsyl333anc_8 fsyl333anc_9 w3a fsyl333anc_10 esyl333anc_0 esyl333anc_1 esyl333anc_2 esyl333anc_3 esyl333anc_4 esyl333anc_5 fsyl333anc_0 fsyl333anc_7 fsyl333anc_8 fsyl333anc_9 esyl333anc_6 esyl333anc_7 esyl333anc_8 3jca esyl333anc_9 syl331anc $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an1_0 $f wff ph $.
	fsyl3an1_1 $f wff ps $.
	fsyl3an1_2 $f wff ch $.
	fsyl3an1_3 $f wff th $.
	fsyl3an1_4 $f wff ta $.
	esyl3an1_0 $e |- ( ph -> ps ) $.
	esyl3an1_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an1 $p |- ( ( ph /\ ch /\ th ) -> ta ) $= fsyl3an1_0 fsyl3an1_2 fsyl3an1_3 w3a fsyl3an1_1 fsyl3an1_2 fsyl3an1_3 w3a fsyl3an1_4 fsyl3an1_0 fsyl3an1_1 fsyl3an1_2 fsyl3an1_3 esyl3an1_0 3anim1i esyl3an1_1 syl $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an2_0 $f wff ph $.
	fsyl3an2_1 $f wff ps $.
	fsyl3an2_2 $f wff ch $.
	fsyl3an2_3 $f wff th $.
	fsyl3an2_4 $f wff ta $.
	esyl3an2_0 $e |- ( ph -> ch ) $.
	esyl3an2_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an2 $p |- ( ( ps /\ ph /\ th ) -> ta ) $= fsyl3an2_1 fsyl3an2_0 fsyl3an2_3 fsyl3an2_4 fsyl3an2_0 fsyl3an2_2 fsyl3an2_1 fsyl3an2_3 fsyl3an2_4 wi esyl3an2_0 fsyl3an2_1 fsyl3an2_2 fsyl3an2_3 fsyl3an2_4 esyl3an2_1 3exp syl5 3imp $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an3_0 $f wff ph $.
	fsyl3an3_1 $f wff ps $.
	fsyl3an3_2 $f wff ch $.
	fsyl3an3_3 $f wff th $.
	fsyl3an3_4 $f wff ta $.
	esyl3an3_0 $e |- ( ph -> th ) $.
	esyl3an3_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an3 $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= fsyl3an3_1 fsyl3an3_2 fsyl3an3_0 fsyl3an3_4 fsyl3an3_0 fsyl3an3_3 fsyl3an3_1 fsyl3an3_2 fsyl3an3_4 esyl3an3_0 fsyl3an3_1 fsyl3an3_2 fsyl3an3_3 fsyl3an3_4 esyl3an3_1 3exp syl7 3imp $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an1b_0 $f wff ph $.
	fsyl3an1b_1 $f wff ps $.
	fsyl3an1b_2 $f wff ch $.
	fsyl3an1b_3 $f wff th $.
	fsyl3an1b_4 $f wff ta $.
	esyl3an1b_0 $e |- ( ph <-> ps ) $.
	esyl3an1b_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an1b $p |- ( ( ph /\ ch /\ th ) -> ta ) $= fsyl3an1b_0 fsyl3an1b_1 fsyl3an1b_2 fsyl3an1b_3 fsyl3an1b_4 fsyl3an1b_0 fsyl3an1b_1 esyl3an1b_0 biimpi esyl3an1b_1 syl3an1 $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an2b_0 $f wff ph $.
	fsyl3an2b_1 $f wff ps $.
	fsyl3an2b_2 $f wff ch $.
	fsyl3an2b_3 $f wff th $.
	fsyl3an2b_4 $f wff ta $.
	esyl3an2b_0 $e |- ( ph <-> ch ) $.
	esyl3an2b_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an2b $p |- ( ( ps /\ ph /\ th ) -> ta ) $= fsyl3an2b_0 fsyl3an2b_1 fsyl3an2b_2 fsyl3an2b_3 fsyl3an2b_4 fsyl3an2b_0 fsyl3an2b_2 esyl3an2b_0 biimpi esyl3an2b_1 syl3an2 $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an3b_0 $f wff ph $.
	fsyl3an3b_1 $f wff ps $.
	fsyl3an3b_2 $f wff ch $.
	fsyl3an3b_3 $f wff th $.
	fsyl3an3b_4 $f wff ta $.
	esyl3an3b_0 $e |- ( ph <-> th ) $.
	esyl3an3b_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an3b $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= fsyl3an3b_0 fsyl3an3b_1 fsyl3an3b_2 fsyl3an3b_3 fsyl3an3b_4 fsyl3an3b_0 fsyl3an3b_3 esyl3an3b_0 biimpi esyl3an3b_1 syl3an3 $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an1br_0 $f wff ph $.
	fsyl3an1br_1 $f wff ps $.
	fsyl3an1br_2 $f wff ch $.
	fsyl3an1br_3 $f wff th $.
	fsyl3an1br_4 $f wff ta $.
	esyl3an1br_0 $e |- ( ps <-> ph ) $.
	esyl3an1br_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an1br $p |- ( ( ph /\ ch /\ th ) -> ta ) $= fsyl3an1br_0 fsyl3an1br_1 fsyl3an1br_2 fsyl3an1br_3 fsyl3an1br_4 fsyl3an1br_1 fsyl3an1br_0 esyl3an1br_0 biimpri esyl3an1br_1 syl3an1 $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an2br_0 $f wff ph $.
	fsyl3an2br_1 $f wff ps $.
	fsyl3an2br_2 $f wff ch $.
	fsyl3an2br_3 $f wff th $.
	fsyl3an2br_4 $f wff ta $.
	esyl3an2br_0 $e |- ( ch <-> ph ) $.
	esyl3an2br_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an2br $p |- ( ( ps /\ ph /\ th ) -> ta ) $= fsyl3an2br_0 fsyl3an2br_1 fsyl3an2br_2 fsyl3an2br_3 fsyl3an2br_4 fsyl3an2br_2 fsyl3an2br_0 esyl3an2br_0 biimpri esyl3an2br_1 syl3an2 $.
$}
$( A syllogism inference.  (Contributed by NM, 22-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyl3an3br_0 $f wff ph $.
	fsyl3an3br_1 $f wff ps $.
	fsyl3an3br_2 $f wff ch $.
	fsyl3an3br_3 $f wff th $.
	fsyl3an3br_4 $f wff ta $.
	esyl3an3br_0 $e |- ( th <-> ph ) $.
	esyl3an3br_1 $e |- ( ( ps /\ ch /\ th ) -> ta ) $.
	syl3an3br $p |- ( ( ps /\ ch /\ ph ) -> ta ) $= fsyl3an3br_0 fsyl3an3br_1 fsyl3an3br_2 fsyl3an3br_3 fsyl3an3br_4 fsyl3an3br_3 fsyl3an3br_0 esyl3an3br_0 biimpri esyl3an3br_1 syl3an3 $.
$}
$( A triple syllogism inference.  (Contributed by NM, 13-May-2004.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl3an_0 $f wff ph $.
	fsyl3an_1 $f wff ps $.
	fsyl3an_2 $f wff ch $.
	fsyl3an_3 $f wff th $.
	fsyl3an_4 $f wff ta $.
	fsyl3an_5 $f wff et $.
	fsyl3an_6 $f wff ze $.
	esyl3an_0 $e |- ( ph -> ps ) $.
	esyl3an_1 $e |- ( ch -> th ) $.
	esyl3an_2 $e |- ( ta -> et ) $.
	esyl3an_3 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	syl3an $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= fsyl3an_0 fsyl3an_2 fsyl3an_4 w3a fsyl3an_1 fsyl3an_3 fsyl3an_5 w3a fsyl3an_6 fsyl3an_0 fsyl3an_1 fsyl3an_2 fsyl3an_3 fsyl3an_4 fsyl3an_5 esyl3an_0 esyl3an_1 esyl3an_2 3anim123i esyl3an_3 syl $.
$}
$( A triple syllogism inference.  (Contributed by NM, 15-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl3anb_0 $f wff ph $.
	fsyl3anb_1 $f wff ps $.
	fsyl3anb_2 $f wff ch $.
	fsyl3anb_3 $f wff th $.
	fsyl3anb_4 $f wff ta $.
	fsyl3anb_5 $f wff et $.
	fsyl3anb_6 $f wff ze $.
	esyl3anb_0 $e |- ( ph <-> ps ) $.
	esyl3anb_1 $e |- ( ch <-> th ) $.
	esyl3anb_2 $e |- ( ta <-> et ) $.
	esyl3anb_3 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	syl3anb $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= fsyl3anb_0 fsyl3anb_2 fsyl3anb_4 w3a fsyl3anb_1 fsyl3anb_3 fsyl3anb_5 w3a fsyl3anb_6 fsyl3anb_0 fsyl3anb_1 fsyl3anb_2 fsyl3anb_3 fsyl3anb_4 fsyl3anb_5 esyl3anb_0 esyl3anb_1 esyl3anb_2 3anbi123i esyl3anb_3 sylbi $.
$}
$( A triple syllogism inference.  (Contributed by NM, 29-Dec-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl3anbr_0 $f wff ph $.
	fsyl3anbr_1 $f wff ps $.
	fsyl3anbr_2 $f wff ch $.
	fsyl3anbr_3 $f wff th $.
	fsyl3anbr_4 $f wff ta $.
	fsyl3anbr_5 $f wff et $.
	fsyl3anbr_6 $f wff ze $.
	esyl3anbr_0 $e |- ( ps <-> ph ) $.
	esyl3anbr_1 $e |- ( th <-> ch ) $.
	esyl3anbr_2 $e |- ( et <-> ta ) $.
	esyl3anbr_3 $e |- ( ( ps /\ th /\ et ) -> ze ) $.
	syl3anbr $p |- ( ( ph /\ ch /\ ta ) -> ze ) $= fsyl3anbr_0 fsyl3anbr_1 fsyl3anbr_2 fsyl3anbr_3 fsyl3anbr_4 fsyl3anbr_5 fsyl3anbr_6 fsyl3anbr_1 fsyl3anbr_0 esyl3anbr_0 bicomi fsyl3anbr_3 fsyl3anbr_2 esyl3anbr_1 bicomi fsyl3anbr_5 fsyl3anbr_4 esyl3anbr_2 bicomi esyl3anbr_3 syl3anb $.
$}
$( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyld3an3_0 $f wff ph $.
	fsyld3an3_1 $f wff ps $.
	fsyld3an3_2 $f wff ch $.
	fsyld3an3_3 $f wff th $.
	fsyld3an3_4 $f wff ta $.
	esyld3an3_0 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	esyld3an3_1 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	syld3an3 $p |- ( ( ph /\ ps /\ ch ) -> ta ) $= fsyld3an3_0 fsyld3an3_1 fsyld3an3_2 w3a fsyld3an3_0 fsyld3an3_1 fsyld3an3_3 fsyld3an3_4 fsyld3an3_0 fsyld3an3_1 fsyld3an3_2 simp1 fsyld3an3_0 fsyld3an3_1 fsyld3an3_2 simp2 esyld3an3_0 esyld3an3_1 syl3anc $.
$}
$( A syllogism inference.  (Contributed by NM, 7-Jul-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyld3an1_0 $f wff ph $.
	fsyld3an1_1 $f wff ps $.
	fsyld3an1_2 $f wff ch $.
	fsyld3an1_3 $f wff th $.
	fsyld3an1_4 $f wff ta $.
	esyld3an1_0 $e |- ( ( ch /\ ps /\ th ) -> ph ) $.
	esyld3an1_1 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	syld3an1 $p |- ( ( ch /\ ps /\ th ) -> ta ) $= fsyld3an1_3 fsyld3an1_1 fsyld3an1_2 fsyld3an1_4 fsyld3an1_3 fsyld3an1_1 fsyld3an1_2 fsyld3an1_0 fsyld3an1_4 fsyld3an1_2 fsyld3an1_1 fsyld3an1_3 fsyld3an1_0 esyld3an1_0 3com13 fsyld3an1_0 fsyld3an1_1 fsyld3an1_3 fsyld3an1_4 esyld3an1_1 3com13 syld3an3 3com13 $.
$}
$( A syllogism inference.  (Contributed by NM, 20-May-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fsyld3an2_0 $f wff ph $.
	fsyld3an2_1 $f wff ps $.
	fsyld3an2_2 $f wff ch $.
	fsyld3an2_3 $f wff th $.
	fsyld3an2_4 $f wff ta $.
	esyld3an2_0 $e |- ( ( ph /\ ch /\ th ) -> ps ) $.
	esyld3an2_1 $e |- ( ( ph /\ ps /\ th ) -> ta ) $.
	syld3an2 $p |- ( ( ph /\ ch /\ th ) -> ta ) $= fsyld3an2_0 fsyld3an2_3 fsyld3an2_2 fsyld3an2_4 fsyld3an2_0 fsyld3an2_3 fsyld3an2_2 fsyld3an2_1 fsyld3an2_4 fsyld3an2_0 fsyld3an2_2 fsyld3an2_3 fsyld3an2_1 esyld3an2_0 3com23 fsyld3an2_0 fsyld3an2_1 fsyld3an2_3 fsyld3an2_4 esyld3an2_1 3com23 syld3an3 3com23 $.
$}
$( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anl1_0 $f wff ph $.
	fsyl3anl1_1 $f wff ps $.
	fsyl3anl1_2 $f wff ch $.
	fsyl3anl1_3 $f wff th $.
	fsyl3anl1_4 $f wff ta $.
	fsyl3anl1_5 $f wff et $.
	esyl3anl1_0 $e |- ( ph -> ps ) $.
	esyl3anl1_1 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	syl3anl1 $p |- ( ( ( ph /\ ch /\ th ) /\ ta ) -> et ) $= fsyl3anl1_0 fsyl3anl1_2 fsyl3anl1_3 w3a fsyl3anl1_1 fsyl3anl1_2 fsyl3anl1_3 w3a fsyl3anl1_4 fsyl3anl1_5 fsyl3anl1_0 fsyl3anl1_1 fsyl3anl1_2 fsyl3anl1_3 esyl3anl1_0 3anim1i esyl3anl1_1 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anl2_0 $f wff ph $.
	fsyl3anl2_1 $f wff ps $.
	fsyl3anl2_2 $f wff ch $.
	fsyl3anl2_3 $f wff th $.
	fsyl3anl2_4 $f wff ta $.
	fsyl3anl2_5 $f wff et $.
	esyl3anl2_0 $e |- ( ph -> ch ) $.
	esyl3anl2_1 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	syl3anl2 $p |- ( ( ( ps /\ ph /\ th ) /\ ta ) -> et ) $= fsyl3anl2_1 fsyl3anl2_0 fsyl3anl2_3 w3a fsyl3anl2_4 fsyl3anl2_5 fsyl3anl2_0 fsyl3anl2_1 fsyl3anl2_2 fsyl3anl2_3 fsyl3anl2_4 fsyl3anl2_5 wi esyl3anl2_0 fsyl3anl2_1 fsyl3anl2_2 fsyl3anl2_3 w3a fsyl3anl2_4 fsyl3anl2_5 esyl3anl2_1 ex syl3an2 imp $.
$}
$( A syllogism inference.  (Contributed by NM, 24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anl3_0 $f wff ph $.
	fsyl3anl3_1 $f wff ps $.
	fsyl3anl3_2 $f wff ch $.
	fsyl3anl3_3 $f wff th $.
	fsyl3anl3_4 $f wff ta $.
	fsyl3anl3_5 $f wff et $.
	esyl3anl3_0 $e |- ( ph -> th ) $.
	esyl3anl3_1 $e |- ( ( ( ps /\ ch /\ th ) /\ ta ) -> et ) $.
	syl3anl3 $p |- ( ( ( ps /\ ch /\ ph ) /\ ta ) -> et ) $= fsyl3anl3_1 fsyl3anl3_2 fsyl3anl3_0 w3a fsyl3anl3_1 fsyl3anl3_2 fsyl3anl3_3 w3a fsyl3anl3_4 fsyl3anl3_5 fsyl3anl3_0 fsyl3anl3_3 fsyl3anl3_1 fsyl3anl3_2 esyl3anl3_0 3anim3i esyl3anl3_1 sylan $.
$}
$( A triple syllogism inference.  (Contributed by NM, 24-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	$v si $.
	fsyl3anl_0 $f wff ph $.
	fsyl3anl_1 $f wff ps $.
	fsyl3anl_2 $f wff ch $.
	fsyl3anl_3 $f wff th $.
	fsyl3anl_4 $f wff ta $.
	fsyl3anl_5 $f wff et $.
	fsyl3anl_6 $f wff ze $.
	fsyl3anl_7 $f wff si $.
	esyl3anl_0 $e |- ( ph -> ps ) $.
	esyl3anl_1 $e |- ( ch -> th ) $.
	esyl3anl_2 $e |- ( ta -> et ) $.
	esyl3anl_3 $e |- ( ( ( ps /\ th /\ et ) /\ ze ) -> si ) $.
	syl3anl $p |- ( ( ( ph /\ ch /\ ta ) /\ ze ) -> si ) $= fsyl3anl_0 fsyl3anl_2 fsyl3anl_4 w3a fsyl3anl_1 fsyl3anl_3 fsyl3anl_5 w3a fsyl3anl_6 fsyl3anl_7 fsyl3anl_0 fsyl3anl_1 fsyl3anl_2 fsyl3anl_3 fsyl3anl_4 fsyl3anl_5 esyl3anl_0 esyl3anl_1 esyl3anl_2 3anim123i esyl3anl_3 sylan $.
$}
$( A syllogism inference.  (Contributed by NM, 31-Jul-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anr1_0 $f wff ph $.
	fsyl3anr1_1 $f wff ps $.
	fsyl3anr1_2 $f wff ch $.
	fsyl3anr1_3 $f wff th $.
	fsyl3anr1_4 $f wff ta $.
	fsyl3anr1_5 $f wff et $.
	esyl3anr1_0 $e |- ( ph -> ps ) $.
	esyl3anr1_1 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	syl3anr1 $p |- ( ( ch /\ ( ph /\ th /\ ta ) ) -> et ) $= fsyl3anr1_0 fsyl3anr1_3 fsyl3anr1_4 w3a fsyl3anr1_2 fsyl3anr1_1 fsyl3anr1_3 fsyl3anr1_4 w3a fsyl3anr1_5 fsyl3anr1_0 fsyl3anr1_1 fsyl3anr1_3 fsyl3anr1_4 esyl3anr1_0 3anim1i esyl3anr1_1 sylan2 $.
$}
$( A syllogism inference.  (Contributed by NM, 1-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anr2_0 $f wff ph $.
	fsyl3anr2_1 $f wff ps $.
	fsyl3anr2_2 $f wff ch $.
	fsyl3anr2_3 $f wff th $.
	fsyl3anr2_4 $f wff ta $.
	fsyl3anr2_5 $f wff et $.
	esyl3anr2_0 $e |- ( ph -> th ) $.
	esyl3anr2_1 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	syl3anr2 $p |- ( ( ch /\ ( ps /\ ph /\ ta ) ) -> et ) $= fsyl3anr2_1 fsyl3anr2_0 fsyl3anr2_4 w3a fsyl3anr2_2 fsyl3anr2_5 fsyl3anr2_0 fsyl3anr2_1 fsyl3anr2_3 fsyl3anr2_4 fsyl3anr2_2 fsyl3anr2_5 esyl3anr2_0 fsyl3anr2_2 fsyl3anr2_1 fsyl3anr2_3 fsyl3anr2_4 w3a fsyl3anr2_5 esyl3anr2_1 ancoms syl3anl2 ancoms $.
$}
$( A syllogism inference.  (Contributed by NM, 23-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fsyl3anr3_0 $f wff ph $.
	fsyl3anr3_1 $f wff ps $.
	fsyl3anr3_2 $f wff ch $.
	fsyl3anr3_3 $f wff th $.
	fsyl3anr3_4 $f wff ta $.
	fsyl3anr3_5 $f wff et $.
	esyl3anr3_0 $e |- ( ph -> ta ) $.
	esyl3anr3_1 $e |- ( ( ch /\ ( ps /\ th /\ ta ) ) -> et ) $.
	syl3anr3 $p |- ( ( ch /\ ( ps /\ th /\ ph ) ) -> et ) $= fsyl3anr3_1 fsyl3anr3_3 fsyl3anr3_0 w3a fsyl3anr3_2 fsyl3anr3_1 fsyl3anr3_3 fsyl3anr3_4 w3a fsyl3anr3_5 fsyl3anr3_0 fsyl3anr3_4 fsyl3anr3_1 fsyl3anr3_3 esyl3anr3_0 3anim3i esyl3anr3_1 sylan2 $.
$}
$( Importation inference (undistribute conjunction).  (Contributed by NM,
       14-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impdi_0 $f wff ph $.
	f3impdi_1 $f wff ps $.
	f3impdi_2 $f wff ch $.
	f3impdi_3 $f wff th $.
	e3impdi_0 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th ) $.
	3impdi $p |- ( ( ph /\ ps /\ ch ) -> th ) $= f3impdi_0 f3impdi_1 f3impdi_2 f3impdi_3 f3impdi_0 f3impdi_1 f3impdi_2 f3impdi_3 e3impdi_0 anandis 3impb $.
$}
$( Importation inference (undistribute conjunction).  (Contributed by NM,
       20-Aug-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3impdir_0 $f wff ph $.
	f3impdir_1 $f wff ps $.
	f3impdir_2 $f wff ch $.
	f3impdir_3 $f wff th $.
	e3impdir_0 $e |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th ) $.
	3impdir $p |- ( ( ph /\ ch /\ ps ) -> th ) $= f3impdir_0 f3impdir_2 f3impdir_1 f3impdir_3 f3impdir_0 f3impdir_2 f3impdir_1 f3impdir_3 e3impdir_0 anandirs 3impa $.
$}
$( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anidm12_0 $f wff ph $.
	f3anidm12_1 $f wff ps $.
	f3anidm12_2 $f wff ch $.
	e3anidm12_0 $e |- ( ( ph /\ ph /\ ps ) -> ch ) $.
	3anidm12 $p |- ( ( ph /\ ps ) -> ch ) $= f3anidm12_0 f3anidm12_1 f3anidm12_2 f3anidm12_0 f3anidm12_0 f3anidm12_1 f3anidm12_2 e3anidm12_0 3expib anabsi5 $.
$}
$( Inference from idempotent law for conjunction.  (Contributed by NM,
       7-Mar-2008.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anidm13_0 $f wff ph $.
	f3anidm13_1 $f wff ps $.
	f3anidm13_2 $f wff ch $.
	e3anidm13_0 $e |- ( ( ph /\ ps /\ ph ) -> ch ) $.
	3anidm13 $p |- ( ( ph /\ ps ) -> ch ) $= f3anidm13_0 f3anidm13_1 f3anidm13_2 f3anidm13_0 f3anidm13_1 f3anidm13_0 f3anidm13_2 e3anidm13_0 3com23 3anidm12 $.
$}
$( Inference from idempotent law for conjunction.  (Contributed by NM,
       1-Feb-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3anidm23_0 $f wff ph $.
	f3anidm23_1 $f wff ps $.
	f3anidm23_2 $f wff ch $.
	e3anidm23_0 $e |- ( ( ph /\ ps /\ ps ) -> ch ) $.
	3anidm23 $p |- ( ( ph /\ ps ) -> ch ) $= f3anidm23_0 f3anidm23_1 f3anidm23_2 f3anidm23_0 f3anidm23_1 f3anidm23_1 f3anidm23_2 e3anidm23_0 3expa anabss3 $.
$}
$( Infer implication from triple disjunction.  (Contributed by NM,
       26-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	f3ori_0 $f wff ph $.
	f3ori_1 $f wff ps $.
	f3ori_2 $f wff ch $.
	e3ori_0 $e |- ( ph \/ ps \/ ch ) $.
	3ori $p |- ( ( -. ph /\ -. ps ) -> ch ) $= f3ori_0 wn f3ori_1 wn wa f3ori_0 f3ori_1 wo wn f3ori_2 f3ori_0 f3ori_1 ioran f3ori_0 f3ori_1 wo f3ori_2 f3ori_0 f3ori_1 f3ori_2 w3o f3ori_0 f3ori_1 wo f3ori_2 wo e3ori_0 f3ori_0 f3ori_1 f3ori_2 df-3or mpbi ori sylbir $.
$}
$( Disjunction of 3 antecedents.  (Contributed by NM, 8-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3jao_0 $f wff ph $.
	f3jao_1 $f wff ps $.
	f3jao_2 $f wff ch $.
	f3jao_3 $f wff th $.
	3jao $p |- ( ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) -> ( ( ph \/ ch \/ th ) -> ps ) ) $= f3jao_0 f3jao_2 f3jao_3 w3o f3jao_0 f3jao_2 wo f3jao_3 wo f3jao_0 f3jao_1 wi f3jao_2 f3jao_1 wi f3jao_3 f3jao_1 wi w3a f3jao_1 f3jao_0 f3jao_2 f3jao_3 df-3or f3jao_0 f3jao_1 wi f3jao_2 f3jao_1 wi f3jao_3 f3jao_1 wi f3jao_0 f3jao_2 wo f3jao_3 wo f3jao_1 wi f3jao_0 f3jao_1 wi f3jao_2 f3jao_1 wi f3jao_0 f3jao_2 wo f3jao_1 wi f3jao_3 f3jao_1 wi f3jao_0 f3jao_2 wo f3jao_3 wo f3jao_1 wi wi f3jao_0 f3jao_1 f3jao_2 jao f3jao_0 f3jao_2 wo f3jao_1 f3jao_3 jao syl6 3imp syl5bi $.
$}
$( Disjunction of 3 antecedents.  (Contributed by NM, 13-Sep-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3jaob_0 $f wff ph $.
	f3jaob_1 $f wff ps $.
	f3jaob_2 $f wff ch $.
	f3jaob_3 $f wff th $.
	3jaob $p |- ( ( ( ph \/ ch \/ th ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) /\ ( th -> ps ) ) ) $= f3jaob_0 f3jaob_2 f3jaob_3 w3o f3jaob_1 wi f3jaob_0 f3jaob_1 wi f3jaob_2 f3jaob_1 wi f3jaob_3 f3jaob_1 wi w3a f3jaob_0 f3jaob_2 f3jaob_3 w3o f3jaob_1 wi f3jaob_0 f3jaob_1 wi f3jaob_2 f3jaob_1 wi f3jaob_3 f3jaob_1 wi f3jaob_0 f3jaob_0 f3jaob_2 f3jaob_3 w3o f3jaob_1 f3jaob_0 f3jaob_2 f3jaob_3 3mix1 imim1i f3jaob_2 f3jaob_0 f3jaob_2 f3jaob_3 w3o f3jaob_1 f3jaob_2 f3jaob_0 f3jaob_3 3mix2 imim1i f3jaob_3 f3jaob_0 f3jaob_2 f3jaob_3 w3o f3jaob_1 f3jaob_3 f3jaob_0 f3jaob_2 3mix3 imim1i 3jca f3jaob_0 f3jaob_1 f3jaob_2 f3jaob_3 3jao impbii $.
$}
$( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       12-Sep-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3jaoi_0 $f wff ph $.
	f3jaoi_1 $f wff ps $.
	f3jaoi_2 $f wff ch $.
	f3jaoi_3 $f wff th $.
	e3jaoi_0 $e |- ( ph -> ps ) $.
	e3jaoi_1 $e |- ( ch -> ps ) $.
	e3jaoi_2 $e |- ( th -> ps ) $.
	3jaoi $p |- ( ( ph \/ ch \/ th ) -> ps ) $= f3jaoi_0 f3jaoi_1 wi f3jaoi_2 f3jaoi_1 wi f3jaoi_3 f3jaoi_1 wi w3a f3jaoi_0 f3jaoi_2 f3jaoi_3 w3o f3jaoi_1 wi f3jaoi_0 f3jaoi_1 wi f3jaoi_2 f3jaoi_1 wi f3jaoi_3 f3jaoi_1 wi e3jaoi_0 e3jaoi_1 e3jaoi_2 3pm3.2i f3jaoi_0 f3jaoi_1 f3jaoi_2 f3jaoi_3 3jao ax-mp $.
$}
$( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3jaod_0 $f wff ph $.
	f3jaod_1 $f wff ps $.
	f3jaod_2 $f wff ch $.
	f3jaod_3 $f wff th $.
	f3jaod_4 $f wff ta $.
	e3jaod_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3jaod_1 $e |- ( ph -> ( th -> ch ) ) $.
	e3jaod_2 $e |- ( ph -> ( ta -> ch ) ) $.
	3jaod $p |- ( ph -> ( ( ps \/ th \/ ta ) -> ch ) ) $= f3jaod_0 f3jaod_1 f3jaod_2 wi f3jaod_3 f3jaod_2 wi f3jaod_4 f3jaod_2 wi f3jaod_1 f3jaod_3 f3jaod_4 w3o f3jaod_2 wi e3jaod_0 e3jaod_1 e3jaod_2 f3jaod_1 f3jaod_2 f3jaod_3 f3jaod_4 3jao syl3anc $.
$}
$( Disjunction of 3 antecedents (inference).  (Contributed by NM,
       14-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3jaoian_0 $f wff ph $.
	f3jaoian_1 $f wff ps $.
	f3jaoian_2 $f wff ch $.
	f3jaoian_3 $f wff th $.
	f3jaoian_4 $f wff ta $.
	e3jaoian_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	e3jaoian_1 $e |- ( ( th /\ ps ) -> ch ) $.
	e3jaoian_2 $e |- ( ( ta /\ ps ) -> ch ) $.
	3jaoian $p |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch ) $= f3jaoian_0 f3jaoian_3 f3jaoian_4 w3o f3jaoian_1 f3jaoian_2 f3jaoian_0 f3jaoian_1 f3jaoian_2 wi f3jaoian_3 f3jaoian_4 f3jaoian_0 f3jaoian_1 f3jaoian_2 e3jaoian_0 ex f3jaoian_3 f3jaoian_1 f3jaoian_2 e3jaoian_1 ex f3jaoian_4 f3jaoian_1 f3jaoian_2 e3jaoian_2 ex 3jaoi imp $.
$}
$( Disjunction of 3 antecedents (deduction).  (Contributed by NM,
       14-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3jaodan_0 $f wff ph $.
	f3jaodan_1 $f wff ps $.
	f3jaodan_2 $f wff ch $.
	f3jaodan_3 $f wff th $.
	f3jaodan_4 $f wff ta $.
	e3jaodan_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	e3jaodan_1 $e |- ( ( ph /\ th ) -> ch ) $.
	e3jaodan_2 $e |- ( ( ph /\ ta ) -> ch ) $.
	3jaodan $p |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch ) $= f3jaodan_0 f3jaodan_1 f3jaodan_3 f3jaodan_4 w3o f3jaodan_2 f3jaodan_0 f3jaodan_1 f3jaodan_2 f3jaodan_3 f3jaodan_4 f3jaodan_0 f3jaodan_1 f3jaodan_2 e3jaodan_0 ex f3jaodan_0 f3jaodan_3 f3jaodan_2 e3jaodan_1 ex f3jaodan_0 f3jaodan_4 f3jaodan_2 e3jaodan_2 ex 3jaod imp $.
$}
$( Inference conjoining and disjoining the antecedents of three
       implications.  (Contributed by Jeff Hankins, 15-Aug-2009.)  (Proof
       shortened by Andrew Salmon, 13-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	f3jaao_0 $f wff ph $.
	f3jaao_1 $f wff ps $.
	f3jaao_2 $f wff ch $.
	f3jaao_3 $f wff th $.
	f3jaao_4 $f wff ta $.
	f3jaao_5 $f wff et $.
	f3jaao_6 $f wff ze $.
	e3jaao_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3jaao_1 $e |- ( th -> ( ta -> ch ) ) $.
	e3jaao_2 $e |- ( et -> ( ze -> ch ) ) $.
	3jaao $p |- ( ( ph /\ th /\ et ) -> ( ( ps \/ ta \/ ze ) -> ch ) ) $= f3jaao_0 f3jaao_3 f3jaao_5 w3a f3jaao_1 f3jaao_2 f3jaao_4 f3jaao_6 f3jaao_0 f3jaao_3 f3jaao_1 f3jaao_2 wi f3jaao_5 e3jaao_0 3ad2ant1 f3jaao_3 f3jaao_0 f3jaao_4 f3jaao_2 wi f3jaao_5 e3jaao_1 3ad2ant2 f3jaao_5 f3jaao_0 f3jaao_6 f3jaao_2 wi f3jaao_3 e3jaao_2 3ad2ant3 3jaod $.
$}
$( Nested syllogism inference conjoining 3 dissimilar antecedents.
       (Contributed by NM, 1-May-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	fsyl3an9b_0 $f wff ph $.
	fsyl3an9b_1 $f wff ps $.
	fsyl3an9b_2 $f wff ch $.
	fsyl3an9b_3 $f wff th $.
	fsyl3an9b_4 $f wff ta $.
	fsyl3an9b_5 $f wff et $.
	fsyl3an9b_6 $f wff ze $.
	esyl3an9b_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	esyl3an9b_1 $e |- ( th -> ( ch <-> ta ) ) $.
	esyl3an9b_2 $e |- ( et -> ( ta <-> ze ) ) $.
	syl3an9b $p |- ( ( ph /\ th /\ et ) -> ( ps <-> ze ) ) $= fsyl3an9b_0 fsyl3an9b_3 fsyl3an9b_5 fsyl3an9b_1 fsyl3an9b_6 wb fsyl3an9b_0 fsyl3an9b_3 wa fsyl3an9b_1 fsyl3an9b_4 fsyl3an9b_5 fsyl3an9b_6 fsyl3an9b_0 fsyl3an9b_1 fsyl3an9b_2 fsyl3an9b_3 fsyl3an9b_4 esyl3an9b_0 esyl3an9b_1 sylan9bb esyl3an9b_2 sylan9bb 3impa $.
$}
$( Deduction joining 3 equivalences to form equivalence of disjunctions.
       (Contributed by NM, 20-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	f3orbi123d_0 $f wff ph $.
	f3orbi123d_1 $f wff ps $.
	f3orbi123d_2 $f wff ch $.
	f3orbi123d_3 $f wff th $.
	f3orbi123d_4 $f wff ta $.
	f3orbi123d_5 $f wff et $.
	f3orbi123d_6 $f wff ze $.
	e3orbi123d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3orbi123d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	e3orbi123d_2 $e |- ( ph -> ( et <-> ze ) ) $.
	3orbi123d $p |- ( ph -> ( ( ps \/ th \/ et ) <-> ( ch \/ ta \/ ze ) ) ) $= f3orbi123d_0 f3orbi123d_1 f3orbi123d_3 wo f3orbi123d_5 wo f3orbi123d_2 f3orbi123d_4 wo f3orbi123d_6 wo f3orbi123d_1 f3orbi123d_3 f3orbi123d_5 w3o f3orbi123d_2 f3orbi123d_4 f3orbi123d_6 w3o f3orbi123d_0 f3orbi123d_1 f3orbi123d_3 wo f3orbi123d_2 f3orbi123d_4 wo f3orbi123d_5 f3orbi123d_6 f3orbi123d_0 f3orbi123d_1 f3orbi123d_2 f3orbi123d_3 f3orbi123d_4 e3orbi123d_0 e3orbi123d_1 orbi12d e3orbi123d_2 orbi12d f3orbi123d_1 f3orbi123d_3 f3orbi123d_5 df-3or f3orbi123d_2 f3orbi123d_4 f3orbi123d_6 df-3or 3bitr4g $.
$}
$( Deduction joining 3 equivalences to form equivalence of conjunctions.
       (Contributed by NM, 22-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	f3anbi123d_0 $f wff ph $.
	f3anbi123d_1 $f wff ps $.
	f3anbi123d_2 $f wff ch $.
	f3anbi123d_3 $f wff th $.
	f3anbi123d_4 $f wff ta $.
	f3anbi123d_5 $f wff et $.
	f3anbi123d_6 $f wff ze $.
	e3anbi123d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3anbi123d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	e3anbi123d_2 $e |- ( ph -> ( et <-> ze ) ) $.
	3anbi123d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ ze ) ) ) $= f3anbi123d_0 f3anbi123d_1 f3anbi123d_3 wa f3anbi123d_5 wa f3anbi123d_2 f3anbi123d_4 wa f3anbi123d_6 wa f3anbi123d_1 f3anbi123d_3 f3anbi123d_5 w3a f3anbi123d_2 f3anbi123d_4 f3anbi123d_6 w3a f3anbi123d_0 f3anbi123d_1 f3anbi123d_3 wa f3anbi123d_2 f3anbi123d_4 wa f3anbi123d_5 f3anbi123d_6 f3anbi123d_0 f3anbi123d_1 f3anbi123d_2 f3anbi123d_3 f3anbi123d_4 e3anbi123d_0 e3anbi123d_1 anbi12d e3anbi123d_2 anbi12d f3anbi123d_1 f3anbi123d_3 f3anbi123d_5 df-3an f3anbi123d_2 f3anbi123d_4 f3anbi123d_6 df-3an 3bitr4g $.
$}
$( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3anbi12d_0 $f wff ph $.
	f3anbi12d_1 $f wff ps $.
	f3anbi12d_2 $f wff ch $.
	f3anbi12d_3 $f wff th $.
	f3anbi12d_4 $f wff ta $.
	f3anbi12d_5 $f wff et $.
	e3anbi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3anbi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	3anbi12d $p |- ( ph -> ( ( ps /\ th /\ et ) <-> ( ch /\ ta /\ et ) ) ) $= f3anbi12d_0 f3anbi12d_1 f3anbi12d_2 f3anbi12d_3 f3anbi12d_4 f3anbi12d_5 f3anbi12d_5 e3anbi12d_0 e3anbi12d_1 f3anbi12d_0 f3anbi12d_5 biidd 3anbi123d $.
$}
$( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3anbi13d_0 $f wff ph $.
	f3anbi13d_1 $f wff ps $.
	f3anbi13d_2 $f wff ch $.
	f3anbi13d_3 $f wff th $.
	f3anbi13d_4 $f wff ta $.
	f3anbi13d_5 $f wff et $.
	e3anbi13d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3anbi13d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	3anbi13d $p |- ( ph -> ( ( ps /\ et /\ th ) <-> ( ch /\ et /\ ta ) ) ) $= f3anbi13d_0 f3anbi13d_1 f3anbi13d_2 f3anbi13d_5 f3anbi13d_5 f3anbi13d_3 f3anbi13d_4 e3anbi13d_0 f3anbi13d_0 f3anbi13d_5 biidd e3anbi13d_1 3anbi123d $.
$}
$( Deduction conjoining and adding a conjunct to equivalences.
       (Contributed by NM, 8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3anbi23d_0 $f wff ph $.
	f3anbi23d_1 $f wff ps $.
	f3anbi23d_2 $f wff ch $.
	f3anbi23d_3 $f wff th $.
	f3anbi23d_4 $f wff ta $.
	f3anbi23d_5 $f wff et $.
	e3anbi23d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	e3anbi23d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	3anbi23d $p |- ( ph -> ( ( et /\ ps /\ th ) <-> ( et /\ ch /\ ta ) ) ) $= f3anbi23d_0 f3anbi23d_5 f3anbi23d_5 f3anbi23d_1 f3anbi23d_2 f3anbi23d_3 f3anbi23d_4 f3anbi23d_0 f3anbi23d_5 biidd e3anbi23d_0 e3anbi23d_1 3anbi123d $.
$}
$( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anbi1d_0 $f wff ph $.
	f3anbi1d_1 $f wff ps $.
	f3anbi1d_2 $f wff ch $.
	f3anbi1d_3 $f wff th $.
	f3anbi1d_4 $f wff ta $.
	e3anbi1d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	3anbi1d $p |- ( ph -> ( ( ps /\ th /\ ta ) <-> ( ch /\ th /\ ta ) ) ) $= f3anbi1d_0 f3anbi1d_1 f3anbi1d_2 f3anbi1d_3 f3anbi1d_3 f3anbi1d_4 e3anbi1d_0 f3anbi1d_0 f3anbi1d_3 biidd 3anbi12d $.
$}
$( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anbi2d_0 $f wff ph $.
	f3anbi2d_1 $f wff ps $.
	f3anbi2d_2 $f wff ch $.
	f3anbi2d_3 $f wff th $.
	f3anbi2d_4 $f wff ta $.
	e3anbi2d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	3anbi2d $p |- ( ph -> ( ( th /\ ps /\ ta ) <-> ( th /\ ch /\ ta ) ) ) $= f3anbi2d_0 f3anbi2d_3 f3anbi2d_3 f3anbi2d_1 f3anbi2d_2 f3anbi2d_4 f3anbi2d_0 f3anbi2d_3 biidd e3anbi2d_0 3anbi12d $.
$}
$( Deduction adding conjuncts to an equivalence.  (Contributed by NM,
       8-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anbi3d_0 $f wff ph $.
	f3anbi3d_1 $f wff ps $.
	f3anbi3d_2 $f wff ch $.
	f3anbi3d_3 $f wff th $.
	f3anbi3d_4 $f wff ta $.
	e3anbi3d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	3anbi3d $p |- ( ph -> ( ( th /\ ta /\ ps ) <-> ( th /\ ta /\ ch ) ) ) $= f3anbi3d_0 f3anbi3d_3 f3anbi3d_3 f3anbi3d_1 f3anbi3d_2 f3anbi3d_4 f3anbi3d_0 f3anbi3d_3 biidd e3anbi3d_0 3anbi13d $.
$}
$( Deduction joining 3 implications to form implication of conjunctions.
       (Contributed by NM, 24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	f3anim123d_0 $f wff ph $.
	f3anim123d_1 $f wff ps $.
	f3anim123d_2 $f wff ch $.
	f3anim123d_3 $f wff th $.
	f3anim123d_4 $f wff ta $.
	f3anim123d_5 $f wff et $.
	f3anim123d_6 $f wff ze $.
	e3anim123d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3anim123d_1 $e |- ( ph -> ( th -> ta ) ) $.
	e3anim123d_2 $e |- ( ph -> ( et -> ze ) ) $.
	3anim123d $p |- ( ph -> ( ( ps /\ th /\ et ) -> ( ch /\ ta /\ ze ) ) ) $= f3anim123d_0 f3anim123d_1 f3anim123d_3 wa f3anim123d_5 wa f3anim123d_2 f3anim123d_4 wa f3anim123d_6 wa f3anim123d_1 f3anim123d_3 f3anim123d_5 w3a f3anim123d_2 f3anim123d_4 f3anim123d_6 w3a f3anim123d_0 f3anim123d_1 f3anim123d_3 wa f3anim123d_2 f3anim123d_4 wa f3anim123d_5 f3anim123d_6 f3anim123d_0 f3anim123d_1 f3anim123d_2 f3anim123d_3 f3anim123d_4 e3anim123d_0 e3anim123d_1 anim12d e3anim123d_2 anim12d f3anim123d_1 f3anim123d_3 f3anim123d_5 df-3an f3anim123d_2 f3anim123d_4 f3anim123d_6 df-3an 3imtr4g $.
$}
$( Deduction joining 3 implications to form implication of disjunctions.
       (Contributed by NM, 4-Apr-1997.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	$v ze $.
	f3orim123d_0 $f wff ph $.
	f3orim123d_1 $f wff ps $.
	f3orim123d_2 $f wff ch $.
	f3orim123d_3 $f wff th $.
	f3orim123d_4 $f wff ta $.
	f3orim123d_5 $f wff et $.
	f3orim123d_6 $f wff ze $.
	e3orim123d_0 $e |- ( ph -> ( ps -> ch ) ) $.
	e3orim123d_1 $e |- ( ph -> ( th -> ta ) ) $.
	e3orim123d_2 $e |- ( ph -> ( et -> ze ) ) $.
	3orim123d $p |- ( ph -> ( ( ps \/ th \/ et ) -> ( ch \/ ta \/ ze ) ) ) $= f3orim123d_0 f3orim123d_1 f3orim123d_3 wo f3orim123d_5 wo f3orim123d_2 f3orim123d_4 wo f3orim123d_6 wo f3orim123d_1 f3orim123d_3 f3orim123d_5 w3o f3orim123d_2 f3orim123d_4 f3orim123d_6 w3o f3orim123d_0 f3orim123d_1 f3orim123d_3 wo f3orim123d_2 f3orim123d_4 wo f3orim123d_5 f3orim123d_6 f3orim123d_0 f3orim123d_1 f3orim123d_2 f3orim123d_3 f3orim123d_4 e3orim123d_0 e3orim123d_1 orim12d e3orim123d_2 orim12d f3orim123d_1 f3orim123d_3 f3orim123d_5 df-3or f3orim123d_2 f3orim123d_4 f3orim123d_6 df-3or 3imtr4g $.
$}
$( Rearrangement of 6 conjuncts.  (Contributed by NM, 13-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fan6_0 $f wff ph $.
	fan6_1 $f wff ps $.
	fan6_2 $f wff ch $.
	fan6_3 $f wff th $.
	fan6_4 $f wff ta $.
	fan6_5 $f wff et $.
	an6 $p |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta /\ et ) ) <-> ( ( ph /\ th ) /\ ( ps /\ ta ) /\ ( ch /\ et ) ) ) $= fan6_0 fan6_1 wa fan6_2 wa fan6_3 fan6_4 wa fan6_5 wa wa fan6_0 fan6_3 wa fan6_1 fan6_4 wa wa fan6_2 fan6_5 wa wa fan6_0 fan6_1 fan6_2 w3a fan6_3 fan6_4 fan6_5 w3a wa fan6_0 fan6_3 wa fan6_1 fan6_4 wa fan6_2 fan6_5 wa w3a fan6_0 fan6_1 wa fan6_2 wa fan6_3 fan6_4 wa fan6_5 wa wa fan6_0 fan6_1 wa fan6_3 fan6_4 wa wa fan6_2 fan6_5 wa wa fan6_0 fan6_3 wa fan6_1 fan6_4 wa wa fan6_2 fan6_5 wa wa fan6_0 fan6_1 wa fan6_2 fan6_3 fan6_4 wa fan6_5 an4 fan6_0 fan6_1 wa fan6_3 fan6_4 wa wa fan6_0 fan6_3 wa fan6_1 fan6_4 wa wa fan6_2 fan6_5 wa fan6_0 fan6_1 fan6_3 fan6_4 an4 anbi1i bitri fan6_0 fan6_1 fan6_2 w3a fan6_0 fan6_1 wa fan6_2 wa fan6_3 fan6_4 fan6_5 w3a fan6_3 fan6_4 wa fan6_5 wa fan6_0 fan6_1 fan6_2 df-3an fan6_3 fan6_4 fan6_5 df-3an anbi12i fan6_0 fan6_3 wa fan6_1 fan6_4 wa fan6_2 fan6_5 wa df-3an 3bitr4i $.
$}
$( Analog of ~ an4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3an6_0 $f wff ph $.
	f3an6_1 $f wff ps $.
	f3an6_2 $f wff ch $.
	f3an6_3 $f wff th $.
	f3an6_4 $f wff ta $.
	f3an6_5 $f wff et $.
	3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <-> ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $= f3an6_0 f3an6_2 f3an6_4 w3a f3an6_1 f3an6_3 f3an6_5 w3a wa f3an6_0 f3an6_1 wa f3an6_2 f3an6_3 wa f3an6_4 f3an6_5 wa w3a f3an6_0 f3an6_2 f3an6_4 f3an6_1 f3an6_3 f3an6_5 an6 bicomi $.
$}
$( Analog of ~ or4 for triple conjunction.  (Contributed by Scott Fenton,
     16-Mar-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	f3or6_0 $f wff ph $.
	f3or6_1 $f wff ps $.
	f3or6_2 $f wff ch $.
	f3or6_3 $f wff th $.
	f3or6_4 $f wff ta $.
	f3or6_5 $f wff et $.
	3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <-> ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $= f3or6_0 f3or6_1 wo f3or6_2 f3or6_3 wo wo f3or6_4 f3or6_5 wo wo f3or6_0 f3or6_2 wo f3or6_4 wo f3or6_1 f3or6_3 wo f3or6_5 wo wo f3or6_0 f3or6_1 wo f3or6_2 f3or6_3 wo f3or6_4 f3or6_5 wo w3o f3or6_0 f3or6_2 f3or6_4 w3o f3or6_1 f3or6_3 f3or6_5 w3o wo f3or6_0 f3or6_2 wo f3or6_4 wo f3or6_1 f3or6_3 wo f3or6_5 wo wo f3or6_0 f3or6_2 wo f3or6_1 f3or6_3 wo wo f3or6_4 f3or6_5 wo wo f3or6_0 f3or6_1 wo f3or6_2 f3or6_3 wo wo f3or6_4 f3or6_5 wo wo f3or6_0 f3or6_2 wo f3or6_4 f3or6_1 f3or6_3 wo f3or6_5 or4 f3or6_0 f3or6_2 wo f3or6_1 f3or6_3 wo wo f3or6_0 f3or6_1 wo f3or6_2 f3or6_3 wo wo f3or6_4 f3or6_5 wo f3or6_0 f3or6_2 f3or6_1 f3or6_3 or4 orbi1i bitr2i f3or6_0 f3or6_1 wo f3or6_2 f3or6_3 wo f3or6_4 f3or6_5 wo df-3or f3or6_0 f3or6_2 f3or6_4 w3o f3or6_0 f3or6_2 wo f3or6_4 wo f3or6_1 f3or6_3 f3or6_5 w3o f3or6_1 f3or6_3 wo f3or6_5 wo f3or6_0 f3or6_2 f3or6_4 df-3or f3or6_1 f3or6_3 f3or6_5 df-3or orbi12i 3bitr4i $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an1_0 $f wff ph $.
	fmp3an1_1 $f wff ps $.
	fmp3an1_2 $f wff ch $.
	fmp3an1_3 $f wff th $.
	emp3an1_0 $e |- ph $.
	emp3an1_1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an1 $p |- ( ( ps /\ ch ) -> th ) $= fmp3an1_0 fmp3an1_1 fmp3an1_2 wa fmp3an1_3 emp3an1_0 fmp3an1_0 fmp3an1_1 fmp3an1_2 fmp3an1_3 emp3an1_1 3expb mpan $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an2_0 $f wff ph $.
	fmp3an2_1 $f wff ps $.
	fmp3an2_2 $f wff ch $.
	fmp3an2_3 $f wff th $.
	emp3an2_0 $e |- ps $.
	emp3an2_1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an2 $p |- ( ( ph /\ ch ) -> th ) $= fmp3an2_0 fmp3an2_1 fmp3an2_2 fmp3an2_3 emp3an2_0 fmp3an2_0 fmp3an2_1 fmp3an2_2 fmp3an2_3 emp3an2_1 3expa mpanl2 $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       21-Nov-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an3_0 $f wff ph $.
	fmp3an3_1 $f wff ps $.
	fmp3an3_2 $f wff ch $.
	fmp3an3_3 $f wff th $.
	emp3an3_0 $e |- ch $.
	emp3an3_1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an3 $p |- ( ( ph /\ ps ) -> th ) $= fmp3an3_0 fmp3an3_1 wa fmp3an3_2 fmp3an3_3 emp3an3_0 fmp3an3_0 fmp3an3_1 fmp3an3_2 fmp3an3_3 emp3an3_1 3expia mpi $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       13-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an12_0 $f wff ph $.
	fmp3an12_1 $f wff ps $.
	fmp3an12_2 $f wff ch $.
	fmp3an12_3 $f wff th $.
	emp3an12_0 $e |- ph $.
	emp3an12_1 $e |- ps $.
	emp3an12_2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an12 $p |- ( ch -> th ) $= fmp3an12_1 fmp3an12_2 fmp3an12_3 emp3an12_1 fmp3an12_0 fmp3an12_1 fmp3an12_2 fmp3an12_3 emp3an12_0 emp3an12_2 mp3an1 mpan $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an13_0 $f wff ph $.
	fmp3an13_1 $f wff ps $.
	fmp3an13_2 $f wff ch $.
	fmp3an13_3 $f wff th $.
	emp3an13_0 $e |- ph $.
	emp3an13_1 $e |- ch $.
	emp3an13_2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an13 $p |- ( ps -> th ) $= fmp3an13_0 fmp3an13_1 fmp3an13_3 emp3an13_0 fmp3an13_0 fmp3an13_1 fmp3an13_2 fmp3an13_3 emp3an13_1 emp3an13_2 mp3an3 mpan $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       14-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an23_0 $f wff ph $.
	fmp3an23_1 $f wff ps $.
	fmp3an23_2 $f wff ch $.
	fmp3an23_3 $f wff th $.
	emp3an23_0 $e |- ps $.
	emp3an23_1 $e |- ch $.
	emp3an23_2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an23 $p |- ( ph -> th ) $= fmp3an23_0 fmp3an23_1 fmp3an23_3 emp3an23_0 fmp3an23_0 fmp3an23_1 fmp3an23_2 fmp3an23_3 emp3an23_1 emp3an23_2 mp3an3 mpan2 $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 5-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3an1i_0 $f wff ph $.
	fmp3an1i_1 $f wff ps $.
	fmp3an1i_2 $f wff ch $.
	fmp3an1i_3 $f wff th $.
	fmp3an1i_4 $f wff ta $.
	emp3an1i_0 $e |- ps $.
	emp3an1i_1 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	mp3an1i $p |- ( ph -> ( ( ch /\ th ) -> ta ) ) $= fmp3an1i_2 fmp3an1i_3 wa fmp3an1i_0 fmp3an1i_4 fmp3an1i_1 fmp3an1i_2 fmp3an1i_3 fmp3an1i_0 fmp3an1i_4 wi emp3an1i_0 fmp3an1i_0 fmp3an1i_1 fmp3an1i_2 fmp3an1i_3 w3a fmp3an1i_4 emp3an1i_1 com12 mp3an1 com12 $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anl1_0 $f wff ph $.
	fmp3anl1_1 $f wff ps $.
	fmp3anl1_2 $f wff ch $.
	fmp3anl1_3 $f wff th $.
	fmp3anl1_4 $f wff ta $.
	emp3anl1_0 $e |- ph $.
	emp3anl1_1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	mp3anl1 $p |- ( ( ( ps /\ ch ) /\ th ) -> ta ) $= fmp3anl1_1 fmp3anl1_2 wa fmp3anl1_3 fmp3anl1_4 fmp3anl1_0 fmp3anl1_1 fmp3anl1_2 fmp3anl1_3 fmp3anl1_4 wi emp3anl1_0 fmp3anl1_0 fmp3anl1_1 fmp3anl1_2 w3a fmp3anl1_3 fmp3anl1_4 emp3anl1_1 ex mp3an1 imp $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anl2_0 $f wff ph $.
	fmp3anl2_1 $f wff ps $.
	fmp3anl2_2 $f wff ch $.
	fmp3anl2_3 $f wff th $.
	fmp3anl2_4 $f wff ta $.
	emp3anl2_0 $e |- ps $.
	emp3anl2_1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	mp3anl2 $p |- ( ( ( ph /\ ch ) /\ th ) -> ta ) $= fmp3anl2_0 fmp3anl2_2 wa fmp3anl2_3 fmp3anl2_4 fmp3anl2_0 fmp3anl2_1 fmp3anl2_2 fmp3anl2_3 fmp3anl2_4 wi emp3anl2_0 fmp3anl2_0 fmp3anl2_1 fmp3anl2_2 w3a fmp3anl2_3 fmp3anl2_4 emp3anl2_1 ex mp3an2 imp $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       24-Feb-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anl3_0 $f wff ph $.
	fmp3anl3_1 $f wff ps $.
	fmp3anl3_2 $f wff ch $.
	fmp3anl3_3 $f wff th $.
	fmp3anl3_4 $f wff ta $.
	emp3anl3_0 $e |- ch $.
	emp3anl3_1 $e |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $.
	mp3anl3 $p |- ( ( ( ph /\ ps ) /\ th ) -> ta ) $= fmp3anl3_0 fmp3anl3_1 wa fmp3anl3_3 fmp3anl3_4 fmp3anl3_0 fmp3anl3_1 fmp3anl3_2 fmp3anl3_3 fmp3anl3_4 wi emp3anl3_0 fmp3anl3_0 fmp3anl3_1 fmp3anl3_2 w3a fmp3anl3_3 fmp3anl3_4 emp3anl3_1 ex mp3an3 imp $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 4-Nov-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anr1_0 $f wff ph $.
	fmp3anr1_1 $f wff ps $.
	fmp3anr1_2 $f wff ch $.
	fmp3anr1_3 $f wff th $.
	fmp3anr1_4 $f wff ta $.
	emp3anr1_0 $e |- ps $.
	emp3anr1_1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	mp3anr1 $p |- ( ( ph /\ ( ch /\ th ) ) -> ta ) $= fmp3anr1_2 fmp3anr1_3 wa fmp3anr1_0 fmp3anr1_4 fmp3anr1_1 fmp3anr1_2 fmp3anr1_3 fmp3anr1_0 fmp3anr1_4 emp3anr1_0 fmp3anr1_0 fmp3anr1_1 fmp3anr1_2 fmp3anr1_3 w3a fmp3anr1_4 emp3anr1_1 ancoms mp3anl1 ancoms $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       24-Nov-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anr2_0 $f wff ph $.
	fmp3anr2_1 $f wff ps $.
	fmp3anr2_2 $f wff ch $.
	fmp3anr2_3 $f wff th $.
	fmp3anr2_4 $f wff ta $.
	emp3anr2_0 $e |- ch $.
	emp3anr2_1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	mp3anr2 $p |- ( ( ph /\ ( ps /\ th ) ) -> ta ) $= fmp3anr2_1 fmp3anr2_3 wa fmp3anr2_0 fmp3anr2_4 fmp3anr2_1 fmp3anr2_2 fmp3anr2_3 fmp3anr2_0 fmp3anr2_4 emp3anr2_0 fmp3anr2_0 fmp3anr2_1 fmp3anr2_2 fmp3anr2_3 w3a fmp3anr2_4 emp3anr2_1 ancoms mp3anl2 ancoms $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       19-Oct-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3anr3_0 $f wff ph $.
	fmp3anr3_1 $f wff ps $.
	fmp3anr3_2 $f wff ch $.
	fmp3anr3_3 $f wff th $.
	fmp3anr3_4 $f wff ta $.
	emp3anr3_0 $e |- th $.
	emp3anr3_1 $e |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $.
	mp3anr3 $p |- ( ( ph /\ ( ps /\ ch ) ) -> ta ) $= fmp3anr3_1 fmp3anr3_2 wa fmp3anr3_0 fmp3anr3_4 fmp3anr3_1 fmp3anr3_2 fmp3anr3_3 fmp3anr3_0 fmp3anr3_4 emp3anr3_0 fmp3anr3_0 fmp3anr3_1 fmp3anr3_2 fmp3anr3_3 w3a fmp3anr3_4 emp3anr3_1 ancoms mp3anl3 ancoms $.
$}
$( An inference based on modus ponens.  (Contributed by NM,
       14-May-1999.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmp3an_0 $f wff ph $.
	fmp3an_1 $f wff ps $.
	fmp3an_2 $f wff ch $.
	fmp3an_3 $f wff th $.
	emp3an_0 $e |- ph $.
	emp3an_1 $e |- ps $.
	emp3an_2 $e |- ch $.
	emp3an_3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mp3an $p |- th $= fmp3an_1 fmp3an_2 fmp3an_3 emp3an_1 emp3an_2 fmp3an_0 fmp3an_1 fmp3an_2 fmp3an_3 emp3an_0 emp3an_3 mp3an1 mp2an $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 8-Nov-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpd3an3_0 $f wff ph $.
	fmpd3an3_1 $f wff ps $.
	fmpd3an3_2 $f wff ch $.
	fmpd3an3_3 $f wff th $.
	empd3an3_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	empd3an3_1 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mpd3an3 $p |- ( ( ph /\ ps ) -> th ) $= fmpd3an3_0 fmpd3an3_1 wa fmpd3an3_2 fmpd3an3_3 empd3an3_0 fmpd3an3_0 fmpd3an3_1 fmpd3an3_2 fmpd3an3_3 empd3an3_1 3expa mpdan $.
$}
$( An inference based on modus ponens.  (Contributed by NM, 4-Dec-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fmpd3an23_0 $f wff ph $.
	fmpd3an23_1 $f wff ps $.
	fmpd3an23_2 $f wff ch $.
	fmpd3an23_3 $f wff th $.
	empd3an23_0 $e |- ( ph -> ps ) $.
	empd3an23_1 $e |- ( ph -> ch ) $.
	empd3an23_2 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	mpd3an23 $p |- ( ph -> th ) $= fmpd3an23_0 fmpd3an23_0 fmpd3an23_1 fmpd3an23_2 fmpd3an23_3 fmpd3an23_0 id empd3an23_0 empd3an23_1 empd3an23_2 syl3anc $.
$}
$( A deduction based on modus ponens.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fmp3and_0 $f wff ph $.
	fmp3and_1 $f wff ps $.
	fmp3and_2 $f wff ch $.
	fmp3and_3 $f wff th $.
	fmp3and_4 $f wff ta $.
	emp3and_0 $e |- ( ph -> ps ) $.
	emp3and_1 $e |- ( ph -> ch ) $.
	emp3and_2 $e |- ( ph -> th ) $.
	emp3and_3 $e |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ) $.
	mp3and $p |- ( ph -> ta ) $= fmp3and_0 fmp3and_1 fmp3and_2 fmp3and_3 w3a fmp3and_4 fmp3and_0 fmp3and_1 fmp3and_2 fmp3and_3 emp3and_0 emp3and_1 emp3and_2 3jca emp3and_3 mpd $.
$}
$( Infer implication from a logical equivalence.  Similar to ~ biimpa .
       (Contributed by NM, 4-Sep-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fbiimp3a_0 $f wff ph $.
	fbiimp3a_1 $f wff ps $.
	fbiimp3a_2 $f wff ch $.
	fbiimp3a_3 $f wff th $.
	ebiimp3a_0 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	biimp3a $p |- ( ( ph /\ ps /\ ch ) -> th ) $= fbiimp3a_0 fbiimp3a_1 fbiimp3a_2 fbiimp3a_3 fbiimp3a_0 fbiimp3a_1 wa fbiimp3a_2 fbiimp3a_3 ebiimp3a_0 biimpa 3impa $.
$}
$( Infer implication from a logical equivalence.  Similar to ~ biimpar .
       (Contributed by NM, 2-Jan-2009.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fbiimp3ar_0 $f wff ph $.
	fbiimp3ar_1 $f wff ps $.
	fbiimp3ar_2 $f wff ch $.
	fbiimp3ar_3 $f wff th $.
	ebiimp3ar_0 $e |- ( ( ph /\ ps ) -> ( ch <-> th ) ) $.
	biimp3ar $p |- ( ( ph /\ ps /\ th ) -> ch ) $= fbiimp3ar_0 fbiimp3ar_1 fbiimp3ar_3 fbiimp3ar_2 fbiimp3ar_0 fbiimp3ar_1 fbiimp3ar_2 fbiimp3ar_3 ebiimp3ar_0 exbiri 3imp $.
$}
$( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 18-Apr-2007.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anandis_0 $f wff ph $.
	f3anandis_1 $f wff ps $.
	f3anandis_2 $f wff ch $.
	f3anandis_3 $f wff th $.
	f3anandis_4 $f wff ta $.
	e3anandis_0 $e |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) /\ ( ph /\ th ) ) -> ta ) $.
	3anandis $p |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ) $= f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 w3a wa f3anandis_0 f3anandis_1 f3anandis_0 f3anandis_2 f3anandis_0 f3anandis_3 f3anandis_4 f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 w3a simpl f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 simpr1 f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 w3a simpl f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 simpr2 f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 w3a simpl f3anandis_0 f3anandis_1 f3anandis_2 f3anandis_3 simpr3 e3anandis_0 syl222anc $.
$}
$( Inference that undistributes a triple conjunction in the antecedent.
       (Contributed by NM, 25-Jul-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	f3anandirs_0 $f wff ph $.
	f3anandirs_1 $f wff ps $.
	f3anandirs_2 $f wff ch $.
	f3anandirs_3 $f wff th $.
	f3anandirs_4 $f wff ta $.
	e3anandirs_0 $e |- ( ( ( ph /\ th ) /\ ( ps /\ th ) /\ ( ch /\ th ) ) -> ta ) $.
	3anandirs $p |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ) $= f3anandirs_0 f3anandirs_1 f3anandirs_2 w3a f3anandirs_3 wa f3anandirs_0 f3anandirs_3 f3anandirs_1 f3anandirs_3 f3anandirs_2 f3anandirs_3 f3anandirs_4 f3anandirs_0 f3anandirs_1 f3anandirs_2 f3anandirs_3 simpl1 f3anandirs_0 f3anandirs_1 f3anandirs_2 w3a f3anandirs_3 simpr f3anandirs_0 f3anandirs_1 f3anandirs_2 f3anandirs_3 simpl2 f3anandirs_0 f3anandirs_1 f3anandirs_2 w3a f3anandirs_3 simpr f3anandirs_0 f3anandirs_1 f3anandirs_2 f3anandirs_3 simpl3 f3anandirs_0 f3anandirs_1 f3anandirs_2 w3a f3anandirs_3 simpr e3anandirs_0 syl222anc $.
$}
$( Deduction for elimination by cases.  (Contributed by NM,
       22-Apr-1994.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fecase23d_0 $f wff ph $.
	fecase23d_1 $f wff ps $.
	fecase23d_2 $f wff ch $.
	fecase23d_3 $f wff th $.
	eecase23d_0 $e |- ( ph -> -. ch ) $.
	eecase23d_1 $e |- ( ph -> -. th ) $.
	eecase23d_2 $e |- ( ph -> ( ps \/ ch \/ th ) ) $.
	ecase23d $p |- ( ph -> ps ) $= fecase23d_0 fecase23d_1 fecase23d_2 fecase23d_3 wo fecase23d_0 fecase23d_2 wn fecase23d_3 wn fecase23d_2 fecase23d_3 wo wn eecase23d_0 eecase23d_1 fecase23d_2 fecase23d_3 ioran sylanbrc fecase23d_0 fecase23d_1 fecase23d_2 fecase23d_3 wo fecase23d_0 fecase23d_1 fecase23d_2 fecase23d_3 w3o fecase23d_1 fecase23d_2 fecase23d_3 wo wo eecase23d_2 fecase23d_1 fecase23d_2 fecase23d_3 3orass sylib ord mt3d $.
$}
$( Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	f3ecase_0 $f wff ph $.
	f3ecase_1 $f wff ps $.
	f3ecase_2 $f wff ch $.
	f3ecase_3 $f wff th $.
	e3ecase_0 $e |- ( -. ph -> th ) $.
	e3ecase_1 $e |- ( -. ps -> th ) $.
	e3ecase_2 $e |- ( -. ch -> th ) $.
	e3ecase_3 $e |- ( ( ph /\ ps /\ ch ) -> th ) $.
	3ecase $p |- th $= f3ecase_1 f3ecase_2 f3ecase_3 f3ecase_0 f3ecase_1 f3ecase_2 f3ecase_3 wi wi f3ecase_0 f3ecase_1 f3ecase_2 f3ecase_3 e3ecase_3 3exp f3ecase_0 wn f3ecase_2 f3ecase_3 wi f3ecase_1 f3ecase_0 wn f3ecase_3 f3ecase_2 e3ecase_0 a1d a1d pm2.61i e3ecase_1 e3ecase_2 pm2.61nii $.
$}

