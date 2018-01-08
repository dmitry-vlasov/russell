$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Founded_and_well-ordering_relations.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Introduce new constant symbols. $)
$c Ord  $.
$( Ordinal predicate $)
$c On  $.
$( The class of ordinal numbers $)
$c Lim  $.
$( Limit ordinal predicate $)
$c suc  $.
$( Successor function (read:  'successor of') $)
$( Extend the definition of a wff to include the ordinal predicate. $)
${
	fword_0 $f class A $.
	word $a wff Ord A $.
$}
$( Extend the definition of a class to include the class of all ordinal
     numbers.  (The 0 in the name prevents creating a file called con.html,
     which causes problems in Windows.) $)
${
	con0 $a class On $.
$}
$( Extend the definition of a wff to include the limit ordinal predicate. $)
${
	fwlim_0 $f class A $.
	wlim $a wff Lim A $.
$}
$( Extend class notation to include the successor function. $)
${
	fcsuc_0 $f class A $.
	csuc $a class suc A $.
$}
$( Define the ordinal predicate, which is true for a class that is transitive
     and is well-ordered by the epsilon relation.  Variant of definition of
     [BellMachover] p. 468.  (Contributed by NM, 17-Sep-1993.) $)
${
	fdf-ord_0 $f class A $.
	df-ord $a |- ( Ord A <-> ( Tr A /\ _E We A ) ) $.
$}
$( Define the class of all ordinal numbers.  Definition 7.11 of
     [TakeutiZaring] p. 38.  (Contributed by NM, 5-Jun-1994.) $)
${
	fdf-on_0 $f set x $.
	df-on $a |- On = { x | Ord x } $.
$}
$( Define the limit ordinal predicate, which is true for a non-empty ordinal
     that is not a successor (i.e. that is the union of itself).  Our
     definition combines the definition of Lim of [BellMachover] p. 471 and
     Exercise 1 of [TakeutiZaring] p. 42.  See ~ dflim2 , ~ dflim3 , and dflim4
     for alternate definitions.  (Contributed by NM, 22-Apr-1994.) $)
${
	fdf-lim_0 $f class A $.
	df-lim $a |- ( Lim A <-> ( Ord A /\ A =/= (/) /\ A = U. A ) ) $.
$}
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
${
	fdf-suc_0 $f class A $.
	df-suc $a |- suc A = ( A u. { A } ) $.
$}
$( Equality theorem for the ordinal predicate.  (Contributed by NM,
     17-Sep-1993.) $)
${
	fordeq_0 $f class A $.
	fordeq_1 $f class B $.
	ordeq $p |- ( A = B -> ( Ord A <-> Ord B ) ) $= fordeq_0 fordeq_1 wceq fordeq_0 wtr fordeq_0 cep wwe wa fordeq_1 wtr fordeq_1 cep wwe wa fordeq_0 word fordeq_1 word fordeq_0 fordeq_1 wceq fordeq_0 wtr fordeq_1 wtr fordeq_0 cep wwe fordeq_1 cep wwe fordeq_0 fordeq_1 treq fordeq_0 fordeq_1 cep weeq2 anbi12d fordeq_0 df-ord fordeq_1 df-ord 3bitr4g $.
$}
$( An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)
${
	$d x A $.
	ielong_0 $f set x $.
	felong_0 $f class A $.
	felong_1 $f class V $.
	elong $p |- ( A e. V -> ( A e. On <-> Ord A ) ) $= ielong_0 cv word felong_0 word ielong_0 felong_0 con0 felong_1 ielong_0 cv felong_0 ordeq ielong_0 df-on elab2g $.
$}
$( An ordinal number is an ordinal set.  (Contributed by NM,
       5-Jun-1994.) $)
${
	felon_0 $f class A $.
	eelon_0 $e |- A e. _V $.
	elon $p |- ( A e. On <-> Ord A ) $= felon_0 cvv wcel felon_0 con0 wcel felon_0 word wb eelon_0 felon_0 cvv elong ax-mp $.
$}
$( An ordinal number has the ordinal property.  (Contributed by NM,
     5-Jun-1994.) $)
${
	feloni_0 $f class A $.
	eloni $p |- ( A e. On -> Ord A ) $= feloni_0 con0 wcel feloni_0 word feloni_0 con0 elong ibi $.
$}
$( An ordinal number is an ordinal set.  (Contributed by NM, 8-Feb-2004.) $)
${
	felon2_0 $f class A $.
	elon2 $p |- ( A e. On <-> ( Ord A /\ A e. _V ) ) $= felon2_0 con0 wcel felon2_0 word felon2_0 cvv wcel wa felon2_0 con0 wcel felon2_0 word felon2_0 cvv wcel felon2_0 eloni felon2_0 con0 elex jca felon2_0 cvv wcel felon2_0 con0 wcel felon2_0 word felon2_0 cvv elong biimparc impbii $.
$}
$( Equality theorem for the limit predicate.  (Contributed by NM,
     22-Apr-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	flimeq_0 $f class A $.
	flimeq_1 $f class B $.
	limeq $p |- ( A = B -> ( Lim A <-> Lim B ) ) $= flimeq_0 flimeq_1 wceq flimeq_0 word flimeq_0 c0 wne flimeq_0 flimeq_0 cuni wceq w3a flimeq_1 word flimeq_1 c0 wne flimeq_1 flimeq_1 cuni wceq w3a flimeq_0 wlim flimeq_1 wlim flimeq_0 flimeq_1 wceq flimeq_0 word flimeq_1 word flimeq_0 c0 wne flimeq_1 c0 wne flimeq_0 flimeq_0 cuni wceq flimeq_1 flimeq_1 cuni wceq flimeq_0 flimeq_1 ordeq flimeq_0 flimeq_1 c0 neeq1 flimeq_0 flimeq_1 wceq flimeq_0 flimeq_1 flimeq_0 cuni flimeq_1 cuni flimeq_0 flimeq_1 wceq id flimeq_0 flimeq_1 unieq eqeq12d 3anbi123d flimeq_0 df-lim flimeq_1 df-lim 3bitr4g $.
$}
$( Epsilon well-orders every ordinal.  Proposition 7.4 of [TakeutiZaring]
     p. 36.  (Contributed by NM, 3-Apr-1994.) $)
${
	fordwe_0 $f class A $.
	ordwe $p |- ( Ord A -> _E We A ) $= fordwe_0 word fordwe_0 wtr fordwe_0 cep wwe fordwe_0 df-ord simprbi $.
$}
$( An ordinal class is transitive.  (Contributed by NM, 3-Apr-1994.) $)
${
	fordtr_0 $f class A $.
	ordtr $p |- ( Ord A -> Tr A ) $= fordtr_0 word fordtr_0 wtr fordtr_0 cep wwe fordtr_0 df-ord simplbi $.
$}
$( Epsilon is well-founded on an ordinal class.  (Contributed by NM,
     22-Apr-1994.) $)
${
	fordfr_0 $f class A $.
	ordfr $p |- ( Ord A -> _E Fr A ) $= fordfr_0 word fordfr_0 cep wwe fordfr_0 cep wfr fordfr_0 ordwe fordfr_0 cep wefr syl $.
$}
$( An element of an ordinal class is a subset of it.  (Contributed by NM,
     30-May-1994.) $)
${
	fordelss_0 $f class A $.
	fordelss_1 $f class B $.
	ordelss $p |- ( ( Ord A /\ B e. A ) -> B C_ A ) $= fordelss_0 word fordelss_0 wtr fordelss_1 fordelss_0 wcel fordelss_1 fordelss_0 wss fordelss_0 ordtr fordelss_0 wtr fordelss_1 fordelss_0 wcel fordelss_1 fordelss_0 wss fordelss_0 fordelss_1 trss imp sylan $.
$}
$( A transitive subclass of an ordinal class is ordinal.  (Contributed by NM,
     29-May-1994.) $)
${
	ftrssord_0 $f class A $.
	ftrssord_1 $f class B $.
	trssord $p |- ( ( Tr A /\ A C_ B /\ Ord B ) -> Ord A ) $= ftrssord_0 wtr ftrssord_0 ftrssord_1 wss ftrssord_1 word w3a ftrssord_0 wtr ftrssord_0 cep wwe wa ftrssord_0 word ftrssord_0 wtr ftrssord_0 ftrssord_1 wss ftrssord_1 word ftrssord_0 wtr ftrssord_0 cep wwe wa ftrssord_0 ftrssord_1 wss ftrssord_1 word wa ftrssord_0 cep wwe ftrssord_0 wtr ftrssord_1 word ftrssord_0 ftrssord_1 wss ftrssord_1 cep wwe ftrssord_0 cep wwe ftrssord_1 ordwe ftrssord_0 ftrssord_1 wss ftrssord_1 cep wwe ftrssord_0 cep wwe ftrssord_0 ftrssord_1 cep wess imp sylan2 anim2i 3impb ftrssord_0 df-ord sylibr $.
$}
$( Epsilon irreflexivity of ordinals: no ordinal class is a member of
     itself.  Theorem 2.2(i) of [BellMachover] p. 469, generalized to classes.
     We prove this without invoking the Axiom of Regularity.  (Contributed by
     NM, 2-Jan-1994.) $)
${
	fordirr_0 $f class A $.
	ordirr $p |- ( Ord A -> -. A e. A ) $= fordirr_0 word fordirr_0 cep wfr fordirr_0 fordirr_0 wcel wn fordirr_0 ordfr fordirr_0 efrirr syl $.
$}
$( A member of an ordinal class is not equal to it.  (Contributed by NM,
     25-May-1998.) $)
${
	fnordeq_0 $f class A $.
	fnordeq_1 $f class B $.
	nordeq $p |- ( ( Ord A /\ B e. A ) -> A =/= B ) $= fnordeq_0 word fnordeq_1 fnordeq_0 wcel fnordeq_0 fnordeq_1 wne fnordeq_0 word fnordeq_1 fnordeq_0 wcel fnordeq_0 fnordeq_1 fnordeq_0 word fnordeq_0 fnordeq_0 wcel wn fnordeq_0 fnordeq_1 wceq fnordeq_1 fnordeq_0 wcel wn fnordeq_0 ordirr fnordeq_0 fnordeq_1 wceq fnordeq_0 fnordeq_0 wcel fnordeq_1 fnordeq_0 wcel fnordeq_0 fnordeq_1 fnordeq_0 eleq1 notbid syl5ibcom necon2ad imp $.
$}
$( An ordinal class cannot an element of one of its members.  Variant of
     first part of Theorem 2.2(vii) of [BellMachover] p. 469.  (Contributed by
     NM, 3-Apr-1994.) $)
${
	fordn2lp_0 $f class A $.
	fordn2lp_1 $f class B $.
	ordn2lp $p |- ( Ord A -> -. ( A e. B /\ B e. A ) ) $= fordn2lp_0 word fordn2lp_0 fordn2lp_1 wcel fordn2lp_1 fordn2lp_0 wcel wa fordn2lp_0 fordn2lp_0 wcel fordn2lp_0 ordirr fordn2lp_0 word fordn2lp_0 wtr fordn2lp_0 fordn2lp_1 wcel fordn2lp_1 fordn2lp_0 wcel wa fordn2lp_0 fordn2lp_0 wcel wi fordn2lp_0 ordtr fordn2lp_0 fordn2lp_0 fordn2lp_1 trel syl mtod $.
$}
$( A subclass (possibly proper) of an ordinal class has a minimal element.
       Proposition 7.5 of [TakeutiZaring] p. 36.  (Contributed by NM,
       18-Feb-2004.)  (Revised by David Abernethy, 16-Mar-2011.) $)
${
	$d x B $.
	ftz7.5_0 $f set x $.
	ftz7.5_1 $f class A $.
	ftz7.5_2 $f class B $.
	tz7.5 $p |- ( ( Ord A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= ftz7.5_1 word ftz7.5_1 cep wwe ftz7.5_2 ftz7.5_1 wss ftz7.5_2 c0 wne ftz7.5_2 ftz7.5_0 cv cin c0 wceq ftz7.5_0 ftz7.5_2 wrex ftz7.5_1 ordwe ftz7.5_0 ftz7.5_1 ftz7.5_2 wefrc syl3an1 $.
$}
$( An element of an ordinal class is ordinal.  Proposition 7.6 of
       [TakeutiZaring] p. 36.  (Contributed by NM, 23-Apr-1994.) $)
${
	$d x y z A $.
	$d x y z B $.
	iordelord_0 $f set x $.
	iordelord_1 $f set y $.
	iordelord_2 $f set z $.
	fordelord_0 $f class A $.
	fordelord_1 $f class B $.
	ordelord $p |- ( ( Ord A /\ B e. A ) -> Ord B ) $= fordelord_0 word fordelord_1 fordelord_0 wcel fordelord_1 word fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_0 cv word wi fordelord_0 word fordelord_1 fordelord_0 wcel wa fordelord_1 word wi iordelord_0 fordelord_1 fordelord_0 iordelord_0 cv fordelord_1 wceq fordelord_0 word iordelord_0 cv fordelord_0 wcel wa fordelord_0 word fordelord_1 fordelord_0 wcel wa iordelord_0 cv word fordelord_1 word iordelord_0 cv fordelord_1 wceq iordelord_0 cv fordelord_0 wcel fordelord_1 fordelord_0 wcel fordelord_0 word iordelord_0 cv fordelord_1 fordelord_0 eleq1 anbi2d iordelord_0 cv fordelord_1 ordeq imbi12d fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_0 cv wtr iordelord_0 cv cep wwe iordelord_0 cv word fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel wi iordelord_1 wal iordelord_2 wal iordelord_0 cv wtr fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel wi iordelord_2 iordelord_1 fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel wi fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa wa fordelord_0 word iordelord_2 cv fordelord_0 wcel iordelord_1 cv fordelord_0 wcel iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel wi fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa simpll fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv fordelord_0 wcel iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa wa iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel iordelord_0 cv fordelord_0 wcel w3a fordelord_0 word iordelord_2 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel iordelord_0 cv fordelord_0 wcel w3a iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel w3a iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa wa iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel 3anrot iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel 3anass bitr3i fordelord_0 word fordelord_0 wtr iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel iordelord_0 cv fordelord_0 wcel w3a iordelord_2 cv fordelord_0 wcel wi fordelord_0 ordtr fordelord_0 iordelord_2 cv iordelord_1 cv iordelord_0 cv trel3 syl syl5bir impl fordelord_0 word iordelord_0 cv fordelord_0 wcel wa iordelord_1 cv iordelord_0 cv wcel iordelord_1 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_1 cv iordelord_0 cv wcel iordelord_1 cv fordelord_0 wcel fordelord_0 word iordelord_1 cv iordelord_0 cv wcel iordelord_0 cv fordelord_0 wcel iordelord_1 cv fordelord_0 wcel fordelord_0 word fordelord_0 wtr iordelord_1 cv iordelord_0 cv wcel iordelord_0 cv fordelord_0 wcel wa iordelord_1 cv fordelord_0 wcel wi fordelord_0 ordtr fordelord_0 iordelord_1 cv iordelord_0 cv trel syl exp3acom23 imp31 adantrl fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa simplr fordelord_0 word fordelord_0 cep wwe iordelord_2 cv fordelord_0 wcel iordelord_1 cv fordelord_0 wcel iordelord_0 cv fordelord_0 wcel w3a iordelord_2 cv iordelord_1 cv wcel iordelord_1 cv iordelord_0 cv wcel wa iordelord_2 cv iordelord_0 cv wcel wi fordelord_0 ordwe iordelord_2 iordelord_1 iordelord_0 fordelord_0 wetrep sylan syl13anc ex pm2.43d alrimivv iordelord_2 iordelord_1 iordelord_0 cv dftr2 sylibr fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_0 cv cep wwe fordelord_0 word iordelord_0 cv fordelord_0 wcel iordelord_0 cv fordelord_0 wss iordelord_0 cv cep wwe fordelord_0 word fordelord_0 wtr iordelord_0 cv fordelord_0 wcel iordelord_0 cv fordelord_0 wss wi fordelord_0 ordtr fordelord_0 iordelord_0 cv trss syl fordelord_0 word fordelord_0 cep wwe iordelord_0 cv fordelord_0 wss iordelord_0 cv cep wwe fordelord_0 ordwe iordelord_0 cv fordelord_0 cep wess syl5com syld imp iordelord_0 cv df-ord sylanbrc vtoclg anabsi7 $.
$}
$( The class of all ordinal numbers is transitive.  (Contributed by NM,
       4-May-2009.) $)
${
	$d x y $.
	itron_0 $f set x $.
	itron_1 $f set y $.
	tron $p |- Tr On $= con0 wtr itron_0 cv con0 wss itron_0 con0 itron_0 con0 dftr3 itron_0 cv con0 wcel itron_1 itron_0 cv con0 itron_0 cv con0 wcel itron_1 cv itron_0 cv wcel itron_1 cv word itron_1 cv con0 wcel itron_0 cv con0 wcel itron_1 cv itron_0 cv wcel itron_1 cv word itron_0 cv con0 wcel itron_0 cv word itron_1 cv itron_0 cv wcel itron_1 cv word itron_0 cv itron_0 vex elon itron_0 cv itron_1 cv ordelord sylanb ex itron_1 cv itron_1 vex elon syl6ibr ssrdv mprgbir $.
$}
$( An element of an ordinal class is an ordinal number.  (Contributed by NM,
     26-Oct-2003.) $)
${
	fordelon_0 $f class A $.
	fordelon_1 $f class B $.
	ordelon $p |- ( ( Ord A /\ B e. A ) -> B e. On ) $= fordelon_0 word fordelon_1 fordelon_0 wcel wa fordelon_1 con0 wcel fordelon_1 word fordelon_0 fordelon_1 ordelord fordelon_1 fordelon_0 wcel fordelon_1 con0 wcel fordelon_1 word wb fordelon_0 word fordelon_1 fordelon_0 elong adantl mpbird $.
$}
$( An element of an ordinal number is an ordinal number.  Theorem 2.2(iii) of
     [BellMachover] p. 469.  (Contributed by NM, 26-Oct-2003.) $)
${
	fonelon_0 $f class A $.
	fonelon_1 $f class B $.
	onelon $p |- ( ( A e. On /\ B e. A ) -> B e. On ) $= fonelon_0 con0 wcel fonelon_0 word fonelon_1 fonelon_0 wcel fonelon_1 con0 wcel fonelon_0 eloni fonelon_0 fonelon_1 ordelon sylan $.
$}
$( Proposition 7.7 of [TakeutiZaring] p. 37.  (Contributed by NM,
       5-May-1994.) $)
${
	$d x y A $.
	$d x y B $.
	itz7.7_0 $f set x $.
	itz7.7_1 $f set y $.
	ftz7.7_0 $f class A $.
	ftz7.7_1 $f class B $.
	tz7.7 $p |- ( ( Ord A /\ Tr B ) -> ( B e. A <-> ( B C_ A /\ B =/= A ) ) ) $= ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne wa ftz7.7_0 word ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne wa wi ftz7.7_1 wtr ftz7.7_0 word ftz7.7_0 wtr ftz7.7_0 cep wfr ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne wa wi ftz7.7_0 ordtr ftz7.7_0 ordfr ftz7.7_0 wtr ftz7.7_0 cep wfr ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne wa ftz7.7_0 ftz7.7_1 tz7.2 3exp sylc adantr ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne ftz7.7_1 ftz7.7_0 wcel ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne ftz7.7_1 ftz7.7_0 wcel wi ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wne wa ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_1 ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 pssdifn0 ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_1 ftz7.7_0 wcel wi wi ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_0 word ftz7.7_1 ftz7.7_0 wss ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_1 ftz7.7_0 wcel wi wi ftz7.7_1 wtr ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_0 word ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_1 ftz7.7_0 wcel wi ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss ftz7.7_0 word ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_1 ftz7.7_0 wcel ftz7.7_0 word ftz7.7_0 ftz7.7_1 cdif c0 wne wa ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 ftz7.7_0 ftz7.7_1 cdif wrex ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa ftz7.7_1 ftz7.7_0 wcel ftz7.7_0 word ftz7.7_0 ftz7.7_1 cdif ftz7.7_0 wss ftz7.7_0 ftz7.7_1 cdif c0 wne ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 ftz7.7_0 ftz7.7_1 cdif wrex ftz7.7_0 ftz7.7_1 difss itz7.7_0 ftz7.7_0 ftz7.7_0 ftz7.7_1 cdif tz7.5 mp3an2 ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq ftz7.7_1 ftz7.7_0 wcel itz7.7_0 ftz7.7_0 ftz7.7_1 cdif ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq ftz7.7_1 ftz7.7_0 wcel ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq wa wa itz7.7_0 cv ftz7.7_1 ftz7.7_0 ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq wa wa itz7.7_0 cv ftz7.7_1 ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_1 wss ftz7.7_0 word itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_1 wss wi wi ftz7.7_1 wtr ftz7.7_1 ftz7.7_0 wss ftz7.7_0 word ftz7.7_0 wtr itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_1 wss wi wi ftz7.7_0 ordtr itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv ftz7.7_0 wcel ftz7.7_0 wtr itz7.7_0 cv ftz7.7_0 wss ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_1 wss wi itz7.7_0 cv ftz7.7_0 ftz7.7_1 eldifi ftz7.7_0 itz7.7_0 cv trss ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_0 wss itz7.7_0 cv ftz7.7_1 wss ftz7.7_0 ftz7.7_1 itz7.7_0 cv difin0ss com12 syl56 syl ad2antrr imp32 ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_1 itz7.7_0 cv wss ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa itz7.7_1 ftz7.7_1 itz7.7_0 cv ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv ftz7.7_1 wcel itz7.7_1 cv itz7.7_0 cv wcel wi ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv itz7.7_0 cv wcel ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv itz7.7_0 cv wcel ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa wa itz7.7_1 cv itz7.7_0 cv wcel itz7.7_1 cv itz7.7_0 cv wceq itz7.7_0 cv itz7.7_1 cv wcel ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa itz7.7_1 cv itz7.7_0 cv wceq wn ftz7.7_0 word ftz7.7_1 wtr wa itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv itz7.7_0 cv wceq wn ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv itz7.7_0 cv wceq wn itz7.7_1 cv ftz7.7_1 wcel itz7.7_1 cv itz7.7_0 cv wceq itz7.7_0 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_1 cv itz7.7_0 cv wceq itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_1 wcel itz7.7_1 cv itz7.7_0 cv ftz7.7_1 eleq1 biimpcd itz7.7_0 cv ftz7.7_0 ftz7.7_1 eldifn nsyli imp adantll adantl ftz7.7_1 wtr ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa itz7.7_0 cv itz7.7_1 cv wcel wn ftz7.7_0 word ftz7.7_1 wtr ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv itz7.7_1 cv wcel wn ftz7.7_1 wtr itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv itz7.7_1 cv wcel wn wi ftz7.7_1 ftz7.7_0 wss ftz7.7_1 wtr itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv itz7.7_1 cv wcel wn wi ftz7.7_1 wtr itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv itz7.7_1 cv wcel itz7.7_0 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel ftz7.7_1 wtr itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv itz7.7_1 cv wcel itz7.7_0 cv ftz7.7_1 wcel wi ftz7.7_1 wtr itz7.7_0 cv itz7.7_1 cv wcel itz7.7_1 cv ftz7.7_1 wcel itz7.7_0 cv ftz7.7_1 wcel ftz7.7_1 itz7.7_0 cv itz7.7_1 cv trel exp3acom23 imp itz7.7_0 cv ftz7.7_0 ftz7.7_1 eldifn nsyli ex adantld imp32 adantll ftz7.7_0 word ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa itz7.7_1 cv itz7.7_0 cv wcel itz7.7_1 cv itz7.7_0 cv wceq itz7.7_0 cv itz7.7_1 cv wcel w3o ftz7.7_1 wtr ftz7.7_0 word ftz7.7_0 cep wwe itz7.7_1 cv ftz7.7_0 wcel itz7.7_0 cv ftz7.7_0 wcel wa itz7.7_1 cv itz7.7_0 cv wcel itz7.7_1 cv itz7.7_0 cv wceq itz7.7_0 cv itz7.7_1 cv wcel w3o ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel wa ftz7.7_0 ordwe ftz7.7_1 ftz7.7_0 wss itz7.7_1 cv ftz7.7_1 wcel wa itz7.7_1 cv ftz7.7_0 wcel itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv ftz7.7_0 wcel ftz7.7_1 ftz7.7_0 itz7.7_1 cv ssel2 itz7.7_0 cv ftz7.7_0 ftz7.7_1 eldifi anim12i itz7.7_1 itz7.7_0 ftz7.7_0 wecmpep syl2an adantlr ecase23d exp44 com34 imp31 ssrdv adantrr eqssd itz7.7_0 cv ftz7.7_0 ftz7.7_1 cdif wcel itz7.7_0 cv ftz7.7_0 wcel ftz7.7_0 word ftz7.7_1 wtr wa ftz7.7_1 ftz7.7_0 wss wa ftz7.7_0 ftz7.7_1 cdif itz7.7_0 cv cin c0 wceq itz7.7_0 cv ftz7.7_0 ftz7.7_1 eldifi ad2antrl eqeltrrd exp32 rexlimdv syl5 exp4b com23 adantrd pm2.43i syl7 exp4a pm2.43d imp3a impbid $.
$}
$( Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     25-Nov-1995.) $)
${
	fordelssne_0 $f class A $.
	fordelssne_1 $f class B $.
	ordelssne $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $= fordelssne_1 word fordelssne_0 word fordelssne_0 fordelssne_1 wcel fordelssne_0 fordelssne_1 wss fordelssne_0 fordelssne_1 wne wa wb fordelssne_0 word fordelssne_1 word fordelssne_0 wtr fordelssne_0 fordelssne_1 wcel fordelssne_0 fordelssne_1 wss fordelssne_0 fordelssne_1 wne wa wb fordelssne_0 ordtr fordelssne_1 fordelssne_0 tz7.7 sylan2 ancoms $.
$}
$( Corollary 7.8 of [TakeutiZaring] p. 37.  (Contributed by NM,
     17-Jun-1998.) $)
${
	fordelpss_0 $f class A $.
	fordelpss_1 $f class B $.
	ordelpss $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> A C. B ) ) $= fordelpss_0 word fordelpss_1 word wa fordelpss_0 fordelpss_1 wcel fordelpss_0 fordelpss_1 wss fordelpss_0 fordelpss_1 wne wa fordelpss_0 fordelpss_1 wpss fordelpss_0 fordelpss_1 ordelssne fordelpss_0 fordelpss_1 df-pss syl6bbr $.
$}
$( For ordinal classes, subclass is equivalent to membership or equality.
     (Contributed by NM, 25-Nov-1995.)  (Proof shortened by Andrew Salmon,
     25-Jul-2011.) $)
${
	fordsseleq_0 $f class A $.
	fordsseleq_1 $f class B $.
	ordsseleq $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) ) $= fordsseleq_0 word fordsseleq_1 word wa fordsseleq_0 fordsseleq_1 wcel fordsseleq_0 fordsseleq_1 wceq wo fordsseleq_0 fordsseleq_1 wpss fordsseleq_0 fordsseleq_1 wceq wo fordsseleq_0 fordsseleq_1 wss fordsseleq_0 word fordsseleq_1 word wa fordsseleq_0 fordsseleq_1 wcel fordsseleq_0 fordsseleq_1 wpss fordsseleq_0 fordsseleq_1 wceq fordsseleq_0 fordsseleq_1 ordelpss orbi1d fordsseleq_0 fordsseleq_1 sspss syl6rbbr $.
$}
$( The intersection of two ordinal classes is ordinal.  Proposition 7.9 of
     [TakeutiZaring] p. 37.  (Contributed by NM, 9-May-1994.) $)
${
	fordin_0 $f class A $.
	fordin_1 $f class B $.
	ordin $p |- ( ( Ord A /\ Ord B ) -> Ord ( A i^i B ) ) $= fordin_0 word fordin_1 word fordin_0 fordin_1 cin wtr fordin_0 fordin_1 cin word fordin_0 word fordin_0 wtr fordin_1 wtr fordin_0 fordin_1 cin wtr fordin_1 word fordin_0 ordtr fordin_1 ordtr fordin_0 fordin_1 trin syl2an fordin_0 fordin_1 cin wtr fordin_0 fordin_1 cin fordin_1 wss fordin_1 word fordin_0 fordin_1 cin word fordin_0 fordin_1 inss2 fordin_0 fordin_1 cin fordin_1 trssord mp3an2 sylancom $.
$}
$( The intersection of two ordinal numbers is an ordinal number.
       (Contributed by NM, 7-Apr-1995.) $)
${
	fonin_0 $f class A $.
	fonin_1 $f class B $.
	onin $p |- ( ( A e. On /\ B e. On ) -> ( A i^i B ) e. On ) $= fonin_0 con0 wcel fonin_1 con0 wcel wa fonin_0 fonin_1 cin con0 wcel fonin_0 fonin_1 cin word fonin_0 con0 wcel fonin_0 word fonin_1 word fonin_0 fonin_1 cin word fonin_1 con0 wcel fonin_0 eloni fonin_1 eloni fonin_0 fonin_1 ordin syl2an fonin_0 con0 wcel fonin_1 con0 wcel wa fonin_0 con0 wcel fonin_0 fonin_1 cin cvv wcel fonin_0 fonin_1 cin con0 wcel fonin_0 fonin_1 cin word wb fonin_0 con0 wcel fonin_1 con0 wcel simpl fonin_0 fonin_1 con0 inex1g fonin_0 fonin_1 cin cvv elong 3syl mpbird $.
$}
$( A trichotomy law for ordinals.  Proposition 7.10 of [TakeutiZaring]
     p. 38.  (Contributed by NM, 10-May-1994.)  (Proof shortened by Andrew
     Salmon, 25-Jul-2011.) $)
${
	fordtri3or_0 $f class A $.
	fordtri3or_1 $f class B $.
	ordtri3or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ A = B \/ B e. A ) ) $= fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 wcel fordtri3or_0 fordtri3or_1 wceq fordtri3or_1 fordtri3or_0 wcel w3o fordtri3or_0 fordtri3or_1 wpss fordtri3or_0 fordtri3or_1 wceq fordtri3or_1 fordtri3or_0 wpss w3o fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 wss fordtri3or_1 fordtri3or_0 wss wo fordtri3or_0 fordtri3or_1 wpss fordtri3or_0 fordtri3or_1 wceq fordtri3or_1 fordtri3or_0 wpss w3o fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel wn fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wn wo fordtri3or_0 fordtri3or_1 wss fordtri3or_1 fordtri3or_0 wss wo fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 fordtri3or_1 cin wcel wn fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel wn fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wn wo fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin word fordtri3or_0 fordtri3or_1 cin fordtri3or_0 fordtri3or_1 cin wcel wn fordtri3or_0 fordtri3or_1 ordin fordtri3or_0 fordtri3or_1 cin ordirr syl fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel wn fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wn wo fordtri3or_0 fordtri3or_1 cin fordtri3or_0 fordtri3or_1 cin wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel ianor fordtri3or_0 fordtri3or_1 cin fordtri3or_0 fordtri3or_1 cin wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_1 wcel wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 fordtri3or_1 elin fordtri3or_0 fordtri3or_1 cin fordtri3or_1 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_1 fordtri3or_0 cin fordtri3or_1 fordtri3or_0 fordtri3or_1 incom eleq1i anbi2i bitri xchnxbir sylib fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel wn fordtri3or_0 fordtri3or_1 wss fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wn fordtri3or_1 fordtri3or_0 wss fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel wn fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wceq fordtri3or_0 fordtri3or_1 wss fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wceq fordtri3or_0 word fordtri3or_1 word fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wceq wo fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 cin word fordtri3or_0 word fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wceq wo fordtri3or_0 fordtri3or_1 ordin fordtri3or_0 fordtri3or_1 cin word fordtri3or_0 word wa fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wss fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wcel fordtri3or_0 fordtri3or_1 cin fordtri3or_0 wceq wo fordtri3or_0 fordtri3or_1 inss1 fordtri3or_0 fordtri3or_1 cin fordtri3or_0 ordsseleq mpbii sylan anabss1 ord fordtri3or_0 fordtri3or_1 df-ss syl6ibr fordtri3or_0 word fordtri3or_1 word wa fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel wn fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wceq fordtri3or_1 fordtri3or_0 wss fordtri3or_0 word fordtri3or_1 word wa fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wceq fordtri3or_0 word fordtri3or_1 word fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wceq wo fordtri3or_1 word fordtri3or_0 word wa fordtri3or_1 fordtri3or_0 cin word fordtri3or_1 word fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wceq wo fordtri3or_1 fordtri3or_0 ordin fordtri3or_1 fordtri3or_0 cin word fordtri3or_1 word wa fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wss fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wcel fordtri3or_1 fordtri3or_0 cin fordtri3or_1 wceq wo fordtri3or_1 fordtri3or_0 inss1 fordtri3or_1 fordtri3or_0 cin fordtri3or_1 ordsseleq mpbii sylan anabss4 ord fordtri3or_1 fordtri3or_0 df-ss syl6ibr orim12d mpd fordtri3or_0 fordtri3or_1 sspsstri sylib fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 wcel fordtri3or_0 fordtri3or_1 wpss fordtri3or_0 fordtri3or_1 wceq fordtri3or_0 fordtri3or_1 wceq fordtri3or_1 fordtri3or_0 wcel fordtri3or_1 fordtri3or_0 wpss fordtri3or_0 fordtri3or_1 ordelpss fordtri3or_0 word fordtri3or_1 word wa fordtri3or_0 fordtri3or_1 wceq biidd fordtri3or_1 word fordtri3or_0 word fordtri3or_1 fordtri3or_0 wcel fordtri3or_1 fordtri3or_0 wpss wb fordtri3or_1 fordtri3or_0 ordelpss ancoms 3orbi123d mpbird $.
$}
$( A trichotomy law for ordinals.  (Contributed by NM, 25-Mar-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fordtri1_0 $f class A $.
	fordtri1_1 $f class B $.
	ordtri1 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> -. B e. A ) ) $= fordtri1_0 word fordtri1_1 word wa fordtri1_0 fordtri1_1 wss fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq wo fordtri1_1 fordtri1_0 wcel wn fordtri1_0 fordtri1_1 ordsseleq fordtri1_0 word fordtri1_1 word wa fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq wo fordtri1_1 fordtri1_0 wcel wn fordtri1_0 word fordtri1_0 fordtri1_1 wcel fordtri1_1 fordtri1_0 wcel wn fordtri1_1 word fordtri1_0 fordtri1_1 wceq fordtri1_0 word fordtri1_0 fordtri1_1 wcel fordtri1_1 fordtri1_0 wcel wa wn fordtri1_0 fordtri1_1 wcel fordtri1_1 fordtri1_0 wcel wn wi fordtri1_0 fordtri1_1 ordn2lp fordtri1_0 fordtri1_1 wcel fordtri1_1 fordtri1_0 wcel imnan sylibr fordtri1_1 word fordtri1_1 fordtri1_0 wcel wn fordtri1_0 fordtri1_1 wceq fordtri1_1 fordtri1_1 wcel wn fordtri1_1 ordirr fordtri1_0 fordtri1_1 wceq fordtri1_1 fordtri1_0 wcel fordtri1_1 fordtri1_1 wcel fordtri1_0 fordtri1_1 fordtri1_1 eleq2 notbid syl5ibrcom jaao fordtri1_0 word fordtri1_1 word wa fordtri1_1 fordtri1_0 wcel fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq wo fordtri1_0 word fordtri1_1 word wa fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq wo fordtri1_1 fordtri1_0 wcel fordtri1_0 word fordtri1_1 word wa fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq fordtri1_1 fordtri1_0 wcel w3o fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq wo fordtri1_1 fordtri1_0 wcel wo fordtri1_0 fordtri1_1 ordtri3or fordtri1_0 fordtri1_1 wcel fordtri1_0 fordtri1_1 wceq fordtri1_1 fordtri1_0 wcel df-3or sylib orcomd ord impbid bitrd $.
$}
$( A trichotomy law for ordinal numbers.  (Contributed by NM, 6-Nov-2003.) $)
${
	fontri1_0 $f class A $.
	fontri1_1 $f class B $.
	ontri1 $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> -. B e. A ) ) $= fontri1_0 con0 wcel fontri1_0 word fontri1_1 word fontri1_0 fontri1_1 wss fontri1_1 fontri1_0 wcel wn wb fontri1_1 con0 wcel fontri1_0 eloni fontri1_1 eloni fontri1_0 fontri1_1 ordtri1 syl2an $.
$}
$( A trichotomy law for ordinals.  (Contributed by NM, 25-Nov-1995.) $)
${
	fordtri2_0 $f class A $.
	fordtri2_1 $f class B $.
	ordtri2 $p |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> -. ( A = B \/ B e. A ) ) ) $= fordtri2_0 word fordtri2_1 word wa fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel wo fordtri2_0 fordtri2_1 wcel fordtri2_1 word fordtri2_0 word fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel wo fordtri2_0 fordtri2_1 wcel wn wb fordtri2_1 word fordtri2_0 word wa fordtri2_1 fordtri2_0 wss fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel wo fordtri2_0 fordtri2_1 wcel wn fordtri2_1 word fordtri2_0 word wa fordtri2_1 fordtri2_0 wss fordtri2_1 fordtri2_0 wcel fordtri2_1 fordtri2_0 wceq wo fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel wo fordtri2_1 fordtri2_0 ordsseleq fordtri2_1 fordtri2_0 wcel fordtri2_1 fordtri2_0 wceq wo fordtri2_1 fordtri2_0 wcel fordtri2_0 fordtri2_1 wceq wo fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel wo fordtri2_1 fordtri2_0 wceq fordtri2_0 fordtri2_1 wceq fordtri2_1 fordtri2_0 wcel fordtri2_1 fordtri2_0 eqcom orbi2i fordtri2_1 fordtri2_0 wcel fordtri2_0 fordtri2_1 wceq orcom bitri syl6bb fordtri2_1 fordtri2_0 ordtri1 bitr3d ancoms con2bid $.
$}
$( A trichotomy law for ordinals.  (Contributed by NM, 18-Oct-1995.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fordtri3_0 $f class A $.
	fordtri3_1 $f class B $.
	ordtri3 $p |- ( ( Ord A /\ Ord B ) -> ( A = B <-> -. ( A e. B \/ B e. A ) ) ) $= fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wceq fordtri3_0 fordtri3_1 wcel fordtri3_1 fordtri3_0 wcel wo wn fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wceq fordtri3_0 fordtri3_1 wcel wn fordtri3_1 fordtri3_0 wcel wn wa fordtri3_0 fordtri3_1 wcel fordtri3_1 fordtri3_0 wcel wo wn fordtri3_0 fordtri3_1 wceq fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wcel wn fordtri3_1 fordtri3_0 wcel wn wa fordtri3_0 fordtri3_1 wceq fordtri3_0 word fordtri3_0 fordtri3_1 wcel wn fordtri3_1 word fordtri3_1 fordtri3_0 wcel wn fordtri3_0 word fordtri3_0 fordtri3_0 wcel wn fordtri3_0 fordtri3_1 wceq fordtri3_0 fordtri3_1 wcel wn fordtri3_0 ordirr fordtri3_0 fordtri3_1 wceq fordtri3_0 fordtri3_0 wcel fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 fordtri3_0 eleq2 notbid syl5ib fordtri3_1 word fordtri3_1 fordtri3_0 wcel wn fordtri3_0 fordtri3_1 wceq fordtri3_1 fordtri3_1 wcel wn fordtri3_1 ordirr fordtri3_0 fordtri3_1 wceq fordtri3_1 fordtri3_0 wcel fordtri3_1 fordtri3_1 wcel fordtri3_0 fordtri3_1 fordtri3_1 eleq2 notbid syl5ibr anim12d com12 fordtri3_0 fordtri3_1 wcel fordtri3_1 fordtri3_0 wcel pm4.56 syl6ib fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wcel fordtri3_1 fordtri3_0 wcel wo fordtri3_0 fordtri3_1 wceq fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 wceq wo fordtri3_1 fordtri3_0 wcel wo fordtri3_0 fordtri3_1 wcel fordtri3_1 fordtri3_0 wcel wo fordtri3_0 fordtri3_1 wceq wo fordtri3_0 word fordtri3_1 word wa fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 wceq fordtri3_1 fordtri3_0 wcel w3o fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 wceq wo fordtri3_1 fordtri3_0 wcel wo fordtri3_0 fordtri3_1 ordtri3or fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 wceq fordtri3_1 fordtri3_0 wcel df-3or sylib fordtri3_0 fordtri3_1 wcel fordtri3_0 fordtri3_1 wceq fordtri3_1 fordtri3_0 wcel or32 sylib ord impbid $.
$}
$( A trichotomy law for ordinals.  (Contributed by NM, 1-Nov-2003.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fordtri4_0 $f class A $.
	fordtri4_1 $f class B $.
	ordtri4 $p |- ( ( Ord A /\ Ord B ) -> ( A = B <-> ( A C_ B /\ -. A e. B ) ) ) $= fordtri4_0 fordtri4_1 wceq fordtri4_0 fordtri4_1 wss fordtri4_1 fordtri4_0 wss wa fordtri4_0 word fordtri4_1 word wa fordtri4_0 fordtri4_1 wss fordtri4_0 fordtri4_1 wcel wn wa fordtri4_0 fordtri4_1 eqss fordtri4_0 word fordtri4_1 word wa fordtri4_1 fordtri4_0 wss fordtri4_0 fordtri4_1 wcel wn fordtri4_0 fordtri4_1 wss fordtri4_1 word fordtri4_0 word fordtri4_1 fordtri4_0 wss fordtri4_0 fordtri4_1 wcel wn wb fordtri4_1 fordtri4_0 ordtri1 ancoms anbi2d syl5bb $.
$}
$( An ordinal class and its singleton are disjoint.  (Contributed by NM,
     19-May-1998.) $)
${
	forddisj_0 $f class A $.
	orddisj $p |- ( Ord A -> ( A i^i { A } ) = (/) ) $= forddisj_0 word forddisj_0 forddisj_0 wcel wn forddisj_0 forddisj_0 csn cin c0 wceq forddisj_0 ordirr forddisj_0 forddisj_0 disjsn sylibr $.
$}
$( The ordinal class is well-founded.  This lemma is needed for ~ ordon in
       order to eliminate the need for the Axiom of Regularity.  (Contributed
       by NM, 17-May-1994.) $)
${
	$d x y z $.
	ionfr_0 $f set x $.
	ionfr_1 $f set y $.
	ionfr_2 $f set z $.
	onfr $p |- _E Fr On $= con0 cep wfr ionfr_0 cv con0 wss ionfr_0 cv c0 wne wa ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex wi ionfr_0 ionfr_0 ionfr_2 con0 dfepfr ionfr_0 cv con0 wss ionfr_0 cv c0 wne ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_0 cv c0 wne ionfr_1 cv ionfr_0 cv wcel ionfr_1 wex ionfr_0 cv con0 wss ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_1 ionfr_0 cv n0 ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_1 ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_0 cv ionfr_1 cv cin c0 ionfr_1 cv ionfr_0 cv wcel ionfr_0 cv ionfr_1 cv cin c0 wceq ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_0 cv con0 wss ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_0 cv ionfr_1 cv cin c0 wceq ionfr_2 ionfr_1 cv ionfr_0 cv ionfr_2 cv ionfr_1 cv wceq ionfr_0 cv ionfr_2 cv cin ionfr_0 cv ionfr_1 cv cin c0 ionfr_2 cv ionfr_1 cv ionfr_0 cv ineq2 eqeq1d rspcev adantll ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_0 cv ionfr_1 cv cin c0 wne wa ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_0 cv ionfr_1 cv cin c0 wne wa ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_1 cv cep wfr ionfr_0 cv ionfr_1 cv cin c0 wne ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_1 cv word ionfr_1 cv cep wfr ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_1 cv con0 wcel ionfr_1 cv word ionfr_0 cv con0 ionfr_1 cv ssel2 ionfr_1 cv eloni syl ionfr_1 cv ordfr syl ionfr_1 cv cep wfr ionfr_0 cv ionfr_1 cv cin ionfr_1 cv wss ionfr_0 cv ionfr_1 cv cin c0 wne ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv ionfr_1 cv inss2 ionfr_2 ionfr_1 cv ionfr_0 cv ionfr_1 cv cin ionfr_0 cv ionfr_1 cv ionfr_0 vex inex1 epfrc mp3an2 sylan ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex wb ionfr_0 cv ionfr_1 cv cin c0 wne ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin c0 wceq ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin ionfr_0 cv ionfr_2 cv cin c0 ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_0 cv ionfr_1 cv cin ionfr_2 cv cin ionfr_0 cv ionfr_1 cv ionfr_2 cv cin cin ionfr_0 cv ionfr_2 cv cin ionfr_0 cv ionfr_1 cv ionfr_2 cv inass ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_1 cv ionfr_2 cv cin ionfr_2 cv ionfr_0 cv ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_2 cv ionfr_1 cv wss ionfr_1 cv ionfr_2 cv cin ionfr_2 cv wceq ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_1 cv word ionfr_2 cv ionfr_1 cv wcel ionfr_2 cv ionfr_1 cv wss ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_1 cv word ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_1 cv con0 wcel ionfr_1 cv word ionfr_0 cv con0 ionfr_1 cv ssel2 ionfr_1 cv eloni syl adantr ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel wa ionfr_0 cv ionfr_1 cv cin ionfr_1 cv ionfr_2 cv ionfr_0 cv ionfr_1 cv inss2 ionfr_0 cv con0 wss ionfr_1 cv ionfr_0 cv wcel wa ionfr_2 cv ionfr_0 cv ionfr_1 cv cin wcel simpr sseldi ionfr_1 cv ionfr_2 cv ordelss syl2anc ionfr_2 cv ionfr_1 cv dfss1 sylib ineq2d syl5eq eqeq1d rexbidva adantr mpbid ionfr_0 cv ionfr_1 cv cin ionfr_0 cv wss ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin wrex ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv wrex wi ionfr_0 cv ionfr_1 cv inss1 ionfr_0 cv ionfr_2 cv cin c0 wceq ionfr_2 ionfr_0 cv ionfr_1 cv cin ionfr_0 cv ssrexv ax-mp syl pm2.61dane ex exlimdv syl5bi imp mpgbir $.
$}
$( Relationship between membership and proper subset of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)
${
	fonelpss_0 $f class A $.
	fonelpss_1 $f class B $.
	onelpss $p |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) ) $= fonelpss_0 con0 wcel fonelpss_0 word fonelpss_1 word fonelpss_0 fonelpss_1 wcel fonelpss_0 fonelpss_1 wss fonelpss_0 fonelpss_1 wne wa wb fonelpss_1 con0 wcel fonelpss_0 eloni fonelpss_1 eloni fonelpss_0 fonelpss_1 ordelssne syl2an $.
$}
$( Relationship between subset and membership of an ordinal number.
     (Contributed by NM, 15-Sep-1995.) $)
${
	fonsseleq_0 $f class A $.
	fonsseleq_1 $f class B $.
	onsseleq $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) ) $= fonsseleq_0 con0 wcel fonsseleq_0 word fonsseleq_1 word fonsseleq_0 fonsseleq_1 wss fonsseleq_0 fonsseleq_1 wcel fonsseleq_0 fonsseleq_1 wceq wo wb fonsseleq_1 con0 wcel fonsseleq_0 eloni fonsseleq_1 eloni fonsseleq_0 fonsseleq_1 ordsseleq syl2an $.
$}
$( An element of an ordinal number is a subset of the number.  (Contributed
     by NM, 5-Jun-1994.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fonelss_0 $f class A $.
	fonelss_1 $f class B $.
	onelss $p |- ( A e. On -> ( B e. A -> B C_ A ) ) $= fonelss_0 con0 wcel fonelss_0 word fonelss_1 fonelss_0 wcel fonelss_1 fonelss_0 wss wi fonelss_0 eloni fonelss_0 word fonelss_1 fonelss_0 wcel fonelss_1 fonelss_0 wss fonelss_0 fonelss_1 ordelss ex syl $.
$}
$( Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.) $)
${
	fordtr1_0 $f class A $.
	fordtr1_1 $f class B $.
	fordtr1_2 $f class C $.
	ordtr1 $p |- ( Ord C -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $= fordtr1_2 word fordtr1_2 wtr fordtr1_0 fordtr1_1 wcel fordtr1_1 fordtr1_2 wcel wa fordtr1_0 fordtr1_2 wcel wi fordtr1_2 ordtr fordtr1_2 fordtr1_0 fordtr1_1 trel syl $.
$}
$( Transitive law for ordinal classes.  (Contributed by NM, 12-Dec-2004.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fordtr2_0 $f class A $.
	fordtr2_1 $f class B $.
	fordtr2_2 $f class C $.
	ordtr2 $p |- ( ( Ord A /\ Ord C ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) ) $= fordtr2_0 word fordtr2_2 word wa fordtr2_0 fordtr2_1 wss fordtr2_1 fordtr2_2 wcel wa fordtr2_0 fordtr2_2 wpss fordtr2_0 fordtr2_2 wcel fordtr2_2 word fordtr2_0 fordtr2_1 wss fordtr2_1 fordtr2_2 wcel wa fordtr2_0 fordtr2_2 wpss wi fordtr2_0 word fordtr2_2 word fordtr2_0 fordtr2_1 wss fordtr2_1 fordtr2_2 wcel fordtr2_0 fordtr2_2 wpss fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 word wa wa fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 fordtr2_2 wcel fordtr2_1 word wa fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 word fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 word fordtr2_2 fordtr2_1 ordelord ex ancld anc2li fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 word wa wa fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 word fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss wi fordtr2_2 word fordtr2_1 word fordtr2_1 fordtr2_2 wcel fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss wi fordtr2_2 word fordtr2_1 word fordtr2_1 fordtr2_2 wcel fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss wi wi fordtr2_2 word fordtr2_1 word wa fordtr2_1 fordtr2_2 wcel fordtr2_1 fordtr2_2 wpss fordtr2_0 fordtr2_1 wss fordtr2_0 fordtr2_2 wpss wi fordtr2_1 word fordtr2_2 word fordtr2_1 fordtr2_2 wcel fordtr2_1 fordtr2_2 wpss wb fordtr2_1 fordtr2_2 ordelpss ancoms fordtr2_0 fordtr2_1 wss fordtr2_1 fordtr2_2 wpss fordtr2_0 fordtr2_2 wpss fordtr2_0 fordtr2_1 fordtr2_2 sspsstr expcom syl6bi ex com23 imp32 com12 syl9 imp3a adantl fordtr2_0 fordtr2_2 ordelpss sylibrd $.
$}
$( Transitive law for ordinal classes.  (Contributed by Mario Carneiro,
     30-Dec-2014.) $)
${
	fordtr3_0 $f class A $.
	fordtr3_1 $f class B $.
	fordtr3_2 $f class C $.
	ordtr3 $p |- ( ( Ord B /\ Ord C ) -> ( A e. B -> ( A e. C \/ C e. B ) ) ) $= fordtr3_1 word fordtr3_2 word wa fordtr3_0 fordtr3_1 wcel fordtr3_0 fordtr3_2 wcel fordtr3_2 fordtr3_1 wcel wo fordtr3_1 word fordtr3_2 word wa fordtr3_0 fordtr3_1 wcel wa fordtr3_0 fordtr3_2 wcel fordtr3_2 fordtr3_1 wcel fordtr3_1 word fordtr3_2 word wa fordtr3_0 fordtr3_1 wcel wa fordtr3_0 fordtr3_2 wcel wn fordtr3_2 fordtr3_0 wss fordtr3_2 fordtr3_1 wcel fordtr3_1 word fordtr3_2 word wa fordtr3_0 fordtr3_1 wcel wa fordtr3_2 word fordtr3_0 word fordtr3_2 fordtr3_0 wss fordtr3_0 fordtr3_2 wcel wn wb fordtr3_1 word fordtr3_2 word fordtr3_0 fordtr3_1 wcel simplr fordtr3_1 word fordtr3_0 fordtr3_1 wcel fordtr3_0 word fordtr3_2 word fordtr3_1 fordtr3_0 ordelord adantlr fordtr3_2 fordtr3_0 ordtri1 syl2anc fordtr3_1 word fordtr3_2 word wa fordtr3_0 fordtr3_1 wcel fordtr3_2 fordtr3_0 wss fordtr3_2 fordtr3_1 wcel fordtr3_1 word fordtr3_2 word wa fordtr3_2 fordtr3_0 wss fordtr3_0 fordtr3_1 wcel fordtr3_2 fordtr3_1 wcel fordtr3_2 word fordtr3_1 word fordtr3_2 fordtr3_0 wss fordtr3_0 fordtr3_1 wcel wa fordtr3_2 fordtr3_1 wcel wi fordtr3_2 fordtr3_0 fordtr3_1 ordtr2 ancoms ancomsd expdimp sylbird orrd ex $.
$}
$( Transitive law for ordinal numbers.  Theorem 7M(b) of [Enderton] p. 192.
     (Contributed by NM, 11-Aug-1994.) $)
${
	fontr1_0 $f class A $.
	fontr1_1 $f class B $.
	fontr1_2 $f class C $.
	ontr1 $p |- ( C e. On -> ( ( A e. B /\ B e. C ) -> A e. C ) ) $= fontr1_2 con0 wcel fontr1_2 word fontr1_0 fontr1_1 wcel fontr1_1 fontr1_2 wcel wa fontr1_0 fontr1_2 wcel wi fontr1_2 eloni fontr1_0 fontr1_1 fontr1_2 ordtr1 syl $.
$}
$( Transitive law for ordinal numbers.  Exercise 3 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Nov-2003.) $)
${
	fontr2_0 $f class A $.
	fontr2_1 $f class B $.
	fontr2_2 $f class C $.
	ontr2 $p |- ( ( A e. On /\ C e. On ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) ) $= fontr2_0 con0 wcel fontr2_0 word fontr2_2 word fontr2_0 fontr2_1 wss fontr2_1 fontr2_2 wcel wa fontr2_0 fontr2_2 wcel wi fontr2_2 con0 wcel fontr2_0 eloni fontr2_2 eloni fontr2_0 fontr2_1 fontr2_2 ordtr2 syl2an $.
$}
$( The union of an ordinal stays the same if a subset equal to one of its
       elements is removed.  (Contributed by NM, 10-Dec-2004.) $)
${
	$d x y A $.
	$d x y B $.
	iordunidif_0 $f set x $.
	iordunidif_1 $f set y $.
	fordunidif_0 $f class A $.
	fordunidif_1 $f class B $.
	ordunidif $p |- ( ( Ord A /\ B e. A ) -> U. ( A \ B ) = U. A ) $= fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex iordunidif_0 fordunidif_0 wral fordunidif_0 fordunidif_1 cdif cuni fordunidif_0 cuni wceq fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex iordunidif_0 fordunidif_0 fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv fordunidif_0 wcel wa iordunidif_0 cv fordunidif_1 wcel iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv fordunidif_0 wcel wa iordunidif_0 cv fordunidif_1 wcel fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv fordunidif_1 wss wa iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv fordunidif_1 wcel fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv fordunidif_1 wss wa wi iordunidif_0 cv fordunidif_0 wcel fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv fordunidif_1 wcel iordunidif_0 cv fordunidif_1 wss fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa fordunidif_1 con0 wcel iordunidif_0 cv fordunidif_1 wcel iordunidif_0 cv fordunidif_1 wss wi fordunidif_0 fordunidif_1 ordelon fordunidif_1 iordunidif_0 cv onelss syl fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa fordunidif_1 con0 wcel fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel fordunidif_0 fordunidif_1 ordelon fordunidif_1 fordunidif_0 wcel fordunidif_1 con0 wcel fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel wi fordunidif_0 word fordunidif_1 con0 wcel fordunidif_1 fordunidif_1 wcel wn fordunidif_1 fordunidif_0 wcel fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel fordunidif_1 con0 wcel fordunidif_1 word fordunidif_1 fordunidif_1 wcel wn fordunidif_1 eloni fordunidif_1 ordirr syl fordunidif_1 fordunidif_0 fordunidif_1 cdif wcel fordunidif_1 fordunidif_0 wcel fordunidif_1 fordunidif_1 wcel wn fordunidif_1 fordunidif_0 fordunidif_1 eldif simplbi2 syl5 adantl mpd jctild adantr iordunidif_0 cv iordunidif_1 cv wss iordunidif_0 cv fordunidif_1 wss iordunidif_1 fordunidif_1 fordunidif_0 fordunidif_1 cdif iordunidif_1 cv fordunidif_1 iordunidif_0 cv sseq2 rspcev syl6 iordunidif_0 cv fordunidif_0 wcel iordunidif_0 cv fordunidif_1 wcel wn iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex wi fordunidif_0 word fordunidif_1 fordunidif_0 wcel wa iordunidif_0 cv fordunidif_0 wcel iordunidif_0 cv fordunidif_1 wcel wn iordunidif_0 cv fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv iordunidif_0 cv wss wa iordunidif_0 cv iordunidif_1 cv wss iordunidif_1 fordunidif_0 fordunidif_1 cdif wrex iordunidif_0 cv fordunidif_0 wcel iordunidif_0 cv fordunidif_1 wcel wn iordunidif_0 cv fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv iordunidif_0 cv wss wa iordunidif_0 cv fordunidif_0 wcel iordunidif_0 cv fordunidif_1 wcel wn wa iordunidif_0 cv fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv iordunidif_0 cv wss iordunidif_0 cv fordunidif_0 fordunidif_1 cdif wcel iordunidif_0 cv fordunidif_0 wcel iordunidif_0 cv fordunidif_1 wcel wn wa iordunidif_0 cv fordunidif_0 fordunidif_1 eldif biimpri iordunidif_0 cv ssid jctir ex iordunidif_0 cv iordunidif_1 cv wss iordunidif_0 cv iordunidif_0 cv wss iordunidif_1 iordunidif_0 cv fordunidif_0 fordunidif_1 cdif iordunidif_1 cv iordunidif_0 cv iordunidif_0 cv sseq2 rspcev syl6 adantl pm2.61d ralrimiva iordunidif_0 iordunidif_1 fordunidif_0 fordunidif_1 unidif syl $.
$}
$( If ` B ` is smaller than ` A ` , then it equals the intersection of the
       difference.  Exercise 11 in [TakeutiZaring] p. 44.  (Contributed by
       Andrew Salmon, 14-Nov-2011.) $)
${
	$d x A $.
	$d x B $.
	iordintdif_0 $f set x $.
	fordintdif_0 $f class A $.
	fordintdif_1 $f class B $.
	ordintdif $p |- ( ( Ord A /\ Ord B /\ ( A \ B ) =/= (/) ) -> B = |^| ( A \ B ) ) $= fordintdif_0 fordintdif_1 cdif c0 wne fordintdif_0 word fordintdif_1 word fordintdif_0 fordintdif_1 wss wn fordintdif_1 fordintdif_0 fordintdif_1 cdif cint wceq fordintdif_0 fordintdif_1 wss fordintdif_0 fordintdif_1 cdif c0 fordintdif_0 fordintdif_1 ssdif0 necon3bbii fordintdif_0 word fordintdif_1 word fordintdif_0 fordintdif_1 wss wn w3a fordintdif_0 fordintdif_1 cdif cint iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab cint fordintdif_1 fordintdif_0 fordintdif_1 cdif iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab iordintdif_0 fordintdif_0 fordintdif_1 dfdif2 inteqi fordintdif_0 word fordintdif_1 word fordintdif_0 fordintdif_1 wss wn iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab cint fordintdif_1 wceq fordintdif_0 word fordintdif_1 word wa fordintdif_0 fordintdif_1 wss wn fordintdif_1 fordintdif_0 wcel iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab cint fordintdif_1 wceq fordintdif_0 word fordintdif_1 word wa fordintdif_0 fordintdif_1 wss fordintdif_1 fordintdif_0 wcel fordintdif_0 fordintdif_1 ordtri1 con2bid fordintdif_0 word fordintdif_1 word wa fordintdif_1 fordintdif_0 wcel iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab cint fordintdif_1 wceq fordintdif_0 word fordintdif_1 word wa fordintdif_1 fordintdif_0 wcel iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab cint fordintdif_1 iordintdif_0 cv wss iordintdif_0 fordintdif_0 crab cint fordintdif_1 fordintdif_0 word fordintdif_1 word wa iordintdif_0 cv fordintdif_1 wcel wn iordintdif_0 fordintdif_0 crab fordintdif_1 iordintdif_0 cv wss iordintdif_0 fordintdif_0 crab fordintdif_0 word fordintdif_1 word wa iordintdif_0 cv fordintdif_1 wcel wn fordintdif_1 iordintdif_0 cv wss iordintdif_0 fordintdif_0 fordintdif_0 word fordintdif_1 word wa iordintdif_0 cv fordintdif_0 wcel wa fordintdif_1 iordintdif_0 cv wss iordintdif_0 cv fordintdif_1 wcel wn fordintdif_0 word iordintdif_0 cv fordintdif_0 wcel fordintdif_1 word fordintdif_1 iordintdif_0 cv wss iordintdif_0 cv fordintdif_1 wcel wn wb fordintdif_0 word iordintdif_0 cv fordintdif_0 wcel wa iordintdif_0 cv word fordintdif_1 word fordintdif_1 iordintdif_0 cv wss iordintdif_0 cv fordintdif_1 wcel wn wb fordintdif_0 iordintdif_0 cv ordelord fordintdif_1 word iordintdif_0 cv word fordintdif_1 iordintdif_0 cv wss iordintdif_0 cv fordintdif_1 wcel wn wb fordintdif_1 iordintdif_0 cv ordtri1 ancoms sylan an32s bicomd rabbidva inteqd iordintdif_0 fordintdif_1 fordintdif_0 intmin sylan9eq ex sylbird 3impia syl5req syl3an3br $.
$}
$( If a property is true for an ordinal number, then the minimum ordinal
       number for which it is true is smaller or equal.  Theorem Schema 61 of
       [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)
${
	$d x ps $.
	$d x A $.
	fonintss_0 $f wff ph $.
	fonintss_1 $f wff ps $.
	fonintss_2 $f set x $.
	fonintss_3 $f class A $.
	eonintss_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	onintss $p |- ( A e. On -> ( ps -> |^| { x e. On | ph } C_ A ) ) $= fonintss_3 con0 wcel fonintss_1 fonintss_0 fonintss_2 con0 crab cint fonintss_3 wss fonintss_0 fonintss_1 fonintss_2 fonintss_3 con0 eonintss_0 intminss ex $.
$}
$( A way to show that an ordinal number equals the minimum of a collection
       of ordinal numbers: it must be in the collection, and it must not be
       larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)
${
	$d x A $.
	$d x B $.
	foneqmini_0 $f set x $.
	foneqmini_1 $f class A $.
	foneqmini_2 $f class B $.
	oneqmini $p |- ( B C_ On -> ( ( A e. B /\ A. x e. A -. x e. B ) -> A = |^| B ) ) $= foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral wa foneqmini_1 foneqmini_2 cint wss foneqmini_2 cint foneqmini_1 wss wa foneqmini_1 foneqmini_2 cint wceq foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral wa foneqmini_1 foneqmini_2 cint wss foneqmini_2 cint foneqmini_1 wss foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral foneqmini_1 foneqmini_2 cint wss foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel wa foneqmini_1 foneqmini_2 cint wss foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral foneqmini_1 foneqmini_2 cint wss foneqmini_1 foneqmini_0 cv wss foneqmini_0 foneqmini_2 wral foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel wa foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral foneqmini_0 foneqmini_1 foneqmini_2 ssint foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel wa foneqmini_1 foneqmini_0 cv wss foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_2 foneqmini_1 foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel wa foneqmini_0 cv foneqmini_2 wcel foneqmini_1 foneqmini_0 cv wss wi foneqmini_0 cv foneqmini_2 wcel foneqmini_0 cv foneqmini_1 wcel wn wi foneqmini_0 cv foneqmini_1 wcel foneqmini_0 cv foneqmini_2 wcel wn wi foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel wa foneqmini_0 cv foneqmini_2 wcel foneqmini_1 foneqmini_0 cv wss foneqmini_0 cv foneqmini_1 wcel wn foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_0 cv foneqmini_2 wcel foneqmini_1 foneqmini_0 cv wss foneqmini_0 cv foneqmini_1 wcel wn wb foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_0 cv foneqmini_2 wcel wa foneqmini_1 con0 wcel foneqmini_0 cv con0 wcel wa foneqmini_1 foneqmini_0 cv wss foneqmini_0 cv foneqmini_1 wcel wn wb foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_1 con0 wcel foneqmini_0 cv foneqmini_2 wcel foneqmini_0 cv con0 wcel foneqmini_2 con0 foneqmini_1 ssel foneqmini_2 con0 foneqmini_0 cv ssel anim12d foneqmini_1 foneqmini_0 cv ontri1 syl6 expdimp pm5.74d foneqmini_0 cv foneqmini_2 wcel foneqmini_0 cv foneqmini_1 wcel con2b syl6bb ralbidv2 syl5bb biimprd expimpd foneqmini_2 con0 wss foneqmini_1 foneqmini_2 wcel foneqmini_2 cint foneqmini_1 wss foneqmini_0 cv foneqmini_2 wcel wn foneqmini_0 foneqmini_1 wral foneqmini_1 foneqmini_2 wcel foneqmini_2 cint foneqmini_1 wss wi foneqmini_2 con0 wss foneqmini_1 foneqmini_2 intss1 a1i adantrd jcad foneqmini_1 foneqmini_2 cint eqss syl6ibr $.
$}
$( The empty set is an ordinal class.  (Contributed by NM, 11-May-1994.) $)
${
	ord0 $p |- Ord (/) $= c0 word c0 wtr c0 cep wwe tr0 cep we0 c0 df-ord mpbir2an $.
$}
$( The empty set is an ordinal number.  Corollary 7N(b) of [Enderton]
     p. 193.  (Contributed by NM, 17-Sep-1993.) $)
${
	0elon $p |- (/) e. On $= c0 con0 wcel c0 word ord0 c0 0ex elon mpbir $.
$}
$( A non-empty ordinal contains the empty set.  (Contributed by NM,
     25-Nov-1995.) $)
${
	ford0eln0_0 $f class A $.
	ord0eln0 $p |- ( Ord A -> ( (/) e. A <-> A =/= (/) ) ) $= ford0eln0_0 word c0 ford0eln0_0 wcel ford0eln0_0 c0 wne ford0eln0_0 c0 ne0i ford0eln0_0 c0 wne ford0eln0_0 c0 wceq wn ford0eln0_0 word c0 ford0eln0_0 wcel ford0eln0_0 c0 df-ne ford0eln0_0 word ford0eln0_0 c0 wceq c0 ford0eln0_0 wcel ford0eln0_0 word c0 word ford0eln0_0 c0 wceq c0 ford0eln0_0 wcel wo ord0 ford0eln0_0 word c0 word wa ford0eln0_0 c0 wceq c0 ford0eln0_0 wcel wo ford0eln0_0 c0 wcel wn ford0eln0_0 noel ford0eln0_0 word c0 word wa ford0eln0_0 c0 wcel ford0eln0_0 c0 wceq c0 ford0eln0_0 wcel wo ford0eln0_0 c0 ordtri2 con2bid mpbiri mpan2 ord syl5bi impbid2 $.
$}
$( An ordinal number contains zero iff it is nonzero.  (Contributed by NM,
     6-Dec-2004.) $)
${
	fon0eln0_0 $f class A $.
	on0eln0 $p |- ( A e. On -> ( (/) e. A <-> A =/= (/) ) ) $= fon0eln0_0 con0 wcel fon0eln0_0 word c0 fon0eln0_0 wcel fon0eln0_0 c0 wne wb fon0eln0_0 eloni fon0eln0_0 ord0eln0 syl $.
$}
$( An alternate definition of a limit ordinal.  (Contributed by NM,
     4-Nov-2004.) $)
${
	fdflim2_0 $f class A $.
	dflim2 $p |- ( Lim A <-> ( Ord A /\ (/) e. A /\ A = U. A ) ) $= fdflim2_0 wlim fdflim2_0 word fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq w3a fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 fdflim2_0 cuni wceq w3a fdflim2_0 df-lim fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 fdflim2_0 cuni wceq wa wa fdflim2_0 word fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq wa wa fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 fdflim2_0 cuni wceq w3a fdflim2_0 word fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq w3a fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 fdflim2_0 cuni wceq wa fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq wa fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq fdflim2_0 ord0eln0 anbi1d pm5.32i fdflim2_0 word c0 fdflim2_0 wcel fdflim2_0 fdflim2_0 cuni wceq 3anass fdflim2_0 word fdflim2_0 c0 wne fdflim2_0 fdflim2_0 cuni wceq 3anass 3bitr4i bitr4i $.
$}
$( The intersection of the class of ordinal numbers is the empty set.
     (Contributed by NM, 20-Oct-2003.) $)
${
	inton $p |- |^| On = (/) $= c0 con0 wcel con0 cint c0 wceq 0elon con0 int0el ax-mp $.
$}
$( The empty set is not a limit ordinal.  (Contributed by NM, 24-Mar-1995.)
     (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	nlim0 $p |- -. Lim (/) $= c0 wlim c0 word c0 c0 wcel c0 c0 cuni wceq w3a c0 word c0 c0 wcel c0 c0 cuni wceq w3a c0 c0 wcel c0 noel c0 word c0 c0 wcel c0 c0 cuni wceq simp2 mto c0 dflim2 mtbir $.
$}
$( A limit ordinal is ordinal.  (Contributed by NM, 4-May-1995.) $)
${
	flimord_0 $f class A $.
	limord $p |- ( Lim A -> Ord A ) $= flimord_0 wlim flimord_0 word flimord_0 c0 wne flimord_0 flimord_0 cuni wceq flimord_0 df-lim simp1bi $.
$}
$( A limit ordinal is its own supremum (union).  (Contributed by NM,
     4-May-1995.) $)
${
	flimuni_0 $f class A $.
	limuni $p |- ( Lim A -> A = U. A ) $= flimuni_0 wlim flimuni_0 word flimuni_0 c0 wne flimuni_0 flimuni_0 cuni wceq flimuni_0 df-lim simp3bi $.
$}
$( The union of a limit ordinal is a limit ordinal.  (Contributed by NM,
     19-Sep-2006.) $)
${
	flimuni2_0 $f class A $.
	limuni2 $p |- ( Lim A -> Lim U. A ) $= flimuni2_0 wlim flimuni2_0 cuni wlim flimuni2_0 wlim flimuni2_0 flimuni2_0 cuni wceq flimuni2_0 wlim flimuni2_0 cuni wlim wb flimuni2_0 limuni flimuni2_0 flimuni2_0 cuni limeq syl ibi $.
$}
$( A limit ordinal contains the empty set.  (Contributed by NM,
     15-May-1994.) $)
${
	f0ellim_0 $f class A $.
	0ellim $p |- ( Lim A -> (/) e. A ) $= f0ellim_0 wlim c0 f0ellim_0 wcel f0ellim_0 c0 wne f0ellim_0 wlim f0ellim_0 c0 f0ellim_0 c0 wceq f0ellim_0 wlim c0 wlim nlim0 f0ellim_0 c0 limeq mtbiri necon2ai f0ellim_0 wlim f0ellim_0 word c0 f0ellim_0 wcel f0ellim_0 c0 wne wb f0ellim_0 limord f0ellim_0 ord0eln0 syl mpbird $.
$}
$( A limit ordinal class that is also a set is an ordinal number.
     (Contributed by NM, 26-Apr-2004.) $)
${
	flimelon_0 $f class A $.
	flimelon_1 $f class B $.
	limelon $p |- ( ( A e. B /\ Lim A ) -> A e. On ) $= flimelon_0 flimelon_1 wcel flimelon_0 wlim flimelon_0 con0 wcel flimelon_0 wlim flimelon_0 con0 wcel flimelon_0 flimelon_1 wcel flimelon_0 word flimelon_0 limord flimelon_0 flimelon_1 elong syl5ibr imp $.
$}
$( The class of all ordinal numbers in not empty.  (Contributed by NM,
     17-Sep-1995.) $)
${
	onn0 $p |- On =/= (/) $= c0 con0 wcel con0 c0 wne 0elon con0 c0 ne0i ax-mp $.
$}
$( Equality of successors.  (Contributed by NM, 30-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.) $)
${
	fsuceq_0 $f class A $.
	fsuceq_1 $f class B $.
	suceq $p |- ( A = B -> suc A = suc B ) $= fsuceq_0 fsuceq_1 wceq fsuceq_0 fsuceq_0 csn cun fsuceq_1 fsuceq_1 csn cun fsuceq_0 csuc fsuceq_1 csuc fsuceq_0 fsuceq_1 wceq fsuceq_0 fsuceq_1 fsuceq_0 csn fsuceq_1 csn fsuceq_0 fsuceq_1 wceq id fsuceq_0 fsuceq_1 sneq uneq12d fsuceq_0 df-suc fsuceq_1 df-suc 3eqtr4g $.
$}
$( Membership in a successor.  This one-way implication does not require that
     either ` A ` or ` B ` be sets.  (Contributed by NM, 6-Jun-1994.) $)
${
	felsuci_0 $f class A $.
	felsuci_1 $f class B $.
	elsuci $p |- ( A e. suc B -> ( A e. B \/ A = B ) ) $= felsuci_0 felsuci_1 csuc wcel felsuci_0 felsuci_1 wcel felsuci_0 felsuci_1 csn wcel wo felsuci_0 felsuci_1 wcel felsuci_0 felsuci_1 wceq wo felsuci_0 felsuci_1 csuc wcel felsuci_0 felsuci_1 felsuci_1 csn cun wcel felsuci_0 felsuci_1 wcel felsuci_0 felsuci_1 csn wcel wo felsuci_1 csuc felsuci_1 felsuci_1 csn cun felsuci_0 felsuci_1 df-suc eleq2i felsuci_0 felsuci_1 felsuci_1 csn elun bitri felsuci_0 felsuci_1 csn wcel felsuci_0 felsuci_1 wceq felsuci_0 felsuci_1 wcel felsuci_0 felsuci_1 elsni orim2i sylbi $.
$}
$( Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
     (Contributed by NM, 15-Sep-1995.) $)
${
	felsucg_0 $f class A $.
	felsucg_1 $f class B $.
	felsucg_2 $f class V $.
	elsucg $p |- ( A e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $= felsucg_0 felsucg_1 csuc wcel felsucg_0 felsucg_1 wcel felsucg_0 felsucg_1 csn wcel wo felsucg_0 felsucg_2 wcel felsucg_0 felsucg_1 wcel felsucg_0 felsucg_1 wceq wo felsucg_0 felsucg_1 csuc wcel felsucg_0 felsucg_1 felsucg_1 csn cun wcel felsucg_0 felsucg_1 wcel felsucg_0 felsucg_1 csn wcel wo felsucg_1 csuc felsucg_1 felsucg_1 csn cun felsucg_0 felsucg_1 df-suc eleq2i felsucg_0 felsucg_1 felsucg_1 csn elun bitri felsucg_0 felsucg_2 wcel felsucg_0 felsucg_1 csn wcel felsucg_0 felsucg_1 wceq felsucg_0 felsucg_1 wcel felsucg_0 felsucg_1 felsucg_2 elsncg orbi2d syl5bb $.
$}
$( Variant of membership in a successor, requiring that ` B ` rather than
     ` A ` be a set.  (Contributed by NM, 28-Oct-2003.) $)
${
	felsuc2g_0 $f class A $.
	felsuc2g_1 $f class B $.
	felsuc2g_2 $f class V $.
	elsuc2g $p |- ( B e. V -> ( A e. suc B <-> ( A e. B \/ A = B ) ) ) $= felsuc2g_0 felsuc2g_1 csuc wcel felsuc2g_0 felsuc2g_1 felsuc2g_1 csn cun wcel felsuc2g_1 felsuc2g_2 wcel felsuc2g_0 felsuc2g_1 wcel felsuc2g_0 felsuc2g_1 wceq wo felsuc2g_1 csuc felsuc2g_1 felsuc2g_1 csn cun felsuc2g_0 felsuc2g_1 df-suc eleq2i felsuc2g_0 felsuc2g_1 felsuc2g_1 csn cun wcel felsuc2g_0 felsuc2g_1 wcel felsuc2g_0 felsuc2g_1 csn wcel wo felsuc2g_1 felsuc2g_2 wcel felsuc2g_0 felsuc2g_1 wcel felsuc2g_0 felsuc2g_1 wceq wo felsuc2g_0 felsuc2g_1 felsuc2g_1 csn elun felsuc2g_1 felsuc2g_2 wcel felsuc2g_0 felsuc2g_1 csn wcel felsuc2g_0 felsuc2g_1 wceq felsuc2g_0 felsuc2g_1 wcel felsuc2g_0 felsuc2g_1 felsuc2g_2 elsnc2g orbi2d syl5bb syl5bb $.
$}
$( Membership in a successor.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 15-Sep-2003.) $)
${
	felsuc_0 $f class A $.
	felsuc_1 $f class B $.
	eelsuc_0 $e |- A e. _V $.
	elsuc $p |- ( A e. suc B <-> ( A e. B \/ A = B ) ) $= felsuc_0 cvv wcel felsuc_0 felsuc_1 csuc wcel felsuc_0 felsuc_1 wcel felsuc_0 felsuc_1 wceq wo wb eelsuc_0 felsuc_0 felsuc_1 cvv elsucg ax-mp $.
$}
$( Membership in a successor.  (Contributed by NM, 15-Sep-2003.) $)
${
	felsuc2_0 $f class A $.
	felsuc2_1 $f class B $.
	eelsuc2_0 $e |- A e. _V $.
	elsuc2 $p |- ( B e. suc A <-> ( B e. A \/ B = A ) ) $= felsuc2_0 cvv wcel felsuc2_1 felsuc2_0 csuc wcel felsuc2_1 felsuc2_0 wcel felsuc2_1 felsuc2_0 wceq wo wb eelsuc2_0 felsuc2_1 felsuc2_0 cvv elsuc2g ax-mp $.
$}
$( Bound-variable hypothesis builder for successor.  (Contributed by NM,
       15-Sep-2003.) $)
${
	fnfsuc_0 $f set x $.
	fnfsuc_1 $f class A $.
	enfsuc_0 $e |- F/_ x A $.
	nfsuc $p |- F/_ x suc A $= fnfsuc_0 fnfsuc_1 csuc fnfsuc_1 fnfsuc_1 csn cun fnfsuc_1 df-suc fnfsuc_0 fnfsuc_1 fnfsuc_1 csn enfsuc_0 fnfsuc_0 fnfsuc_1 enfsuc_0 nfsn nfun nfcxfr $.
$}
$( Membership in a successor.  (Contributed by NM, 20-Jun-1998.) $)
${
	felelsuc_0 $f class A $.
	felelsuc_1 $f class B $.
	elelsuc $p |- ( A e. B -> A e. suc B ) $= felelsuc_0 felelsuc_1 wcel felelsuc_0 felelsuc_1 csuc wcel felelsuc_0 felelsuc_1 wcel felelsuc_0 felelsuc_1 wceq wo felelsuc_0 felelsuc_1 wcel felelsuc_0 felelsuc_1 wceq orc felelsuc_0 felelsuc_1 felelsuc_1 elsucg mpbird $.
$}
$( Membership of a successor in another class.  (Contributed by NM,
       29-Jun-2004.) $)
${
	$d x y A $.
	$d x B $.
	fsucel_0 $f set x $.
	fsucel_1 $f set y $.
	fsucel_2 $f class A $.
	fsucel_3 $f class B $.
	sucel $p |- ( suc A e. B <-> E. x e. B A. y ( y e. x <-> ( y e. A \/ y = A ) ) ) $= fsucel_2 csuc fsucel_3 wcel fsucel_0 cv fsucel_2 csuc wceq fsucel_0 fsucel_3 wrex fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 wcel fsucel_1 cv fsucel_2 wceq wo wb fsucel_1 wal fsucel_0 fsucel_3 wrex fsucel_0 fsucel_2 csuc fsucel_3 risset fsucel_0 cv fsucel_2 csuc wceq fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 wcel fsucel_1 cv fsucel_2 wceq wo wb fsucel_1 wal fsucel_0 fsucel_3 fsucel_0 cv fsucel_2 csuc wceq fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 csuc wcel wb fsucel_1 wal fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 wcel fsucel_1 cv fsucel_2 wceq wo wb fsucel_1 wal fsucel_1 fsucel_0 cv fsucel_2 csuc dfcleq fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 csuc wcel wb fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 wcel fsucel_1 cv fsucel_2 wceq wo wb fsucel_1 fsucel_1 cv fsucel_2 csuc wcel fsucel_1 cv fsucel_2 wcel fsucel_1 cv fsucel_2 wceq wo fsucel_1 cv fsucel_0 cv wcel fsucel_1 cv fsucel_2 fsucel_1 vex elsuc bibi2i albii bitri rexbii bitri $.
$}
$( The successor of the empty set.  (Contributed by NM, 1-Feb-2005.) $)
${
	suc0 $p |- suc (/) = { (/) } $= c0 csuc c0 c0 csn cun c0 csn c0 cun c0 csn c0 df-suc c0 c0 csn uncom c0 csn un0 3eqtri $.
$}
$( A proper class is its own successor.  (Contributed by NM, 3-Apr-1995.) $)
${
	fsucprc_0 $f class A $.
	sucprc $p |- ( -. A e. _V -> suc A = A ) $= fsucprc_0 cvv wcel wn fsucprc_0 csuc fsucprc_0 c0 cun fsucprc_0 fsucprc_0 cvv wcel wn fsucprc_0 csuc fsucprc_0 fsucprc_0 csn cun fsucprc_0 c0 cun fsucprc_0 df-suc fsucprc_0 cvv wcel wn fsucprc_0 csn c0 wceq fsucprc_0 fsucprc_0 csn cun fsucprc_0 c0 cun wceq fsucprc_0 snprc fsucprc_0 csn c0 fsucprc_0 uneq2 sylbi syl5eq fsucprc_0 un0 syl6eq $.
$}
$( A transitive class is equal to the union of its successor.  Combines
       Theorem 4E of [Enderton] p. 72 and Exercise 6 of [Enderton] p. 73.
       (Contributed by NM, 30-Aug-1993.) $)
${
	funisuc_0 $f class A $.
	eunisuc_0 $e |- A e. _V $.
	unisuc $p |- ( Tr A <-> U. suc A = A ) $= funisuc_0 cuni funisuc_0 wss funisuc_0 cuni funisuc_0 cun funisuc_0 wceq funisuc_0 wtr funisuc_0 csuc cuni funisuc_0 wceq funisuc_0 cuni funisuc_0 ssequn1 funisuc_0 df-tr funisuc_0 csuc cuni funisuc_0 cuni funisuc_0 cun funisuc_0 funisuc_0 csuc cuni funisuc_0 funisuc_0 csn cun cuni funisuc_0 cuni funisuc_0 csn cuni cun funisuc_0 cuni funisuc_0 cun funisuc_0 csuc funisuc_0 funisuc_0 csn cun funisuc_0 df-suc unieqi funisuc_0 funisuc_0 csn uniun funisuc_0 csn cuni funisuc_0 funisuc_0 cuni funisuc_0 eunisuc_0 unisn uneq2i 3eqtri eqeq1i 3bitr4i $.
$}
$( A class is included in its own successor.  Part of Proposition 7.23 of
     [TakeutiZaring] p. 41 (generalized to arbitrary classes).  (Contributed by
     NM, 31-May-1994.) $)
${
	fsssucid_0 $f class A $.
	sssucid $p |- A C_ suc A $= fsssucid_0 fsssucid_0 fsssucid_0 csn cun fsssucid_0 csuc fsssucid_0 fsssucid_0 csn ssun1 fsssucid_0 df-suc sseqtr4i $.
$}
$( Part of Proposition 7.23 of [TakeutiZaring] p. 41 (generalized).
     (Contributed by NM, 25-Mar-1995.)  (Proof shortened by Scott Fenton,
     20-Feb-2012.) $)
${
	fsucidg_0 $f class A $.
	fsucidg_1 $f class V $.
	sucidg $p |- ( A e. V -> A e. suc A ) $= fsucidg_0 fsucidg_1 wcel fsucidg_0 fsucidg_0 csuc wcel fsucidg_0 fsucidg_0 wcel fsucidg_0 fsucidg_0 wceq wo fsucidg_0 fsucidg_0 wceq fsucidg_0 fsucidg_0 wcel fsucidg_0 eqid olci fsucidg_0 fsucidg_0 fsucidg_1 elsucg mpbiri $.
$}
$( A set belongs to its successor.  (Contributed by NM, 22-Jun-1994.)
       (Proof shortened by Alan Sare, 18-Feb-2012.)  (Proof shortened by Scott
       Fenton, 20-Feb-2012.) $)
${
	fsucid_0 $f class A $.
	esucid_0 $e |- A e. _V $.
	sucid $p |- A e. suc A $= fsucid_0 cvv wcel fsucid_0 fsucid_0 csuc wcel esucid_0 fsucid_0 cvv sucidg ax-mp $.
$}
$( No successor is empty.  (Contributed by NM, 3-Apr-1995.) $)
${
	fnsuceq0_0 $f class A $.
	nsuceq0 $p |- suc A =/= (/) $= fnsuceq0_0 csuc c0 wne fnsuceq0_0 csuc c0 wceq wn fnsuceq0_0 cvv wcel fnsuceq0_0 csuc c0 wceq wn fnsuceq0_0 cvv wcel fnsuceq0_0 csuc c0 wceq fnsuceq0_0 c0 wcel fnsuceq0_0 noel fnsuceq0_0 cvv wcel fnsuceq0_0 fnsuceq0_0 csuc wcel fnsuceq0_0 csuc c0 wceq fnsuceq0_0 c0 wcel fnsuceq0_0 cvv sucidg fnsuceq0_0 csuc c0 fnsuceq0_0 eleq2 syl5ibcom mtoi fnsuceq0_0 cvv wcel wn fnsuceq0_0 csuc c0 wceq wn fnsuceq0_0 cvv wcel wn fnsuceq0_0 csuc c0 wceq fnsuceq0_0 cvv wcel fnsuceq0_0 cvv wcel wn fnsuceq0_0 csuc c0 wceq fnsuceq0_0 c0 wceq fnsuceq0_0 cvv wcel fnsuceq0_0 cvv wcel wn fnsuceq0_0 csuc fnsuceq0_0 c0 fnsuceq0_0 sucprc eqeq1d fnsuceq0_0 c0 wceq fnsuceq0_0 cvv wcel c0 cvv wcel 0ex fnsuceq0_0 c0 cvv eleq1 mpbiri syl6bi con3d pm2.43i pm2.61i fnsuceq0_0 csuc c0 df-ne mpbir $.
$}
$( A set belongs to the successor of an equal set.  (Contributed by NM,
       18-Aug-1994.) $)
${
	feqelsuc_0 $f class A $.
	feqelsuc_1 $f class B $.
	eeqelsuc_0 $e |- A e. _V $.
	eqelsuc $p |- ( A = B -> A e. suc B ) $= feqelsuc_0 feqelsuc_1 wceq feqelsuc_0 feqelsuc_0 csuc feqelsuc_1 csuc feqelsuc_0 eeqelsuc_0 sucid feqelsuc_0 feqelsuc_1 suceq syl5eleq $.
$}
$( Inductive definition for the indexed union at a successor.  (Contributed
       by Mario Carneiro, 4-Feb-2013.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
${
	$d A x $.
	$d C x $.
	fiunsuc_0 $f set x $.
	fiunsuc_1 $f class A $.
	fiunsuc_2 $f class B $.
	fiunsuc_3 $f class C $.
	eiunsuc_0 $e |- A e. _V $.
	eiunsuc_1 $e |- ( x = A -> B = C ) $.
	iunsuc $p |- U_ x e. suc A B = ( U_ x e. A B u. C ) $= fiunsuc_0 fiunsuc_1 csuc fiunsuc_2 ciun fiunsuc_0 fiunsuc_1 fiunsuc_1 csn cun fiunsuc_2 ciun fiunsuc_0 fiunsuc_1 fiunsuc_2 ciun fiunsuc_0 fiunsuc_1 csn fiunsuc_2 ciun cun fiunsuc_0 fiunsuc_1 fiunsuc_2 ciun fiunsuc_3 cun fiunsuc_1 csuc fiunsuc_1 fiunsuc_1 csn cun wceq fiunsuc_0 fiunsuc_1 csuc fiunsuc_2 ciun fiunsuc_0 fiunsuc_1 fiunsuc_1 csn cun fiunsuc_2 ciun wceq fiunsuc_1 df-suc fiunsuc_0 fiunsuc_1 csuc fiunsuc_1 fiunsuc_1 csn cun fiunsuc_2 iuneq1 ax-mp fiunsuc_0 fiunsuc_1 fiunsuc_1 csn fiunsuc_2 iunxun fiunsuc_0 fiunsuc_1 csn fiunsuc_2 ciun fiunsuc_3 fiunsuc_0 fiunsuc_1 fiunsuc_2 ciun fiunsuc_0 fiunsuc_1 fiunsuc_2 fiunsuc_3 eiunsuc_0 eiunsuc_1 iunxsn uneq2i 3eqtri $.
$}
$( The successor of a transtive class is transitive.  (Contributed by Alan
       Sare, 11-Apr-2009.) $)
${
	$d z y A $.
	isuctr_0 $f set y $.
	isuctr_1 $f set z $.
	fsuctr_0 $f class A $.
	suctr $p |- ( Tr A -> Tr suc A ) $= fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_0 wal isuctr_1 wal fsuctr_0 csuc wtr fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_1 isuctr_0 fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 wcel isuctr_0 cv fsuctr_0 wceq wo isuctr_1 cv fsuctr_0 csuc wcel isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 csuc wcel isuctr_0 cv fsuctr_0 wcel isuctr_0 cv fsuctr_0 wceq wo isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel simpr isuctr_0 cv fsuctr_0 isuctr_0 vex elsuc sylib fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 wceq isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_0 cv fsuctr_0 wcel isuctr_0 cv fsuctr_0 wceq wo isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 wceq isuctr_1 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 csuc wcel isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 wceq isuctr_1 cv fsuctr_0 wcel isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel simpl isuctr_0 cv fsuctr_0 isuctr_1 cv eleq2 syl5ibcom isuctr_1 cv fsuctr_0 elelsuc syl6 fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_0 cv fsuctr_0 wceq isuctr_1 cv fsuctr_0 csuc wcel wi isuctr_0 cv fsuctr_0 wcel isuctr_0 cv fsuctr_0 wceq wo isuctr_1 cv fsuctr_0 csuc wcel wi wi fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 csuc wcel wa isuctr_0 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 csuc wcel fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 wcel wi isuctr_0 cv fsuctr_0 csuc wcel fsuctr_0 wtr isuctr_1 cv isuctr_0 cv wcel isuctr_0 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 wcel fsuctr_0 isuctr_1 cv isuctr_0 cv trel exp3a adantrd isuctr_1 cv fsuctr_0 elelsuc syl8 isuctr_0 cv fsuctr_0 wcel isuctr_1 cv fsuctr_0 csuc wcel isuctr_0 cv fsuctr_0 wceq jao syl6 mpdi mpdi alrimivv isuctr_1 isuctr_0 fsuctr_0 csuc dftr2 sylibr $.
$}
$( A set whose successor belongs to a transitive class also belongs.
     (Contributed by NM, 5-Sep-2003.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)
${
	ftrsuc_0 $f class A $.
	ftrsuc_1 $f class B $.
	trsuc $p |- ( ( Tr A /\ suc B e. A ) -> B e. A ) $= ftrsuc_0 wtr ftrsuc_1 csuc ftrsuc_0 wcel ftrsuc_1 ftrsuc_0 wcel ftrsuc_1 csuc ftrsuc_0 wcel ftrsuc_1 ftrsuc_1 csuc wcel ftrsuc_1 csuc ftrsuc_0 wcel wa ftrsuc_0 wtr ftrsuc_1 ftrsuc_0 wcel ftrsuc_1 csuc ftrsuc_0 wcel ftrsuc_1 ftrsuc_1 csuc wcel ftrsuc_1 csuc ftrsuc_0 wcel ftrsuc_1 cvv wcel ftrsuc_1 ftrsuc_1 csuc wcel ftrsuc_1 ftrsuc_1 csuc wss ftrsuc_1 csuc ftrsuc_0 wcel ftrsuc_1 cvv wcel ftrsuc_1 sssucid ftrsuc_1 ftrsuc_1 csuc ftrsuc_0 ssexg mpan ftrsuc_1 cvv sucidg syl ancri ftrsuc_0 ftrsuc_1 ftrsuc_1 csuc trel syl5 imp $.
$}
$( Obsolete proof of ~ suctr as of 5-Apr-2016.  The successor of a
       transitive set is transitive.  (Contributed by Scott Fenton,
       21-Feb-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x y A $.
	itrsuc2OLD_0 $f set x $.
	itrsuc2OLD_1 $f set y $.
	ftrsuc2OLD_0 $f class A $.
	trsuc2OLD $p |- ( Tr A -> Tr suc A ) $= ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo wi itrsuc2OLD_1 wal itrsuc2OLD_0 wal ftrsuc2OLD_0 csuc wtr ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo wi itrsuc2OLD_0 itrsuc2OLD_1 itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wa wo ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel andi ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq wa wo itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wa wo itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq wa wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel wo ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 itrsuc2OLD_0 cv eleq2 biimpac orim2i ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq wo itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq wo ftrsuc2OLD_0 itrsuc2OLD_0 cv itrsuc2OLD_1 cv trel itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq orc syl6 itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq wo wi ftrsuc2OLD_0 wtr itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq orc a1i jaod syl5 itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel wa itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wceq itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 ftrsuc2OLD_0 elsn anbi2i orbi2i itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wceq itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 ftrsuc2OLD_0 elsn orbi2i 3imtr4g syl5bi alrimivv ftrsuc2OLD_0 csuc wtr ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wtr itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel wa itrsuc2OLD_0 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel wi itrsuc2OLD_1 wal itrsuc2OLD_0 wal itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo wi itrsuc2OLD_1 wal itrsuc2OLD_0 wal ftrsuc2OLD_0 csuc ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wceq ftrsuc2OLD_0 csuc wtr ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wtr wb ftrsuc2OLD_0 df-suc ftrsuc2OLD_0 csuc ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun treq ax-mp itrsuc2OLD_0 itrsuc2OLD_1 ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun dftr2 itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel wa itrsuc2OLD_0 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel wi itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo wi itrsuc2OLD_0 itrsuc2OLD_1 itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel wa itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo wa itrsuc2OLD_0 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 wcel itrsuc2OLD_0 cv ftrsuc2OLD_0 csn wcel wo itrsuc2OLD_1 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn cun wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 csn wcel wo itrsuc2OLD_0 cv itrsuc2OLD_1 cv wcel itrsuc2OLD_1 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn elun anbi2i itrsuc2OLD_0 cv ftrsuc2OLD_0 ftrsuc2OLD_0 csn elun imbi12i 2albii 3bitri sylibr $.
$}
$( A member of the successor of a transitive class is a subclass of it.
     (Contributed by NM, 4-Oct-2003.) $)
${
	ftrsucss_0 $f class A $.
	ftrsucss_1 $f class B $.
	trsucss $p |- ( Tr A -> ( B e. suc A -> B C_ A ) ) $= ftrsucss_1 ftrsucss_0 csuc wcel ftrsucss_1 ftrsucss_0 wcel ftrsucss_1 ftrsucss_0 wceq wo ftrsucss_0 wtr ftrsucss_1 ftrsucss_0 wss ftrsucss_1 ftrsucss_0 elsuci ftrsucss_0 wtr ftrsucss_1 ftrsucss_0 wcel ftrsucss_1 ftrsucss_0 wss ftrsucss_1 ftrsucss_0 wceq ftrsucss_0 ftrsucss_1 trss ftrsucss_1 ftrsucss_0 wceq ftrsucss_1 ftrsucss_0 wss wi ftrsucss_0 wtr ftrsucss_1 ftrsucss_0 eqimss a1i jaod syl5 $.
$}
$( A subset of an ordinal belongs to its successor.  (Contributed by NM,
     28-Nov-2003.) $)
${
	fordsssuc_0 $f class A $.
	fordsssuc_1 $f class B $.
	ordsssuc $p |- ( ( A e. On /\ Ord B ) -> ( A C_ B <-> A e. suc B ) ) $= fordsssuc_0 con0 wcel fordsssuc_1 word wa fordsssuc_0 fordsssuc_1 wss fordsssuc_0 fordsssuc_1 wcel fordsssuc_0 fordsssuc_1 wceq wo fordsssuc_0 fordsssuc_1 csuc wcel fordsssuc_0 con0 wcel fordsssuc_0 word fordsssuc_1 word fordsssuc_0 fordsssuc_1 wss fordsssuc_0 fordsssuc_1 wcel fordsssuc_0 fordsssuc_1 wceq wo wb fordsssuc_0 eloni fordsssuc_0 fordsssuc_1 ordsseleq sylan fordsssuc_0 con0 wcel fordsssuc_0 fordsssuc_1 csuc wcel fordsssuc_0 fordsssuc_1 wcel fordsssuc_0 fordsssuc_1 wceq wo wb fordsssuc_1 word fordsssuc_0 fordsssuc_1 con0 elsucg adantr bitr4d $.
$}
$( A subset of an ordinal number belongs to its successor.  (Contributed by
     NM, 15-Sep-1995.) $)
${
	fonsssuc_0 $f class A $.
	fonsssuc_1 $f class B $.
	onsssuc $p |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $= fonsssuc_1 con0 wcel fonsssuc_0 con0 wcel fonsssuc_1 word fonsssuc_0 fonsssuc_1 wss fonsssuc_0 fonsssuc_1 csuc wcel wb fonsssuc_1 eloni fonsssuc_0 fonsssuc_1 ordsssuc sylan2 $.
$}
$( An ordinal subset of an ordinal number belongs to its successor.
     (Contributed by NM, 1-Feb-2005.)  (Proof shortened by Andrew Salmon,
     12-Aug-2011.) $)
${
	fordsssuc2_0 $f class A $.
	fordsssuc2_1 $f class B $.
	ordsssuc2 $p |- ( ( Ord A /\ B e. On ) -> ( A C_ B <-> A e. suc B ) ) $= fordsssuc2_0 cvv wcel fordsssuc2_0 word fordsssuc2_1 con0 wcel wa fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_0 fordsssuc2_1 csuc wcel wb wi fordsssuc2_0 cvv wcel fordsssuc2_0 word fordsssuc2_1 con0 wcel wa fordsssuc2_0 con0 wcel fordsssuc2_1 con0 wcel wa fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_0 fordsssuc2_1 csuc wcel wb fordsssuc2_0 cvv wcel fordsssuc2_0 word fordsssuc2_0 con0 wcel fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel fordsssuc2_0 con0 wcel fordsssuc2_0 word fordsssuc2_0 cvv elong biimprd anim1d fordsssuc2_0 fordsssuc2_1 onsssuc syl6 fordsssuc2_0 cvv wcel wn fordsssuc2_1 con0 wcel fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_0 fordsssuc2_1 csuc wcel wb fordsssuc2_0 word fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel wn fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_0 fordsssuc2_1 csuc wcel wb fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel wn wa fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel wi wn fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_0 fordsssuc2_1 csuc wcel wb fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel annim fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel wi fordsssuc2_0 fordsssuc2_1 csuc wcel fordsssuc2_0 fordsssuc2_1 wss fordsssuc2_1 con0 wcel fordsssuc2_0 cvv wcel fordsssuc2_0 fordsssuc2_1 con0 ssexg ex fordsssuc2_0 fordsssuc2_1 csuc wcel fordsssuc2_0 cvv wcel fordsssuc2_1 con0 wcel fordsssuc2_0 fordsssuc2_1 csuc elex a1d pm5.21ni sylbi expcom adantld pm2.61i $.
$}
$( When its successor is subtracted from a class of ordinal numbers, an
       ordinal number is less than the minimum of the resulting subclass.
       (Contributed by NM, 1-Dec-2003.) $)
${
	$d x A $.
	$d x B $.
	ionmindif_0 $f set x $.
	fonmindif_0 $f class A $.
	fonmindif_1 $f class B $.
	onmindif $p |- ( ( A C_ On /\ B e. On ) -> B e. |^| ( A \ suc B ) ) $= fonmindif_0 con0 wss fonmindif_1 con0 wcel wa fonmindif_1 fonmindif_0 fonmindif_1 csuc cdif cint wcel fonmindif_1 ionmindif_0 cv wcel ionmindif_0 fonmindif_0 fonmindif_1 csuc cdif wral fonmindif_0 con0 wss fonmindif_1 con0 wcel wa fonmindif_1 ionmindif_0 cv wcel ionmindif_0 fonmindif_0 fonmindif_1 csuc cdif ionmindif_0 cv fonmindif_0 fonmindif_1 csuc cdif wcel ionmindif_0 cv fonmindif_0 wcel ionmindif_0 cv fonmindif_1 csuc wcel wn wa fonmindif_0 con0 wss fonmindif_1 con0 wcel wa fonmindif_1 ionmindif_0 cv wcel ionmindif_0 cv fonmindif_0 fonmindif_1 csuc eldif fonmindif_0 con0 wss fonmindif_1 con0 wcel ionmindif_0 cv fonmindif_0 wcel ionmindif_0 cv fonmindif_1 csuc wcel wn fonmindif_1 ionmindif_0 cv wcel fonmindif_0 con0 wss ionmindif_0 cv fonmindif_0 wcel fonmindif_1 con0 wcel ionmindif_0 cv fonmindif_1 csuc wcel wn fonmindif_1 ionmindif_0 cv wcel wi fonmindif_0 con0 wss ionmindif_0 cv fonmindif_0 wcel fonmindif_1 con0 wcel ionmindif_0 cv fonmindif_1 csuc wcel wn fonmindif_1 ionmindif_0 cv wcel wi fonmindif_0 con0 wss ionmindif_0 cv fonmindif_0 wcel wa fonmindif_1 con0 wcel wa ionmindif_0 cv fonmindif_1 csuc wcel wn fonmindif_1 ionmindif_0 cv wcel fonmindif_0 con0 wss ionmindif_0 cv fonmindif_0 wcel wa ionmindif_0 cv con0 wcel fonmindif_1 con0 wcel ionmindif_0 cv fonmindif_1 csuc wcel wn fonmindif_1 ionmindif_0 cv wcel wb fonmindif_0 con0 ionmindif_0 cv ssel2 ionmindif_0 cv con0 wcel fonmindif_1 con0 wcel wa fonmindif_1 ionmindif_0 cv wcel ionmindif_0 cv fonmindif_1 csuc wcel ionmindif_0 cv con0 wcel fonmindif_1 con0 wcel wa ionmindif_0 cv fonmindif_1 wss fonmindif_1 ionmindif_0 cv wcel wn ionmindif_0 cv fonmindif_1 csuc wcel ionmindif_0 cv fonmindif_1 ontri1 ionmindif_0 cv fonmindif_1 onsssuc bitr3d con1bid sylan biimpd exp31 com23 imp4b syl5bi ralrimiv fonmindif_1 con0 wcel fonmindif_1 fonmindif_0 fonmindif_1 csuc cdif cint wcel fonmindif_1 ionmindif_0 cv wcel ionmindif_0 fonmindif_0 fonmindif_1 csuc cdif wral wb fonmindif_0 con0 wss ionmindif_0 fonmindif_1 fonmindif_0 fonmindif_1 csuc cdif con0 elintg adantl mpbird $.
$}
$( There is no set between an ordinal class and its successor.  Generalized
     Proposition 7.25 of [TakeutiZaring] p. 41.  (Contributed by NM,
     21-Jun-1998.) $)
${
	fordnbtwn_0 $f class A $.
	fordnbtwn_1 $f class B $.
	ordnbtwn $p |- ( Ord A -> -. ( A e. B /\ B e. suc A ) ) $= fordnbtwn_0 word fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_0 wcel wo fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 csuc wcel wa fordnbtwn_0 word fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa wn fordnbtwn_0 fordnbtwn_0 wcel wn fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_0 wcel wo wn fordnbtwn_0 fordnbtwn_1 ordn2lp fordnbtwn_0 ordirr fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_0 wcel ioran sylanbrc fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 csuc wcel wa fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wceq wa wo fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_0 wcel wo fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 csuc wcel wa fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel fordnbtwn_1 fordnbtwn_0 wceq wo wa fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wceq wa wo fordnbtwn_1 fordnbtwn_0 csuc wcel fordnbtwn_1 fordnbtwn_0 wcel fordnbtwn_1 fordnbtwn_0 wceq wo fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 elsuci anim2i fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel fordnbtwn_1 fordnbtwn_0 wceq andi sylib fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wceq wa fordnbtwn_0 fordnbtwn_0 wcel fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_1 fordnbtwn_0 wcel wa fordnbtwn_1 fordnbtwn_0 wceq fordnbtwn_0 fordnbtwn_1 wcel fordnbtwn_0 fordnbtwn_0 wcel fordnbtwn_1 fordnbtwn_0 fordnbtwn_0 eleq2 biimpac orim2i syl nsyl $.
$}
$( There is no set between an ordinal number and its successor.  Proposition
     7.25 of [TakeutiZaring] p. 41.  (Contributed by NM, 9-Jun-1994.) $)
${
	fonnbtwn_0 $f class A $.
	fonnbtwn_1 $f class B $.
	onnbtwn $p |- ( A e. On -> -. ( A e. B /\ B e. suc A ) ) $= fonnbtwn_0 con0 wcel fonnbtwn_0 word fonnbtwn_0 fonnbtwn_1 wcel fonnbtwn_1 fonnbtwn_0 csuc wcel wa wn fonnbtwn_0 eloni fonnbtwn_0 fonnbtwn_1 ordnbtwn syl $.
$}
$( A set whose successor is a subset of another class is a member of that
     class.  (Contributed by NM, 16-Sep-1995.) $)
${
	fsucssel_0 $f class A $.
	fsucssel_1 $f class B $.
	fsucssel_2 $f class V $.
	sucssel $p |- ( A e. V -> ( suc A C_ B -> A e. B ) ) $= fsucssel_0 fsucssel_2 wcel fsucssel_0 fsucssel_0 csuc wcel fsucssel_0 csuc fsucssel_1 wss fsucssel_0 fsucssel_1 wcel fsucssel_0 fsucssel_2 sucidg fsucssel_0 csuc fsucssel_1 fsucssel_0 ssel syl5com $.
$}
$( Ordinal derived from its successor.  (Contributed by NM, 20-May-1998.) $)
${
	forddif_0 $f class A $.
	orddif $p |- ( Ord A -> A = ( suc A \ { A } ) ) $= forddif_0 word forddif_0 forddif_0 csn cin c0 wceq forddif_0 forddif_0 csuc forddif_0 csn cdif wceq forddif_0 orddisj forddif_0 forddif_0 csn cin c0 wceq forddif_0 forddif_0 forddif_0 csn cdif wceq forddif_0 forddif_0 csuc forddif_0 csn cdif wceq forddif_0 forddif_0 csn disj3 forddif_0 csuc forddif_0 csn cdif forddif_0 forddif_0 csn cdif forddif_0 forddif_0 csuc forddif_0 csn cdif forddif_0 forddif_0 csn cun forddif_0 csn cdif forddif_0 forddif_0 csn cdif forddif_0 csuc forddif_0 forddif_0 csn cun forddif_0 csn forddif_0 df-suc difeq1i forddif_0 forddif_0 csn difun2 eqtri eqeq2i bitr4i sylib $.
$}
$( An ordinal class includes its union.  (Contributed by NM, 13-Sep-2003.) $)
${
	forduniss_0 $f class A $.
	orduniss $p |- ( Ord A -> U. A C_ A ) $= forduniss_0 word forduniss_0 wtr forduniss_0 cuni forduniss_0 wss forduniss_0 ordtr forduniss_0 df-tr sylib $.
$}
$( A trichotomy law for ordinal classes.  (Contributed by NM, 13-Sep-2003.)
     (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)
${
	fordtri2or_0 $f class A $.
	fordtri2or_1 $f class B $.
	ordtri2or $p |- ( ( Ord A /\ Ord B ) -> ( A e. B \/ B C_ A ) ) $= fordtri2or_0 word fordtri2or_1 word wa fordtri2or_0 fordtri2or_1 wcel fordtri2or_1 fordtri2or_0 wss fordtri2or_0 word fordtri2or_1 word wa fordtri2or_1 fordtri2or_0 wss fordtri2or_0 fordtri2or_1 wcel wn fordtri2or_1 word fordtri2or_0 word fordtri2or_1 fordtri2or_0 wss fordtri2or_0 fordtri2or_1 wcel wn wb fordtri2or_1 fordtri2or_0 ordtri1 ancoms biimprd orrd $.
$}
$( A trichotomy law for ordinal classes.  (Contributed by NM, 2-Nov-2003.) $)
${
	fordtri2or2_0 $f class A $.
	fordtri2or2_1 $f class B $.
	ordtri2or2 $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B \/ B C_ A ) ) $= fordtri2or2_0 word fordtri2or2_1 word wa fordtri2or2_0 fordtri2or2_1 wcel fordtri2or2_1 fordtri2or2_0 wss wo fordtri2or2_0 fordtri2or2_1 wss fordtri2or2_1 fordtri2or2_0 wss wo fordtri2or2_0 fordtri2or2_1 ordtri2or fordtri2or2_1 word fordtri2or2_0 fordtri2or2_1 wcel fordtri2or2_1 fordtri2or2_0 wss wo fordtri2or2_0 fordtri2or2_1 wss fordtri2or2_1 fordtri2or2_0 wss wo wi fordtri2or2_0 word fordtri2or2_1 word fordtri2or2_0 fordtri2or2_1 wcel fordtri2or2_0 fordtri2or2_1 wss fordtri2or2_1 fordtri2or2_0 wss fordtri2or2_1 word fordtri2or2_0 fordtri2or2_1 wcel fordtri2or2_0 fordtri2or2_1 wss fordtri2or2_1 fordtri2or2_0 ordelss ex orim1d adantl mpd $.
$}
$( A consequence of total ordering for ordinal classes.  Similar to
     ~ ordtri2or2 .  (Contributed by David Moews, 1-May-2017.) $)
${
	fordtri2or3_0 $f class A $.
	fordtri2or3_1 $f class B $.
	ordtri2or3 $p |- ( ( Ord A /\ Ord B ) -> ( A = ( A i^i B ) \/ B = ( A i^i B ) ) ) $= fordtri2or3_0 word fordtri2or3_1 word wa fordtri2or3_0 fordtri2or3_1 wss fordtri2or3_1 fordtri2or3_0 wss wo fordtri2or3_0 fordtri2or3_0 fordtri2or3_1 cin wceq fordtri2or3_1 fordtri2or3_0 fordtri2or3_1 cin wceq wo fordtri2or3_0 fordtri2or3_1 ordtri2or2 fordtri2or3_0 fordtri2or3_1 wss fordtri2or3_0 fordtri2or3_0 fordtri2or3_1 cin wceq fordtri2or3_1 fordtri2or3_0 wss fordtri2or3_1 fordtri2or3_0 fordtri2or3_1 cin wceq fordtri2or3_0 fordtri2or3_1 dfss fordtri2or3_1 fordtri2or3_0 dfss5 orbi12i sylib $.
$}
$( The intersection of two ordinal classes is an element of a third if and
     only if either one of them is.  (Contributed by David Moews,
     1-May-2017.) $)
${
	fordelinel_0 $f class A $.
	fordelinel_1 $f class B $.
	fordelinel_2 $f class C $.
	ordelinel $p |- ( ( Ord A /\ Ord B /\ Ord C ) -> ( ( A i^i B ) e. C <-> ( A e. C \/ B e. C ) ) ) $= fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel wo fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_0 fordelinel_1 cin wceq fordelinel_1 fordelinel_0 fordelinel_1 cin wceq wo fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel wo wi fordelinel_0 word fordelinel_1 word fordelinel_0 fordelinel_0 fordelinel_1 cin wceq fordelinel_1 fordelinel_0 fordelinel_1 cin wceq wo fordelinel_2 word fordelinel_0 fordelinel_1 ordtri2or3 3adant3 fordelinel_0 fordelinel_0 fordelinel_1 cin wceq fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel wo wi fordelinel_1 fordelinel_0 fordelinel_1 cin wceq fordelinel_0 fordelinel_0 fordelinel_1 cin wceq fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel wo fordelinel_0 fordelinel_0 fordelinel_1 cin fordelinel_2 eleq1 fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel orc syl6bir fordelinel_1 fordelinel_0 fordelinel_1 cin wceq fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel wo fordelinel_1 fordelinel_0 fordelinel_1 cin fordelinel_2 eleq1 fordelinel_1 fordelinel_2 wcel fordelinel_0 fordelinel_2 wcel olc syl6bir jaoi syl fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_2 wcel fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_1 fordelinel_2 wcel fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_1 cin fordelinel_0 wss fordelinel_0 fordelinel_2 wcel fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_1 inss1 fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_1 cin word fordelinel_2 word wa fordelinel_0 fordelinel_1 cin fordelinel_0 wss fordelinel_0 fordelinel_2 wcel wa fordelinel_0 fordelinel_1 cin fordelinel_2 wcel wi fordelinel_0 word fordelinel_1 word fordelinel_2 word fordelinel_0 fordelinel_1 cin word fordelinel_2 word wa fordelinel_0 word fordelinel_1 word wa fordelinel_0 fordelinel_1 cin word fordelinel_2 word fordelinel_0 fordelinel_1 ordin anim1i 3impa fordelinel_0 fordelinel_1 cin fordelinel_0 fordelinel_2 ordtr2 syl mpani fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_1 cin fordelinel_1 wss fordelinel_1 fordelinel_2 wcel fordelinel_0 fordelinel_1 cin fordelinel_2 wcel fordelinel_0 fordelinel_1 inss2 fordelinel_0 word fordelinel_1 word fordelinel_2 word w3a fordelinel_0 fordelinel_1 cin word fordelinel_2 word wa fordelinel_0 fordelinel_1 cin fordelinel_1 wss fordelinel_1 fordelinel_2 wcel wa fordelinel_0 fordelinel_1 cin fordelinel_2 wcel wi fordelinel_0 word fordelinel_1 word fordelinel_2 word fordelinel_0 fordelinel_1 cin word fordelinel_2 word wa fordelinel_0 word fordelinel_1 word wa fordelinel_0 fordelinel_1 cin word fordelinel_2 word fordelinel_0 fordelinel_1 ordin anim1i 3impa fordelinel_0 fordelinel_1 cin fordelinel_1 fordelinel_2 ordtr2 syl mpani jaod impbid $.
$}
$( Property of a subclass of the maximum (i.e. union) of two ordinals.
     (Contributed by NM, 28-Nov-2003.) $)
${
	fordssun_0 $f class A $.
	fordssun_1 $f class B $.
	fordssun_2 $f class C $.
	ordssun $p |- ( ( Ord B /\ Ord C ) -> ( A C_ ( B u. C ) <-> ( A C_ B \/ A C_ C ) ) ) $= fordssun_1 word fordssun_2 word wa fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss wo fordssun_1 word fordssun_2 word wa fordssun_1 fordssun_2 wss fordssun_2 fordssun_1 wss wo fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss wo wi fordssun_1 fordssun_2 ordtri2or2 fordssun_1 fordssun_2 wss fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss wo wi fordssun_2 fordssun_1 wss fordssun_1 fordssun_2 wss fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_2 wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss wo fordssun_1 fordssun_2 wss fordssun_1 fordssun_2 cun fordssun_2 wceq fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_2 wss wb fordssun_1 fordssun_2 ssequn1 fordssun_1 fordssun_2 cun fordssun_2 fordssun_0 sseq2 sylbi fordssun_0 fordssun_2 wss fordssun_0 fordssun_1 wss olc syl6bi fordssun_2 fordssun_1 wss fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss wo fordssun_2 fordssun_1 wss fordssun_1 fordssun_2 cun fordssun_1 wceq fordssun_0 fordssun_1 fordssun_2 cun wss fordssun_0 fordssun_1 wss wb fordssun_2 fordssun_1 ssequn2 fordssun_1 fordssun_2 cun fordssun_1 fordssun_0 sseq2 sylbi fordssun_0 fordssun_1 wss fordssun_0 fordssun_2 wss orc syl6bi jaoi syl fordssun_0 fordssun_1 fordssun_2 ssun impbid1 $.
$}
$( The maximum (i.e. union) of two ordinals is either one or the other.
     Similar to Exercise 14 of [TakeutiZaring] p. 40.  (Contributed by NM,
     28-Nov-2003.) $)
${
	fordequn_0 $f class A $.
	fordequn_1 $f class B $.
	fordequn_2 $f class C $.
	ordequn $p |- ( ( Ord B /\ Ord C ) -> ( A = ( B u. C ) -> ( A = B \/ A = C ) ) ) $= fordequn_1 word fordequn_2 word wa fordequn_1 fordequn_2 wss fordequn_2 fordequn_1 wss wo fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_1 wceq fordequn_0 fordequn_2 wceq wo wi fordequn_1 fordequn_2 ordtri2or2 fordequn_1 fordequn_2 wss fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_1 wceq fordequn_0 fordequn_2 wceq wo wi fordequn_2 fordequn_1 wss fordequn_1 fordequn_2 wss fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_2 wceq fordequn_0 fordequn_1 wceq fordequn_0 fordequn_2 wceq wo fordequn_1 fordequn_2 wss fordequn_1 fordequn_2 cun fordequn_2 wceq fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_2 wceq wb fordequn_1 fordequn_2 ssequn1 fordequn_1 fordequn_2 cun fordequn_2 fordequn_0 eqeq2 sylbi fordequn_0 fordequn_2 wceq fordequn_0 fordequn_1 wceq olc syl6bi fordequn_2 fordequn_1 wss fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_1 wceq fordequn_0 fordequn_1 wceq fordequn_0 fordequn_2 wceq wo fordequn_2 fordequn_1 wss fordequn_1 fordequn_2 cun fordequn_1 wceq fordequn_0 fordequn_1 fordequn_2 cun wceq fordequn_0 fordequn_1 wceq wb fordequn_2 fordequn_1 ssequn2 fordequn_1 fordequn_2 cun fordequn_1 fordequn_0 eqeq2 sylbi fordequn_0 fordequn_1 wceq fordequn_0 fordequn_2 wceq orc syl6bi jaoi syl $.
$}
$( The maximum (i.e. union) of two ordinals is ordinal.  Exercise 12 of
     [TakeutiZaring] p. 40.  (Contributed by NM, 28-Nov-2003.) $)
${
	fordun_0 $f class A $.
	fordun_1 $f class B $.
	ordun $p |- ( ( Ord A /\ Ord B ) -> Ord ( A u. B ) ) $= fordun_0 word fordun_1 word wa fordun_0 fordun_1 cun fordun_0 wceq fordun_0 fordun_1 cun fordun_1 wceq wo fordun_0 fordun_1 cun word fordun_0 word fordun_1 word wa fordun_0 fordun_1 cun fordun_0 fordun_1 cun wceq fordun_0 fordun_1 cun fordun_0 wceq fordun_0 fordun_1 cun fordun_1 wceq wo fordun_0 fordun_1 cun eqid fordun_0 fordun_1 cun fordun_0 fordun_1 ordequn mpi fordun_0 word fordun_0 fordun_1 cun fordun_0 wceq fordun_0 fordun_1 cun word fordun_1 word fordun_0 fordun_1 cun fordun_1 wceq fordun_0 fordun_1 cun fordun_0 wceq fordun_0 fordun_1 cun word fordun_0 word fordun_0 fordun_1 cun fordun_0 ordeq biimprcd fordun_0 fordun_1 cun fordun_1 wceq fordun_0 fordun_1 cun word fordun_1 word fordun_0 fordun_1 cun fordun_1 ordeq biimprcd jaao mpd $.
$}
$( A subclass relationship for union and successor of ordinal classes.
       (Contributed by NM, 28-Nov-2003.) $)
${
	$d x A $.
	$d x B $.
	iordunisssuc_0 $f set x $.
	fordunisssuc_0 $f class A $.
	fordunisssuc_1 $f class B $.
	ordunisssuc $p |- ( ( A C_ On /\ Ord B ) -> ( U. A C_ B <-> A C_ suc B ) ) $= fordunisssuc_0 con0 wss fordunisssuc_1 word wa iordunisssuc_0 cv fordunisssuc_1 wss iordunisssuc_0 fordunisssuc_0 wral iordunisssuc_0 cv fordunisssuc_1 csuc wcel iordunisssuc_0 fordunisssuc_0 wral fordunisssuc_0 cuni fordunisssuc_1 wss fordunisssuc_0 fordunisssuc_1 csuc wss fordunisssuc_0 con0 wss fordunisssuc_1 word wa iordunisssuc_0 cv fordunisssuc_1 wss iordunisssuc_0 cv fordunisssuc_1 csuc wcel iordunisssuc_0 fordunisssuc_0 fordunisssuc_0 con0 wss iordunisssuc_0 cv fordunisssuc_0 wcel fordunisssuc_1 word iordunisssuc_0 cv fordunisssuc_1 wss iordunisssuc_0 cv fordunisssuc_1 csuc wcel wb fordunisssuc_0 con0 wss iordunisssuc_0 cv fordunisssuc_0 wcel wa iordunisssuc_0 cv con0 wcel fordunisssuc_1 word iordunisssuc_0 cv fordunisssuc_1 wss iordunisssuc_0 cv fordunisssuc_1 csuc wcel wb fordunisssuc_0 con0 iordunisssuc_0 cv ssel2 iordunisssuc_0 cv fordunisssuc_1 ordsssuc sylan an32s ralbidva iordunisssuc_0 fordunisssuc_0 fordunisssuc_1 unissb iordunisssuc_0 fordunisssuc_0 fordunisssuc_1 csuc dfss3 3bitr4g $.
$}
$( The successor operation behaves like a one-to-one function.  Compare
     Exercise 16 of [Enderton] p. 194.  (Contributed by NM, 3-Sep-2003.) $)
${
	fsuc11_0 $f class A $.
	fsuc11_1 $f class B $.
	suc11 $p |- ( ( A e. On /\ B e. On ) -> ( suc A = suc B <-> A = B ) ) $= fsuc11_0 con0 wcel fsuc11_1 con0 wcel wa fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_0 fsuc11_1 wceq fsuc11_0 con0 wcel fsuc11_1 con0 wcel wa fsuc11_0 fsuc11_1 wcel wn fsuc11_1 fsuc11_0 wcel wn wo fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_0 fsuc11_1 wceq wi fsuc11_0 con0 wcel fsuc11_0 fsuc11_1 wcel wn fsuc11_1 fsuc11_0 wcel wn wo fsuc11_1 con0 wcel fsuc11_0 con0 wcel fsuc11_0 word fsuc11_0 fsuc11_1 wcel wn fsuc11_1 fsuc11_0 wcel wn wo fsuc11_0 eloni fsuc11_0 word fsuc11_0 fsuc11_1 wcel fsuc11_1 fsuc11_0 wcel wa wn fsuc11_0 fsuc11_1 wcel wn fsuc11_1 fsuc11_0 wcel wn wo fsuc11_0 fsuc11_1 ordn2lp fsuc11_0 fsuc11_1 wcel fsuc11_1 fsuc11_0 wcel ianor sylib syl adantr fsuc11_0 con0 wcel fsuc11_0 fsuc11_1 wcel wn fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_0 fsuc11_1 wceq wi fsuc11_1 con0 wcel fsuc11_1 fsuc11_0 wcel wn fsuc11_0 con0 wcel fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_0 fsuc11_1 csuc wcel fsuc11_0 fsuc11_1 wcel wn fsuc11_0 fsuc11_1 wceq fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_0 csuc fsuc11_1 csuc wss fsuc11_0 con0 wcel fsuc11_0 fsuc11_1 csuc wcel fsuc11_0 csuc fsuc11_1 csuc eqimss fsuc11_0 fsuc11_1 csuc con0 sucssel syl5 fsuc11_0 fsuc11_1 csuc wcel fsuc11_0 fsuc11_1 wcel wn fsuc11_0 fsuc11_1 wceq fsuc11_0 fsuc11_1 csuc wcel fsuc11_0 fsuc11_1 wcel fsuc11_0 fsuc11_1 wceq fsuc11_0 fsuc11_1 elsuci ord com12 syl9 fsuc11_1 con0 wcel fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_1 fsuc11_0 csuc wcel fsuc11_1 fsuc11_0 wcel wn fsuc11_0 fsuc11_1 wceq fsuc11_0 csuc fsuc11_1 csuc wceq fsuc11_1 csuc fsuc11_0 csuc wss fsuc11_1 con0 wcel fsuc11_1 fsuc11_0 csuc wcel fsuc11_1 csuc fsuc11_0 csuc eqimss2 fsuc11_1 fsuc11_0 csuc con0 sucssel syl5 fsuc11_1 fsuc11_0 wcel wn fsuc11_1 fsuc11_0 csuc wcel fsuc11_1 fsuc11_0 wceq fsuc11_0 fsuc11_1 wceq fsuc11_1 fsuc11_0 csuc wcel fsuc11_1 fsuc11_0 wcel wn fsuc11_1 fsuc11_0 wceq fsuc11_1 fsuc11_0 csuc wcel fsuc11_1 fsuc11_0 wcel fsuc11_1 fsuc11_0 wceq fsuc11_1 fsuc11_0 elsuci ord com12 fsuc11_1 fsuc11_0 eqcom syl6ib syl9 jaao mpd fsuc11_0 fsuc11_1 suceq impbid1 $.
$}
$( An ordinal number is an ordinal class.  (Contributed by NM,
       11-Jun-1994.) $)
${
	fonordi_0 $f class A $.
	eonordi_0 $e |- A e. On $.
	onordi $p |- Ord A $= fonordi_0 con0 wcel fonordi_0 word eonordi_0 fonordi_0 eloni ax-mp $.
$}
$( An ordinal number is a transitive class.  (Contributed by NM,
       11-Jun-1994.) $)
${
	fontrci_0 $f class A $.
	eontrci_0 $e |- A e. On $.
	ontrci $p |- Tr A $= fontrci_0 word fontrci_0 wtr fontrci_0 eontrci_0 onordi fontrci_0 ordtr ax-mp $.
$}
$( An ordinal number is not a member of itself.  Theorem 7M(c) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)
${
	fonirri_0 $f class A $.
	eonirri_0 $e |- A e. On $.
	onirri $p |- -. A e. A $= fonirri_0 word fonirri_0 fonirri_0 wcel wn fonirri_0 eonirri_0 onordi fonirri_0 ordirr ax-mp $.
$}
$( A member of an ordinal number is an ordinal number.  Theorem 7M(a) of
       [Enderton] p. 192.  (Contributed by NM, 11-Jun-1994.) $)
${
	foneli_0 $f class A $.
	foneli_1 $f class B $.
	eoneli_0 $e |- A e. On $.
	oneli $p |- ( B e. A -> B e. On ) $= foneli_0 con0 wcel foneli_1 foneli_0 wcel foneli_1 con0 wcel eoneli_0 foneli_0 foneli_1 onelon mpan $.
$}
$( A member of an ordinal number is a subset of it.  (Contributed by NM,
       11-Aug-1994.) $)
${
	fonelssi_0 $f class A $.
	fonelssi_1 $f class B $.
	eonelssi_0 $e |- A e. On $.
	onelssi $p |- ( B e. A -> B C_ A ) $= fonelssi_0 con0 wcel fonelssi_1 fonelssi_0 wcel fonelssi_1 fonelssi_0 wss wi eonelssi_0 fonelssi_0 fonelssi_1 onelss ax-mp $.
$}
$( An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)
${
	fonssneli_0 $f class A $.
	fonssneli_1 $f class B $.
	eonssneli_0 $e |- A e. On $.
	onssneli $p |- ( A C_ B -> -. B e. A ) $= fonssneli_1 fonssneli_0 wcel fonssneli_0 fonssneli_1 wss fonssneli_1 fonssneli_0 wcel fonssneli_0 fonssneli_1 wss fonssneli_1 fonssneli_1 wcel fonssneli_1 fonssneli_0 wcel fonssneli_1 con0 wcel fonssneli_1 word fonssneli_1 fonssneli_1 wcel wn fonssneli_0 fonssneli_1 eonssneli_0 oneli fonssneli_1 eloni fonssneli_1 ordirr 3syl fonssneli_0 fonssneli_1 wss fonssneli_1 fonssneli_0 wcel fonssneli_1 fonssneli_1 wcel fonssneli_0 fonssneli_1 fonssneli_1 ssel com12 mtod con2i $.
$}
$( An ordering law for ordinal numbers.  (Contributed by NM,
       13-Jun-1994.) $)
${
	fonssnel2i_0 $f class A $.
	fonssnel2i_1 $f class B $.
	eonssnel2i_0 $e |- A e. On $.
	onssnel2i $p |- ( B C_ A -> -. A e. B ) $= fonssnel2i_1 fonssnel2i_0 wss fonssnel2i_0 fonssnel2i_1 wcel fonssnel2i_0 fonssnel2i_0 wcel fonssnel2i_0 eonssnel2i_0 onirri fonssnel2i_1 fonssnel2i_0 fonssnel2i_0 ssel mtoi $.
$}
$( An element of an ordinal number equals the intersection with it.
       (Contributed by NM, 11-Jun-1994.) $)
${
	fonelini_0 $f class A $.
	fonelini_1 $f class B $.
	eonelini_0 $e |- A e. On $.
	onelini $p |- ( B e. A -> B = ( B i^i A ) ) $= fonelini_1 fonelini_0 wcel fonelini_1 fonelini_0 wss fonelini_1 fonelini_1 fonelini_0 cin wceq fonelini_0 fonelini_1 eonelini_0 onelssi fonelini_1 fonelini_0 dfss sylib $.
$}
$( An ordinal number equals its union with any element.  (Contributed by
       NM, 13-Jun-1994.) $)
${
	foneluni_0 $f class A $.
	foneluni_1 $f class B $.
	eoneluni_0 $e |- A e. On $.
	oneluni $p |- ( B e. A -> ( A u. B ) = A ) $= foneluni_1 foneluni_0 wcel foneluni_1 foneluni_0 wss foneluni_0 foneluni_1 cun foneluni_0 wceq foneluni_0 foneluni_1 eoneluni_0 onelssi foneluni_1 foneluni_0 ssequn2 sylib $.
$}
$( An ordinal number is equal to the union of its successor.  (Contributed
       by NM, 12-Jun-1994.) $)
${
	fonunisuci_0 $f class A $.
	eonunisuci_0 $e |- A e. On $.
	onunisuci $p |- U. suc A = A $= fonunisuci_0 wtr fonunisuci_0 csuc cuni fonunisuci_0 wceq fonunisuci_0 eonunisuci_0 ontrci fonunisuci_0 fonunisuci_0 con0 eonunisuci_0 elexi unisuc mpbi $.
$}
$( Subset is equivalent to membership or equality for ordinal numbers.
         (Contributed by NM, 15-Sep-1995.) $)
${
	fonsseli_0 $f class A $.
	fonsseli_1 $f class B $.
	eonsseli_0 $e |- A e. On $.
	eonsseli_1 $e |- B e. On $.
	onsseli $p |- ( A C_ B <-> ( A e. B \/ A = B ) ) $= fonsseli_0 con0 wcel fonsseli_1 con0 wcel fonsseli_0 fonsseli_1 wss fonsseli_0 fonsseli_1 wcel fonsseli_0 fonsseli_1 wceq wo wb eonsseli_0 eonsseli_1 fonsseli_0 fonsseli_1 onsseleq mp2an $.
$}
$( The union of two ordinal numbers is an ordinal number.  (Contributed
         by NM, 13-Jun-1994.) $)
${
	fonun2i_0 $f class A $.
	fonun2i_1 $f class B $.
	eonun2i_0 $e |- A e. On $.
	eonun2i_1 $e |- B e. On $.
	onun2i $p |- ( A u. B ) e. On $= fonun2i_1 fonun2i_0 wcel fonun2i_0 fonun2i_1 wss wo fonun2i_0 fonun2i_1 cun con0 wcel fonun2i_1 word fonun2i_0 word fonun2i_1 fonun2i_0 wcel fonun2i_0 fonun2i_1 wss wo fonun2i_1 eonun2i_1 onordi fonun2i_0 eonun2i_0 onordi fonun2i_1 fonun2i_0 ordtri2or mp2an fonun2i_1 fonun2i_0 wcel fonun2i_0 fonun2i_1 cun con0 wcel fonun2i_0 fonun2i_1 wss fonun2i_1 fonun2i_0 wcel fonun2i_0 fonun2i_1 cun fonun2i_0 con0 fonun2i_0 fonun2i_1 eonun2i_0 oneluni eonun2i_0 syl6eqel fonun2i_0 fonun2i_1 wss fonun2i_0 fonun2i_1 cun fonun2i_1 wceq fonun2i_0 fonun2i_1 cun con0 wcel fonun2i_0 fonun2i_1 ssequn1 fonun2i_0 fonun2i_1 cun fonun2i_1 wceq fonun2i_0 fonun2i_1 cun con0 wcel fonun2i_1 con0 wcel eonun2i_1 fonun2i_0 fonun2i_1 cun fonun2i_1 con0 eleq1 mpbiri sylbi jaoi ax-mp $.
$}
$( An ordinal equal to its own union is either zero or a limit ordinal.
     (Contributed by NM, 1-Oct-2003.) $)
${
	funizlim_0 $f class A $.
	unizlim $p |- ( Ord A -> ( A = U. A <-> ( A = (/) \/ Lim A ) ) ) $= funizlim_0 word funizlim_0 funizlim_0 cuni wceq funizlim_0 c0 wceq funizlim_0 wlim wo funizlim_0 word funizlim_0 funizlim_0 cuni wceq funizlim_0 c0 wceq funizlim_0 wlim wo funizlim_0 word funizlim_0 funizlim_0 cuni wceq wa funizlim_0 c0 wceq funizlim_0 wlim funizlim_0 word funizlim_0 funizlim_0 cuni wceq funizlim_0 c0 wceq wn funizlim_0 wlim wi funizlim_0 word funizlim_0 c0 wceq wn funizlim_0 funizlim_0 cuni wceq funizlim_0 wlim funizlim_0 c0 wceq wn funizlim_0 c0 wne funizlim_0 word funizlim_0 funizlim_0 cuni wceq funizlim_0 wlim wi funizlim_0 c0 df-ne funizlim_0 word funizlim_0 c0 wne funizlim_0 funizlim_0 cuni wceq funizlim_0 wlim funizlim_0 wlim funizlim_0 word funizlim_0 c0 wne funizlim_0 funizlim_0 cuni wceq w3a funizlim_0 df-lim biimpri 3exp syl5bir com23 imp orrd ex funizlim_0 c0 wceq funizlim_0 funizlim_0 cuni wceq funizlim_0 wlim funizlim_0 c0 wceq c0 c0 cuni funizlim_0 funizlim_0 cuni c0 cuni c0 uni0 eqcomi funizlim_0 c0 wceq id funizlim_0 c0 unieq 3eqtr4a funizlim_0 limuni jaoi impbid1 $.
$}
$( An ordinal number either equals zero or contains zero.  (Contributed by
     NM, 1-Jun-2004.) $)
${
	fon0eqel_0 $f class A $.
	on0eqel $p |- ( A e. On -> ( A = (/) \/ (/) e. A ) ) $= fon0eqel_0 con0 wcel c0 fon0eqel_0 wcel c0 fon0eqel_0 wceq wo fon0eqel_0 c0 wceq c0 fon0eqel_0 wcel wo fon0eqel_0 con0 wcel c0 fon0eqel_0 wss c0 fon0eqel_0 wcel c0 fon0eqel_0 wceq wo fon0eqel_0 0ss c0 con0 wcel fon0eqel_0 con0 wcel c0 fon0eqel_0 wss c0 fon0eqel_0 wcel c0 fon0eqel_0 wceq wo wb 0elon c0 fon0eqel_0 onsseleq mpan mpbii c0 fon0eqel_0 wcel c0 fon0eqel_0 wceq wo c0 fon0eqel_0 wcel fon0eqel_0 c0 wceq wo fon0eqel_0 c0 wceq c0 fon0eqel_0 wcel wo c0 fon0eqel_0 wceq fon0eqel_0 c0 wceq c0 fon0eqel_0 wcel c0 fon0eqel_0 eqcom orbi2i c0 fon0eqel_0 wcel fon0eqel_0 c0 wceq orcom bitri sylib $.
$}
$( The singleton of the singleton of the empty set is not an ordinal (nor a
     natural number by ~ omsson ).  It can be used to represent an "undefined"
     value for a partial operation on natural or ordinal numbers.  See also
     ~ onxpdisj .  (Contributed by NM, 21-May-2004.)  (Proof shortened by
     Andrew Salmon, 12-Aug-2011.) $)
${
	snsn0non $p |- -. { { (/) } } e. On $= c0 csn csn con0 wcel c0 csn csn c0 wceq c0 c0 csn csn wcel wo c0 csn csn c0 wceq c0 c0 csn csn wcel c0 csn c0 csn csn wcel c0 csn csn c0 wceq wn c0 csn p0ex snid c0 csn csn c0 csn n0i ax-mp c0 c0 csn csn wcel c0 c0 csn wceq c0 c0 csn wceq c0 csn c0 wceq c0 c0 csn wcel c0 csn c0 wceq wn c0 0ex snid c0 csn c0 n0i ax-mp c0 c0 csn eqcom mtbir c0 c0 csn 0ex elsnc mtbir pm3.2ni c0 csn csn on0eqel mto $.
$}

