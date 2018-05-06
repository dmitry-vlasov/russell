$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Abbreviated_conjunction_and_disjunction_of_three_wff_s.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare connective for alternative denial ('nand'). $)
$c -/\  $.
$( Overlined 'wedge' (read:  'nand') $)
$( Extend wff definition to include alternative denial ('nand'). $)
${
	fwnan_0 $f wff ph $.
	fwnan_1 $f wff ps $.
	wnan $a wff ( ph -/\ ps ) $.
$}
$( Define incompatibility, or alternative denial ('not-and' or 'nand').  This
     is also called the Sheffer stroke, represented by a vertical bar, but we
     use a different symbol to avoid ambiguity with other uses of the vertical
     bar.  In the second edition of Principia Mathematica (1927), Russell and
     Whitehead used the Sheffer stroke and suggested it as a replacement for
     the "or" and "not" operations of the first edition.  However, in practice,
     "or" and "not" are more widely used.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. -/\ T. ) <-> F. ) `
     ( ~ trunantru ), ` ( ( T. -/\ F. ) <-> T. ) ` ( ~ trunanfal ),
     ` ( ( F. -/\ T. ) <-> T. ) ` ( ~ falnantru ), and
     ` ( ( F. -/\ F. ) <-> T. ) ` ( ~ falnanfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` \/_ `
     ( ~ df-xor ) .  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
${
	fdf-nan_0 $f wff ph $.
	fdf-nan_1 $f wff ps $.
	df-nan $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.
$}
$( Write 'and' in terms of 'nand'.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
${
	fnanan_0 $f wff ph $.
	fnanan_1 $f wff ps $.
	nanan $p |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) ) $= fnanan_0 fnanan_1 wnan fnanan_0 fnanan_1 wa fnanan_0 fnanan_1 df-nan con2bii $.
$}
$( The 'nand' operator commutes.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
${
	fnancom_0 $f wff ph $.
	fnancom_1 $f wff ps $.
	nancom $p |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) ) $= fnancom_0 fnancom_1 wa wn fnancom_1 fnancom_0 wa wn fnancom_0 fnancom_1 wnan fnancom_1 fnancom_0 wnan fnancom_0 fnancom_1 wa fnancom_1 fnancom_0 wa fnancom_0 fnancom_1 ancom notbii fnancom_0 fnancom_1 df-nan fnancom_1 fnancom_0 df-nan 3bitr4i $.
$}
$( Lemma for handling nested 'nand's.  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
${
	fnannan_0 $f wff ph $.
	fnannan_1 $f wff ps $.
	fnannan_2 $f wff ch $.
	nannan $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $= fnannan_0 fnannan_2 fnannan_1 wnan wnan fnannan_0 fnannan_2 fnannan_1 wa wn wa wn fnannan_0 fnannan_2 fnannan_1 wa wi fnannan_0 fnannan_2 fnannan_1 wnan wnan fnannan_0 fnannan_2 fnannan_1 wnan wa fnannan_0 fnannan_2 fnannan_1 wa wn wa fnannan_0 fnannan_2 fnannan_1 wnan df-nan fnannan_2 fnannan_1 wnan fnannan_2 fnannan_1 wa wn fnannan_0 fnannan_2 fnannan_1 df-nan anbi2i xchbinx fnannan_0 fnannan_2 fnannan_1 wa iman bitr4i $.
$}
$( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
${
	fnanim_0 $f wff ph $.
	fnanim_1 $f wff ps $.
	nanim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $= fnanim_0 fnanim_1 fnanim_1 wnan wnan fnanim_0 fnanim_1 fnanim_1 wa wi fnanim_0 fnanim_1 wi fnanim_0 fnanim_1 fnanim_1 nannan fnanim_0 fnanim_1 anidmdbi bitr2i $.
$}
$( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
${
	fnannot_0 $f wff ps $.
	nannot $p |- ( -. ps <-> ( ps -/\ ps ) ) $= fnannot_0 fnannot_0 wnan fnannot_0 wn fnannot_0 fnannot_0 wnan fnannot_0 fnannot_0 wa fnannot_0 fnannot_0 fnannot_0 df-nan fnannot_0 anidm xchbinx bicomi $.
$}
$( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
${
	fnanbi_0 $f wff ph $.
	fnanbi_1 $f wff ps $.
	nanbi $p |- ( ( ph <-> ps ) <-> ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $= fnanbi_0 fnanbi_1 wa wn fnanbi_0 wn fnanbi_1 wn wa wn wa wn fnanbi_0 fnanbi_1 wa fnanbi_0 wn fnanbi_1 wn wa wo fnanbi_0 fnanbi_1 wnan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan wnan fnanbi_0 fnanbi_1 wb fnanbi_0 fnanbi_1 wa fnanbi_0 wn fnanbi_1 wn wa pm4.57 fnanbi_0 fnanbi_1 wnan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan wnan fnanbi_0 fnanbi_1 wnan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan wa fnanbi_0 fnanbi_1 wa wn fnanbi_0 wn fnanbi_1 wn wa wn wa fnanbi_0 fnanbi_1 wnan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan df-nan fnanbi_0 fnanbi_1 wnan fnanbi_0 fnanbi_1 wa wn fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan fnanbi_0 wn fnanbi_1 wn wa wn fnanbi_0 fnanbi_1 df-nan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wnan fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan wa fnanbi_0 wn fnanbi_1 wn wa fnanbi_0 fnanbi_0 wnan fnanbi_1 fnanbi_1 wnan df-nan fnanbi_0 wn fnanbi_0 fnanbi_0 wnan fnanbi_1 wn fnanbi_1 fnanbi_1 wnan fnanbi_0 nannot fnanbi_1 nannot anbi12i xchbinxr anbi12i xchbinx fnanbi_0 fnanbi_1 dfbi3 3bitr4ri $.
$}

