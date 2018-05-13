$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/True_and_false_constants.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Truth tables

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Some sources define operations on true/false values using truth tables.
  These tables show the results of their operations for all possible
  combinations of true ( ` T. ` ) and false ( ` F. ` ).
  Here we show that our definitions and axioms produce equivalent results for
  ` /\ ` (conjunction aka logical 'and') ~ df-an ,
  ` \/ ` (disjunction aka logical inclusive 'or') ~ df-or ,
  ` -> ` (implies) ~ wi ,
  ` -. ` (not) ~ wn ,
  ` <-> ` (logical equivalence) ~ df-bi ,
  ` -/\ ` (nand aka Sheffer stroke) ~ df-nan , and
  ` \/_ ` (exclusive or) ~ df-xor .
$)

$(A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_truantru $p |- ( ( T. /\ T. ) <-> T. ) $= a_wtru p_anidm $.
$}

$(A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_truanfal $p |- ( ( T. /\ F. ) <-> F. ) $= p_fal a_wfal a_wtru p_intnan a_wtru a_wfal a_wa p_bifal $.
$}

$(A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_falantru $p |- ( ( F. /\ T. ) <-> F. ) $= p_fal a_wfal a_wtru p_intnanr a_wfal a_wtru a_wa p_bifal $.
$}

$(A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_falanfal $p |- ( ( F. /\ F. ) <-> F. ) $= a_wfal p_anidm $.
$}

$(A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_truortru $p |- ( ( T. \/ T. ) <-> T. ) $= a_wtru p_oridm $.
$}

$(A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_truorfal $p |- ( ( T. \/ F. ) <-> T. ) $= p_tru a_wtru a_wfal p_orci a_wtru a_wfal a_wo p_bitru $.
$}

$(A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_falortru $p |- ( ( F. \/ T. ) <-> T. ) $= p_tru a_wtru a_wfal p_olci a_wfal a_wtru a_wo p_bitru $.
$}

$(A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_falorfal $p |- ( ( F. \/ F. ) <-> F. ) $= a_wfal p_oridm $.
$}

$(A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_truimtru $p |- ( ( T. -> T. ) <-> T. ) $= a_wtru p_id a_wtru a_wtru a_wi p_bitru $.
$}

$(A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_truimfal $p |- ( ( T. -> F. ) <-> F. ) $= p_tru a_wtru a_wfal p_a1bi a_wfal a_wtru a_wfal a_wi p_bicomi $.
$}

$(A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_falimtru $p |- ( ( F. -> T. ) <-> T. ) $= a_wtru p_falim a_wfal a_wtru a_wi p_bitru $.
$}

$(A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_falimfal $p |- ( ( F. -> F. ) <-> T. ) $= a_wfal p_id a_wfal a_wfal a_wi p_bitru $.
$}

$(A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)

${
	$v  $.
	p_nottru $p |- ( -. T. <-> F. ) $= a_df-fal a_wfal a_wtru a_wn p_bicomi $.
$}

$(A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_notfal $p |- ( -. F. <-> T. ) $= p_fal a_wfal a_wn p_bitru $.
$}

$(A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_trubitru $p |- ( ( T. <-> T. ) <-> T. ) $= a_wtru p_biid a_wtru a_wtru a_wb p_bitru $.
$}

$(A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_trubifal $p |- ( ( T. <-> F. ) <-> F. ) $= p_nottru a_wtru a_wfal p_nbbn a_wtru a_wn a_wfal a_wb a_wtru a_wfal a_wb a_wn p_mpbi a_wtru a_wfal a_wb p_bifal $.
$}

$(A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_falbitru $p |- ( ( F. <-> T. ) <-> F. ) $= a_wfal a_wtru p_bicom p_trubifal a_wfal a_wtru a_wb a_wtru a_wfal a_wb a_wfal p_bitri $.
$}

$(A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_falbifal $p |- ( ( F. <-> F. ) <-> T. ) $= a_wfal p_biid a_wfal a_wfal a_wb p_bitru $.
$}

$(A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_trunantru $p |- ( ( T. -/\ T. ) <-> F. ) $= a_wtru p_nannot p_nottru a_wtru a_wtru a_wnan a_wtru a_wn a_wfal p_bitr3i $.
$}

$(A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_trunanfal $p |- ( ( T. -/\ F. ) <-> T. ) $= a_wtru a_wfal a_df-nan p_truanfal a_wtru a_wfal a_wa a_wfal p_notbii p_notfal a_wtru a_wfal a_wnan a_wtru a_wfal a_wa a_wn a_wfal a_wn a_wtru p_3bitri $.
$}

$(A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_falnantru $p |- ( ( F. -/\ T. ) <-> T. ) $= a_wfal a_wtru p_nancom p_trunanfal a_wfal a_wtru a_wnan a_wtru a_wfal a_wnan a_wtru p_bitri $.
$}

$(A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)

${
	$v  $.
	p_falnanfal $p |- ( ( F. -/\ F. ) <-> T. ) $= a_wfal p_nannot p_notfal a_wfal a_wfal a_wnan a_wfal a_wn a_wtru p_bitr3i $.
$}

$(A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)

${
	$v  $.
	p_truxortru $p |- ( ( T. \/_ T. ) <-> F. ) $= a_wtru a_wtru a_df-xor p_trubitru a_wtru a_wtru a_wxo a_wtru a_wtru a_wb a_wtru p_xchbinx p_nottru a_wtru a_wtru a_wxo a_wtru a_wn a_wfal p_bitri $.
$}

$(A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)

${
	$v  $.
	p_truxorfal $p |- ( ( T. \/_ F. ) <-> T. ) $= a_wtru a_wfal a_df-xor p_trubifal a_wtru a_wfal a_wxo a_wtru a_wfal a_wb a_wfal p_xchbinx p_notfal a_wtru a_wfal a_wxo a_wfal a_wn a_wtru p_bitri $.
$}

$(A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)

${
	$v  $.
	p_falxortru $p |- ( ( F. \/_ T. ) <-> T. ) $= a_wfal a_wtru a_df-xor p_falbitru a_wfal a_wtru a_wb a_wfal p_notbii p_notfal a_wfal a_wtru a_wxo a_wfal a_wtru a_wb a_wn a_wfal a_wn a_wtru p_3bitri $.
$}

$(A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)

${
	$v  $.
	p_falxorfal $p |- ( ( F. \/_ F. ) <-> F. ) $= a_wfal a_wfal a_df-xor p_falbifal a_wfal a_wfal a_wxo a_wfal a_wfal a_wb a_wtru p_xchbinx p_nottru a_wfal a_wfal a_wxo a_wtru a_wn a_wfal p_bitri $.
$}


