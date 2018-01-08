$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/True_and_false_constants.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
$( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	truantru $p |- ( ( T. /\ T. ) <-> T. ) $= wtru anidm $.
$}
$( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	truanfal $p |- ( ( T. /\ F. ) <-> F. ) $= wtru wfal wa wfal wtru fal intnan bifal $.
$}
$( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	falantru $p |- ( ( F. /\ T. ) <-> F. ) $= wfal wtru wa wfal wtru fal intnanr bifal $.
$}
$( A ` /\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	falanfal $p |- ( ( F. /\ F. ) <-> F. ) $= wfal anidm $.
$}
$( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	truortru $p |- ( ( T. \/ T. ) <-> T. ) $= wtru oridm $.
$}
$( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	truorfal $p |- ( ( T. \/ F. ) <-> T. ) $= wtru wfal wo wtru wfal tru orci bitru $.
$}
$( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	falortru $p |- ( ( F. \/ T. ) <-> T. ) $= wfal wtru wo wtru wfal tru olci bitru $.
$}
$( A ` \/ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	falorfal $p |- ( ( F. \/ F. ) <-> F. ) $= wfal oridm $.
$}
$( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	truimtru $p |- ( ( T. -> T. ) <-> T. ) $= wtru wtru wi wtru id bitru $.
$}
$( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	truimfal $p |- ( ( T. -> F. ) <-> F. ) $= wfal wtru wfal wi wtru wfal tru a1bi bicomi $.
$}
$( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	falimtru $p |- ( ( F. -> T. ) <-> T. ) $= wfal wtru wi wtru falim bitru $.
$}
$( A ` -> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	falimfal $p |- ( ( F. -> F. ) <-> T. ) $= wfal wfal wi wfal id bitru $.
$}
$( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.) $)
${
	nottru $p |- ( -. T. <-> F. ) $= wfal wtru wn df-fal bicomi $.
$}
$( A ` -. ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	notfal $p |- ( -. F. <-> T. ) $= wfal wn fal bitru $.
$}
$( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	trubitru $p |- ( ( T. <-> T. ) <-> T. ) $= wtru wtru wb wtru biid bitru $.
$}
$( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	trubifal $p |- ( ( T. <-> F. ) <-> F. ) $= wtru wfal wb wtru wn wfal wb wtru wfal wb wn nottru wtru wfal nbbn mpbi bifal $.
$}
$( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	falbitru $p |- ( ( F. <-> T. ) <-> F. ) $= wfal wtru wb wtru wfal wb wfal wfal wtru bicom trubifal bitri $.
$}
$( A ` <-> ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	falbifal $p |- ( ( F. <-> F. ) <-> T. ) $= wfal wfal wb wfal biid bitru $.
$}
$( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	trunantru $p |- ( ( T. -/\ T. ) <-> F. ) $= wtru wtru wnan wtru wn wfal wtru nannot nottru bitr3i $.
$}
$( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	trunanfal $p |- ( ( T. -/\ F. ) <-> T. ) $= wtru wfal wnan wtru wfal wa wn wfal wn wtru wtru wfal df-nan wtru wfal wa wfal truanfal notbii notfal 3bitri $.
$}
$( A ` -/\ ` identity.  (Contributed by Anthony Hart, 23-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	falnantru $p |- ( ( F. -/\ T. ) <-> T. ) $= wfal wtru wnan wtru wfal wnan wtru wfal wtru nancom trunanfal bitri $.
$}
$( A ` -/\ ` identity.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Andrew Salmon, 13-May-2011.) $)
${
	falnanfal $p |- ( ( F. -/\ F. ) <-> T. ) $= wfal wfal wnan wfal wn wtru wfal nannot notfal bitr3i $.
$}
$( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
${
	truxortru $p |- ( ( T. \/_ T. ) <-> F. ) $= wtru wtru wxo wtru wn wfal wtru wtru wxo wtru wtru wb wtru wtru wtru df-xor trubitru xchbinx nottru bitri $.
$}
$( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 8-May-2015.) $)
${
	truxorfal $p |- ( ( T. \/_ F. ) <-> T. ) $= wtru wfal wxo wfal wn wtru wtru wfal wxo wtru wfal wb wfal wtru wfal df-xor trubifal xchbinx notfal bitri $.
$}
$( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
${
	falxortru $p |- ( ( F. \/_ T. ) <-> T. ) $= wfal wtru wxo wfal wtru wb wn wfal wn wtru wfal wtru df-xor wfal wtru wb wfal falbitru notbii notfal 3bitri $.
$}
$( A ` \/_ ` identity.  (Contributed by David A. Wheeler, 9-May-2015.) $)
${
	falxorfal $p |- ( ( F. \/_ F. ) <-> F. ) $= wfal wfal wxo wtru wn wfal wfal wfal wxo wfal wfal wb wtru wfal wfal df-xor falbifal xchbinx nottru bitri $.
$}

