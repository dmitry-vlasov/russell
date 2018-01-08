$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Rederive_new_axioms_from_old__theorems_ax5_,_ax6_,_ax9from9o_,_ax11_,_ax12.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Legacy theorems using obsolete axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These theorems were mostly intended to study properties of the older axiom
  schemes and are not useful outside of this section.  They should not be
  used outside of this section.  They may be deleted when they are deemed to no
  longer be of interest.

$)
$( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       (This theorem simply repeats ~ ax-17 so that we can include the
       following note, which applies only to the obsolete axiomatization.)

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-5o ,
       ~ ax-4 , ~ ax-7 , ~ ax-6o , ~ ax-8 , ~ ax-12o , ~ ax-9o , ~ ax-10o ,
       ~ ax-13 , ~ ax-14 , ~ ax-15 , ~ ax-11o , and ~ ax-16 : in that system,
       we can derive any instance of ~ ax-17 not containing wff variables by
       induction on formula length, using ~ ax17eq and ~ ax17el for the basis
       together ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom,
       our development would be quite inconvenient since we could work only
       with specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a set variable not occurring in a wff (as
       opposed to just two set variables being distinct).  (Contributed by NM,
       19-Aug-2017.)  (New usage is discouraged.)  (Proof modification
       discouraged.) $)
${
	$d x ph $.
	fax17o_0 $f wff ph $.
	fax17o_1 $f set x $.
	ax17o $p |- ( ph -> A. x ph ) $= fax17o_0 fax17o_1 ax-17 $.
$}
$( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.  This
     is often an axiom of equality in textbook systems, but we don't need it as
     an axiom since it can be proved from our other axioms (although the proof,
     as you can see below, is not as obvious as you might think).  This proof
     uses only axioms without distinct variable conditions and thus requires no
     dummy variables.  A simpler proof, similar to Tarki's, is possible if we
     make use of ~ ax-17 ; see the proof of ~ equid .  See ~ equid1ALT for an
     alternate proof.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fequid1_0 $f set x $.
	equid1 $p |- x = x $= fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wi fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wi wi fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wi fequid1_0 wal wi fequid1_0 fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wi fequid1_0 ax-5o fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 wal fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 weq fequid1_0 wal wi fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 ax-4 fequid1_0 fequid1_0 weq fequid1_0 wal wn fequid1_0 ax-4 fequid1_0 fequid1_0 fequid1_0 ax-12o sylc mpg fequid1_0 fequid1_0 weq fequid1_0 fequid1_0 ax-9o syl fequid1_0 fequid1_0 weq fequid1_0 ax-6o pm2.61i $.
$}
$( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fsps-o_0 $f wff ph $.
	fsps-o_1 $f wff ps $.
	fsps-o_2 $f set x $.
	esps-o_0 $e |- ( ph -> ps ) $.
	sps-o $p |- ( A. x ph -> ps ) $= fsps-o_0 fsps-o_2 wal fsps-o_0 fsps-o_1 fsps-o_0 fsps-o_2 ax-4 esps-o_0 syl $.
$}
$( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof does not use
     ~ ax-9o .)  (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf
     Lammen, 23-Mar-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fhbequid_0 $f set x $.
	fhbequid_1 $f set y $.
	hbequid $p |- ( x = x -> A. y x = x ) $= fhbequid_1 fhbequid_0 weq fhbequid_1 wal fhbequid_1 fhbequid_0 weq fhbequid_1 wal fhbequid_0 fhbequid_0 weq fhbequid_0 fhbequid_0 weq fhbequid_1 wal wi fhbequid_0 fhbequid_0 fhbequid_1 ax-12o fhbequid_1 fhbequid_0 weq fhbequid_1 wal fhbequid_0 fhbequid_0 weq fhbequid_1 wal fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_0 weq fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_1 fhbequid_0 weq fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_0 fhbequid_0 ax-8 pm2.43i alimi a1d fhbequid_1 fhbequid_0 weq fhbequid_1 wal fhbequid_0 fhbequid_0 weq fhbequid_1 wal fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_0 weq fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_1 fhbequid_0 weq fhbequid_0 fhbequid_0 weq fhbequid_1 fhbequid_0 fhbequid_0 ax-8 pm2.43i alimi a1d pm2.61ii $.
$}
$( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-5 ,
     ~ ax-8 , ~ ax-12o , and ~ ax-gen .  This shows that this can be proved
     without ~ ax9 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax9 is obtainable from ~ equid and ~ hbth .)  Remark added
     2-Dec-2015 NM:  This proof does implicitly use ~ ax9v , which is used for
     the derivation of ~ ax12o , unless we consider ~ ax-12o the starting axiom
     rather than ~ ax-12 .  (Contributed by NM, 13-Jan-2011.)  (Revised by
     Mario Carneiro, 12-Oct-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fnfequid-o_0 $f set x $.
	fnfequid-o_1 $f set y $.
	nfequid-o $p |- F/ y x = x $= fnfequid-o_0 fnfequid-o_0 weq fnfequid-o_1 fnfequid-o_0 fnfequid-o_1 hbequid nfi $.
$}
$( Proof of a single axiom that can replace ~ ax-4 and ~ ax-6o .  See
     ~ ax46to4 and ~ ax46to6 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax46_0 $f wff ph $.
	fax46_1 $f set x $.
	ax46 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $= fax46_0 fax46_1 wal wn fax46_1 wal fax46_0 fax46_1 wal fax46_0 fax46_0 fax46_1 ax-6o fax46_0 fax46_1 ax-4 ja $.
$}
$( Re-derivation of ~ ax-4 from ~ ax46 .  Only propositional calculus is used
     for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax46to4_0 $f wff ph $.
	fax46to4_1 $f set x $.
	ax46to4 $p |- ( A. x ph -> ph ) $= fax46to4_0 fax46to4_1 wal fax46to4_0 fax46to4_1 wal wn fax46to4_1 wal fax46to4_0 fax46to4_1 wal wi fax46to4_0 fax46to4_0 fax46to4_1 wal fax46to4_0 fax46to4_1 wal wn fax46to4_1 wal ax-1 fax46to4_0 fax46to4_1 ax46 syl $.
$}
$( Re-derivation of ~ ax-6o from ~ ax46 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax46to6_0 $f wff ph $.
	fax46to6_1 $f set x $.
	ax46to6 $p |- ( -. A. x -. A. x ph -> ph ) $= fax46to6_0 fax46to6_1 wal wn fax46to6_1 wal wn fax46to6_0 fax46to6_1 wal wn fax46to6_1 wal fax46to6_0 fax46to6_1 wal wi fax46to6_0 fax46to6_0 fax46to6_1 wal wn fax46to6_1 wal fax46to6_0 fax46to6_1 wal pm2.21 fax46to6_0 fax46to6_1 ax46 syl $.
$}
$( Proof of a single axiom that can replace both ~ ax-6o and ~ ax-7 .  See
     ~ ax67to6 and ~ ax67to7 for the re-derivation of those axioms.
     (Contributed by NM, 18-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax67_0 $f wff ph $.
	fax67_1 $f set x $.
	fax67_2 $f set y $.
	ax67 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $= fax67_0 fax67_1 wal fax67_2 wal wn fax67_1 wal wn fax67_0 fax67_2 wal fax67_1 wal wn fax67_1 wal wn fax67_0 fax67_2 wal fax67_0 fax67_2 wal fax67_1 wal wn fax67_1 wal fax67_0 fax67_1 wal fax67_2 wal wn fax67_1 wal fax67_0 fax67_2 wal fax67_1 wal wn fax67_0 fax67_1 wal fax67_2 wal wn fax67_1 fax67_0 fax67_1 wal fax67_2 wal fax67_0 fax67_2 wal fax67_1 wal fax67_0 fax67_2 fax67_1 ax-7 con3i alimi con3i fax67_0 fax67_2 wal fax67_1 ax-6o syl $.
$}
$( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fnfa1-o_0 $f wff ph $.
	fnfa1-o_1 $f set x $.
	nfa1-o $p |- F/ x A. x ph $= fnfa1-o_0 fnfa1-o_1 wal fnfa1-o_1 fnfa1-o_0 fnfa1-o_1 hba1-o nfi $.
$}
$( Re-derivation of ~ ax-6o from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax67to6_0 $f wff ph $.
	fax67to6_1 $f set x $.
	ax67to6 $p |- ( -. A. x -. A. x ph -> ph ) $= fax67to6_0 fax67to6_1 wal wn fax67to6_1 wal wn fax67to6_0 fax67to6_1 wal fax67to6_1 wal wn fax67to6_1 wal wn fax67to6_0 fax67to6_1 wal fax67to6_0 fax67to6_0 fax67to6_1 wal fax67to6_1 wal wn fax67to6_1 wal fax67to6_0 fax67to6_1 wal wn fax67to6_1 wal fax67to6_0 fax67to6_1 wal fax67to6_1 wal wn fax67to6_0 fax67to6_1 wal wn fax67to6_1 fax67to6_0 fax67to6_1 wal fax67to6_0 fax67to6_1 wal fax67to6_1 wal fax67to6_0 fax67to6_1 hba1-o con3i alimi con3i fax67to6_0 fax67to6_1 fax67to6_1 ax67 fax67to6_0 fax67to6_1 ax-4 3syl $.
$}
$( Re-derivation of ~ ax-7 from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax67to7_0 $f wff ph $.
	fax67to7_1 $f set x $.
	fax67to7_2 $f set y $.
	ax67to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $= fax67to7_0 fax67to7_2 wal fax67to7_1 wal fax67to7_0 fax67to7_2 wal fax67to7_1 wal wn fax67to7_2 wal wn fax67to7_2 wal fax67to7_0 fax67to7_1 wal fax67to7_2 wal fax67to7_0 fax67to7_2 wal fax67to7_1 wal wn fax67to7_2 wal wn fax67to7_2 wal fax67to7_0 fax67to7_2 wal fax67to7_1 wal fax67to7_0 fax67to7_2 wal fax67to7_1 wal wn fax67to7_2 ax67to6 con4i fax67to7_0 fax67to7_2 wal fax67to7_1 wal wn fax67to7_2 wal wn fax67to7_0 fax67to7_1 wal fax67to7_2 fax67to7_0 fax67to7_2 fax67to7_1 ax67 alimi syl $.
$}
$( Proof of a single axiom that can replace ~ ax-4 , ~ ax-6o , and ~ ax-7 in
     a subsystem that includes these axioms plus ~ ax-5o and ~ ax-gen (and
     propositional calculus).  See ~ ax467to4 , ~ ax467to6 , and ~ ax467to7 for
     the re-derivation of those axioms.  This theorem extends the idea in Scott
     Fenton's ~ ax46 .  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax467_0 $f wff ph $.
	fax467_1 $f set x $.
	fax467_2 $f set y $.
	ax467 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $= fax467_0 fax467_2 wal fax467_1 wal wn fax467_2 wal fax467_1 wal fax467_0 fax467_1 wal fax467_0 fax467_0 fax467_2 wal fax467_0 fax467_0 fax467_2 wal fax467_1 wal wn fax467_2 wal fax467_1 wal fax467_0 fax467_2 ax-4 fax467_0 fax467_2 wal wn fax467_0 fax467_2 wal wn fax467_2 wal fax467_0 fax467_2 wal fax467_1 wal wn fax467_1 wal fax467_2 wal fax467_0 fax467_2 wal fax467_1 wal wn fax467_2 wal fax467_1 wal fax467_0 fax467_2 ax6 fax467_0 fax467_2 wal wn fax467_0 fax467_2 wal fax467_1 wal wn fax467_1 wal fax467_2 fax467_0 fax467_2 wal fax467_1 wal wn fax467_1 wal fax467_0 fax467_2 wal fax467_0 fax467_2 wal fax467_1 ax-6o con1i alimi fax467_0 fax467_2 wal fax467_1 wal wn fax467_2 fax467_1 ax-7 3syl nsyl4 fax467_0 fax467_1 ax-4 ja $.
$}
$( Re-derivation of ~ ax-4 from ~ ax467 .  Only propositional calculus is
     used by the re-derivation.  (Contributed by NM, 19-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax467to4_0 $f wff ph $.
	fax467to4_1 $f set x $.
	ax467to4 $p |- ( A. x ph -> ph ) $= fax467to4_0 fax467to4_1 wal fax467to4_0 fax467to4_1 wal fax467to4_1 wal wn fax467to4_1 wal fax467to4_1 wal fax467to4_0 fax467to4_1 wal wi fax467to4_0 fax467to4_0 fax467to4_1 wal fax467to4_0 fax467to4_1 wal fax467to4_1 wal wn fax467to4_1 wal fax467to4_1 wal ax-1 fax467to4_0 fax467to4_1 fax467to4_1 ax467 syl $.
$}
$( Re-derivation of ~ ax-6o from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax467to6_0 $f wff ph $.
	fax467to6_1 $f set x $.
	ax467to6 $p |- ( -. A. x -. A. x ph -> ph ) $= fax467to6_0 fax467to6_1 wal wn fax467to6_1 wal wn fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_1 wal fax467to6_1 wal wn fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_1 wal fax467to6_1 wal fax467to6_0 fax467to6_1 wal wi fax467to6_0 fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_1 wal fax467to6_1 wal fax467to6_0 fax467to6_1 wal wn fax467to6_1 wal fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_1 wal fax467to6_0 fax467to6_1 wal wn fax467to6_1 wal fax467to6_1 fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_0 fax467to6_1 wal wn fax467to6_1 fax467to6_0 fax467to6_1 wal fax467to6_0 fax467to6_1 wal fax467to6_1 wal fax467to6_0 fax467to6_1 hba1-o con3i alimi sps-o con3i fax467to6_0 fax467to6_1 wal fax467to6_1 wal wn fax467to6_1 wal fax467to6_1 wal fax467to6_0 fax467to6_1 wal pm2.21 fax467to6_0 fax467to6_1 fax467to6_1 ax467 3syl $.
$}
$( Re-derivation of ~ ax-7 from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax467to7_0 $f wff ph $.
	fax467to7_1 $f set x $.
	fax467to7_2 $f set y $.
	ax467to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $= fax467to7_0 fax467to7_2 wal fax467to7_1 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal wn fax467to7_2 wal fax467to7_0 fax467to7_1 wal fax467to7_2 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal wn fax467to7_2 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 ax467to6 con4i fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal wn fax467to7_0 fax467to7_1 wal fax467to7_2 fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 wal wn fax467to7_1 wal fax467to7_0 fax467to7_1 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 wal wn fax467to7_0 fax467to7_1 fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 wal wn fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 wal fax467to7_0 fax467to7_1 wal wi fax467to7_0 fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 wal fax467to7_0 fax467to7_1 wal pm2.21 fax467to7_0 fax467to7_1 fax467to7_2 ax467 syl alimi fax467to7_0 fax467to7_2 wal fax467to7_1 wal wn fax467to7_2 wal fax467to7_1 ax467to6 nsyl4 alimi syl $.
$}
$( ~ equid with existential quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf Lammen,
     27-Feb-2014.)  (Proof modification is discouraged.) $)
${
	fequidqe_0 $f set x $.
	fequidqe_1 $f set y $.
	equidqe $p |- -. A. y -. x = x $= fequidqe_0 fequidqe_0 weq wn fequidqe_1 wal fequidqe_1 fequidqe_0 weq wn fequidqe_1 wal fequidqe_1 fequidqe_0 ax9from9o fequidqe_0 fequidqe_0 weq wn fequidqe_1 fequidqe_0 weq wn fequidqe_1 fequidqe_1 fequidqe_0 weq fequidqe_0 fequidqe_0 weq fequidqe_1 fequidqe_0 weq fequidqe_0 fequidqe_0 weq fequidqe_1 fequidqe_0 fequidqe_0 ax-8 pm2.43i con3i alimi mto $.
$}
$( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 .  (Contributed
     by NM, 13-Jan-2011.)  (Proof modification is discouraged.) $)
${
	fax4sp1_0 $f set x $.
	fax4sp1_1 $f set y $.
	ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $= fax4sp1_0 fax4sp1_0 weq wn fax4sp1_1 wal fax4sp1_0 fax4sp1_0 weq wn fax4sp1_0 fax4sp1_1 equidqe pm2.21i $.
$}
$( ~ equid with universal quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fequidq_0 $f set x $.
	fequidq_1 $f set y $.
	equidq $p |- A. y x = x $= fequidq_0 fequidq_0 weq fequidq_1 wal fequidq_0 fequidq_0 weq wn fequidq_1 wal fequidq_0 fequidq_1 equidqe fequidq_0 fequidq_0 weq fequidq_1 wal wn fequidq_0 fequidq_0 weq wn fequidq_1 fequidq_0 fequidq_0 weq fequidq_1 ax6 fequidq_0 fequidq_0 weq fequidq_0 fequidq_0 weq fequidq_1 wal fequidq_0 fequidq_1 hbequid con3i alrimih mt3 $.
$}
$( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
     Alternate proof of ~ equid1 from older axioms ~ ax-6o and ~ ax-9o .
     (Contributed by NM, 5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fequid1ALT_0 $f set x $.
	equid1ALT $p |- x = x $= fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wn fequid1ALT_0 wal fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wn fequid1ALT_0 wal fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wi fequid1ALT_0 wal fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wn fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wi fequid1ALT_0 fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wn fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 wal wi fequid1ALT_0 fequid1ALT_0 fequid1ALT_0 ax-12o pm2.43i alimi fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 fequid1ALT_0 ax-9o syl fequid1ALT_0 fequid1ALT_0 weq fequid1ALT_0 ax-6o pm2.61i $.
$}
$( Rederivation of ~ ax-10 from original version ~ ax-10o .  See theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified, or use
     ~ aecom-o when this form is needed for studies involving ~ ax-10o and
     omitting ~ ax-17 .  (Contributed by NM, 16-May-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax10from10o_0 $f set x $.
	fax10from10o_1 $f set y $.
	ax10from10o $p |- ( A. x x = y -> A. y y = x ) $= fax10from10o_0 fax10from10o_1 weq fax10from10o_0 wal fax10from10o_0 fax10from10o_1 weq fax10from10o_1 wal fax10from10o_1 fax10from10o_0 weq fax10from10o_1 wal fax10from10o_0 fax10from10o_1 weq fax10from10o_0 wal fax10from10o_0 fax10from10o_1 weq fax10from10o_1 wal fax10from10o_0 fax10from10o_1 weq fax10from10o_0 fax10from10o_1 ax-10o pm2.43i fax10from10o_0 fax10from10o_1 weq fax10from10o_1 fax10from10o_0 weq fax10from10o_1 fax10from10o_0 fax10from10o_1 equcomi alimi syl $.
$}
$( A commutation rule for distinct variable specifiers.  Version of
       ~ naecoms using ~ ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fnaecoms-o_0 $f wff ph $.
	fnaecoms-o_1 $f set x $.
	fnaecoms-o_2 $f set y $.
	enaecoms-o_0 $e |- ( -. A. x x = y -> ph ) $.
	naecoms-o $p |- ( -. A. y y = x -> ph ) $= fnaecoms-o_0 fnaecoms-o_2 fnaecoms-o_1 weq fnaecoms-o_2 wal fnaecoms-o_1 fnaecoms-o_2 weq fnaecoms-o_1 wal fnaecoms-o_2 fnaecoms-o_1 weq fnaecoms-o_2 wal fnaecoms-o_0 fnaecoms-o_1 fnaecoms-o_2 aecom-o enaecoms-o_0 nsyl4 con1i $.
$}
$( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  Version of ~ hbnae
     using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fhbnae-o_0 $f set x $.
	fhbnae-o_1 $f set y $.
	fhbnae-o_2 $f set z $.
	hbnae-o $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $= fhbnae-o_0 fhbnae-o_1 weq fhbnae-o_0 wal fhbnae-o_2 fhbnae-o_0 fhbnae-o_1 fhbnae-o_2 hbae-o hbn $.
$}
$( Proof of ~ dvelimh that uses ~ ax-10o but not ~ ax-11o , ~ ax-10 , or
       ~ ax-11 .  Version of ~ dvelimh using ~ ax-10o instead of ~ ax10o .
       (Contributed by NM, 12-Nov-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	fdvelimf-o_0 $f wff ph $.
	fdvelimf-o_1 $f wff ps $.
	fdvelimf-o_2 $f set x $.
	fdvelimf-o_3 $f set y $.
	fdvelimf-o_4 $f set z $.
	edvelimf-o_0 $e |- ( ph -> A. x ph ) $.
	edvelimf-o_1 $e |- ( ps -> A. z ps ) $.
	edvelimf-o_2 $e |- ( z = y -> ( ph <-> ps ) ) $.
	dvelimf-o $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $= fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal fdvelimf-o_1 fdvelimf-o_1 fdvelimf-o_2 wal fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal wi wi fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal wi fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 wal fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 hba1-o fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal wi fdvelimf-o_4 fdvelimf-o_2 fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_2 ax-10o aecoms-o syl5 a1d fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_2 wal wi fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn wa fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_2 fdvelimf-o_4 fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_2 fdvelimf-o_4 fdvelimf-o_4 hbnae-o fdvelimf-o_2 fdvelimf-o_3 fdvelimf-o_4 hbnae-o hban fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn wa fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 fdvelimf-o_2 fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_2 fdvelimf-o_4 fdvelimf-o_2 hbnae-o fdvelimf-o_2 fdvelimf-o_3 fdvelimf-o_2 hbnae-o hban fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_2 wal wi fdvelimf-o_4 fdvelimf-o_3 fdvelimf-o_2 ax-12o imp fdvelimf-o_0 fdvelimf-o_0 fdvelimf-o_2 wal wi fdvelimf-o_2 fdvelimf-o_4 weq fdvelimf-o_2 wal wn fdvelimf-o_2 fdvelimf-o_3 weq fdvelimf-o_2 wal wn wa edvelimf-o_0 a1i hbimd hbald ex pm2.61i fdvelimf-o_0 fdvelimf-o_1 fdvelimf-o_4 fdvelimf-o_3 edvelimf-o_1 edvelimf-o_2 equsalh fdvelimf-o_4 fdvelimf-o_3 weq fdvelimf-o_0 wi fdvelimf-o_4 wal fdvelimf-o_1 fdvelimf-o_2 fdvelimf-o_0 fdvelimf-o_1 fdvelimf-o_4 fdvelimf-o_3 edvelimf-o_1 edvelimf-o_2 equsalh albii 3imtr3g $.
$}
$( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral2 using ~ ax-10o .  (Contributed by NM, 27-Feb-2005.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fdral2-o_0 $f wff ph $.
	fdral2-o_1 $f wff ps $.
	fdral2-o_2 $f set x $.
	fdral2-o_3 $f set y $.
	fdral2-o_4 $f set z $.
	edral2-o_0 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
	dral2-o $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $= fdral2-o_2 fdral2-o_3 weq fdral2-o_2 wal fdral2-o_0 fdral2-o_1 fdral2-o_4 fdral2-o_2 fdral2-o_3 fdral2-o_4 hbae-o edral2-o_0 albidh $.
$}
$( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  Version of ~ aev using
       ~ ax-10o .  (Contributed by NM, 8-Nov-2006.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
$v t $.
${
	$d t u v $.
	$d t u x y $.
	$d u w $.
	iaev-o_0 $f set u $.
	iaev-o_1 $f set t $.
	faev-o_0 $f set x $.
	faev-o_1 $f set y $.
	faev-o_2 $f set z $.
	faev-o_3 $f set w $.
	faev-o_4 $f set v $.
	aev-o $p |- ( A. x x = y -> A. z w = v ) $= faev-o_0 faev-o_1 weq faev-o_0 wal faev-o_3 faev-o_4 weq faev-o_2 faev-o_0 faev-o_1 faev-o_2 hbae-o faev-o_0 faev-o_1 weq faev-o_0 wal iaev-o_1 faev-o_1 weq iaev-o_1 wal iaev-o_0 faev-o_4 weq iaev-o_0 wal faev-o_3 faev-o_4 weq faev-o_0 faev-o_1 weq faev-o_0 wal iaev-o_1 faev-o_1 weq iaev-o_1 faev-o_0 faev-o_1 iaev-o_1 hbae-o faev-o_0 faev-o_1 weq iaev-o_1 faev-o_1 weq faev-o_0 iaev-o_1 faev-o_0 iaev-o_1 faev-o_1 ax-8 spimv alrimih iaev-o_1 faev-o_1 weq iaev-o_1 wal iaev-o_1 iaev-o_0 weq iaev-o_1 wal faev-o_4 iaev-o_0 weq faev-o_4 wal iaev-o_0 faev-o_4 weq iaev-o_0 wal iaev-o_1 faev-o_1 weq iaev-o_1 iaev-o_0 weq iaev-o_1 iaev-o_1 iaev-o_0 weq faev-o_1 iaev-o_1 faev-o_1 iaev-o_1 weq iaev-o_1 iaev-o_0 weq faev-o_1 iaev-o_0 faev-o_1 iaev-o_0 weq faev-o_1 iaev-o_1 weq iaev-o_0 iaev-o_1 weq iaev-o_1 iaev-o_0 weq faev-o_1 iaev-o_0 iaev-o_1 ax-8 iaev-o_0 iaev-o_1 equcomi syl6 spimv aecoms-o a5i-o iaev-o_1 iaev-o_0 weq iaev-o_1 wal faev-o_4 iaev-o_0 weq faev-o_4 iaev-o_1 iaev-o_0 faev-o_4 hbae-o iaev-o_1 iaev-o_0 weq faev-o_4 iaev-o_0 weq iaev-o_1 faev-o_4 iaev-o_1 faev-o_4 iaev-o_0 ax-8 spimv alrimih faev-o_4 iaev-o_0 aecom-o 3syl iaev-o_0 faev-o_4 weq faev-o_3 faev-o_4 weq iaev-o_0 faev-o_3 iaev-o_0 faev-o_3 faev-o_4 ax-8 spimv 3syl alrimih $.
$}
$( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-17 instead, to
       avoid reference to the redundant axiom ~ ax-16 .)  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x z $.
	$d y z $.
	fax17eq_0 $f set x $.
	fax17eq_1 $f set y $.
	fax17eq_2 $f set z $.
	ax17eq $p |- ( x = y -> A. z x = y ) $= fax17eq_2 fax17eq_0 weq fax17eq_2 wal fax17eq_2 fax17eq_1 weq fax17eq_2 wal fax17eq_0 fax17eq_1 weq fax17eq_0 fax17eq_1 weq fax17eq_2 wal wi fax17eq_0 fax17eq_1 fax17eq_2 ax-12o fax17eq_0 fax17eq_1 weq fax17eq_2 fax17eq_0 ax-16 fax17eq_0 fax17eq_1 weq fax17eq_2 fax17eq_1 ax-16 pm2.61ii $.
$}
$( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq2 using ~ ax-11o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d w z x $.
	$d w y $.
	idveeq2-o_0 $f set w $.
	fdveeq2-o_0 $f set x $.
	fdveeq2-o_1 $f set y $.
	fdveeq2-o_2 $f set z $.
	dveeq2-o $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $= fdveeq2-o_2 idveeq2-o_0 weq fdveeq2-o_2 fdveeq2-o_1 weq fdveeq2-o_0 fdveeq2-o_1 idveeq2-o_0 fdveeq2-o_2 idveeq2-o_0 weq fdveeq2-o_0 ax-17 fdveeq2-o_2 fdveeq2-o_1 weq idveeq2-o_0 ax-17 idveeq2-o_0 fdveeq2-o_1 fdveeq2-o_2 equequ2 dvelimf-o $.
$}
$( Version of ~ dveeq2 using ~ ax-16 instead of ~ ax-17 .  TO DO:  Recover
       proof from older set.mm to remove use of ~ ax-17 .  (Contributed by NM,
       29-Apr-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d w z x $.
	$d w y $.
	idveeq2-o16_0 $f set w $.
	fdveeq2-o16_0 $f set x $.
	fdveeq2-o16_1 $f set y $.
	fdveeq2-o16_2 $f set z $.
	dveeq2-o16 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $= fdveeq2-o16_2 idveeq2-o16_0 weq fdveeq2-o16_2 fdveeq2-o16_1 weq fdveeq2-o16_0 fdveeq2-o16_1 idveeq2-o16_0 fdveeq2-o16_2 idveeq2-o16_0 fdveeq2-o16_0 ax17eq idveeq2-o16_0 fdveeq2-o16_1 fdveeq2-o16_2 equequ2 dvelimALT $.
$}
$( A generalization of axiom ~ ax-16 .  Version of ~ a16g using ~ ax-10o .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x y $.
	fa16g-o_0 $f wff ph $.
	fa16g-o_1 $f set x $.
	fa16g-o_2 $f set y $.
	fa16g-o_3 $f set z $.
	a16g-o $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $= fa16g-o_1 fa16g-o_2 weq fa16g-o_1 wal fa16g-o_3 fa16g-o_1 weq fa16g-o_3 wal fa16g-o_0 fa16g-o_0 fa16g-o_1 wal fa16g-o_0 fa16g-o_3 wal fa16g-o_1 fa16g-o_2 fa16g-o_3 fa16g-o_3 fa16g-o_1 aev-o fa16g-o_0 fa16g-o_1 fa16g-o_2 ax-16 fa16g-o_3 fa16g-o_1 weq fa16g-o_3 wal fa16g-o_0 fa16g-o_3 wal fa16g-o_0 fa16g-o_1 wal fa16g-o_0 fa16g-o_0 fa16g-o_3 fa16g-o_1 fa16g-o_3 fa16g-o_1 weq fa16g-o_3 wal fa16g-o_0 biidd dral1-o biimprd sylsyld $.
$}
$( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq1 using ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d w z x $.
	$d w y $.
	idveeq1-o_0 $f set w $.
	fdveeq1-o_0 $f set x $.
	fdveeq1-o_1 $f set y $.
	fdveeq1-o_2 $f set z $.
	dveeq1-o $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= idveeq1-o_0 fdveeq1-o_2 weq fdveeq1-o_1 fdveeq1-o_2 weq fdveeq1-o_0 fdveeq1-o_1 idveeq1-o_0 idveeq1-o_0 fdveeq1-o_2 weq fdveeq1-o_0 ax-17 fdveeq1-o_1 fdveeq1-o_2 weq idveeq1-o_0 ax-17 idveeq1-o_0 fdveeq1-o_1 fdveeq1-o_2 equequ1 dvelimf-o $.
$}
$( Version of ~ dveeq1 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 29-Apr-2008.)  TO DO:  Recover proof from older set.mm to remove use
       of ~ ax-17 .  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d w z x $.
	$d w y $.
	idveeq1-o16_0 $f set w $.
	fdveeq1-o16_0 $f set x $.
	fdveeq1-o16_1 $f set y $.
	fdveeq1-o16_2 $f set z $.
	dveeq1-o16 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $= idveeq1-o16_0 fdveeq1-o16_2 weq fdveeq1-o16_1 fdveeq1-o16_2 weq fdveeq1-o16_0 fdveeq1-o16_1 idveeq1-o16_0 idveeq1-o16_0 fdveeq1-o16_2 fdveeq1-o16_0 ax17eq fdveeq1-o16_1 fdveeq1-o16_2 idveeq1-o16_0 ax17eq idveeq1-o16_0 fdveeq1-o16_1 fdveeq1-o16_2 equequ1 dvelimh $.
$}
$( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.)  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x z $.
	$d y z $.
	fax17el_0 $f set x $.
	fax17el_1 $f set y $.
	fax17el_2 $f set z $.
	ax17el $p |- ( x e. y -> A. z x e. y ) $= fax17el_2 fax17el_0 weq fax17el_2 wal fax17el_2 fax17el_1 weq fax17el_2 wal fax17el_0 fax17el_1 wel fax17el_0 fax17el_1 wel fax17el_2 wal wi fax17el_0 fax17el_1 fax17el_2 ax-15 fax17el_0 fax17el_1 wel fax17el_2 fax17el_0 ax-16 fax17el_0 fax17el_1 wel fax17el_2 fax17el_1 ax-16 pm2.61ii $.
$}
$( This theorem shows that, given ~ ax-16 , we can derive a version of
       ~ ax-10 .  However, it is weaker than ~ ax-10 because it has a distinct
       variable requirement.  (Contributed by Andrew Salmon, 27-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x z w $.
	iax10-16_0 $f set w $.
	fax10-16_0 $f set x $.
	fax10-16_1 $f set z $.
	ax10-16 $p |- ( A. x x = z -> A. z z = x ) $= fax10-16_0 fax10-16_1 weq fax10-16_0 wal fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi iax10-16_0 wal fax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_1 wal fax10-16_1 fax10-16_0 weq fax10-16_1 wal fax10-16_0 fax10-16_1 weq fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi iax10-16_0 wal fax10-16_0 fax10-16_0 fax10-16_1 weq fax10-16_0 wal fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi iax10-16_0 fax10-16_0 iax10-16_0 weq fax10-16_0 fax10-16_1 ax-16 alrimiv a5i-o fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi iax10-16_0 wal fax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_1 wal fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi iax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_0 fax10-16_1 fax10-16_0 fax10-16_1 weq fax10-16_0 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal wi fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 fax10-16_0 fax10-16_1 weq fax10-16_0 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_0 iax10-16_0 weq fax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 wal fax10-16_0 fax10-16_1 iax10-16_0 equequ1 fax10-16_0 iax10-16_0 weq fax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 wal wb fax10-16_0 fax10-16_1 weq fax10-16_0 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_0 fax10-16_1 fax10-16_0 fax10-16_1 iax10-16_0 equequ1 cbvalv a1i imbi12d albidv cbvalv biimpi fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_1 fax10-16_0 weq fax10-16_1 fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 fax10-16_0 weq iax10-16_0 fax10-16_1 fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 wal iax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_1 fax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 wal fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 fax10-16_1 iax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wal fax10-16_1 fax10-16_1 iax10-16_0 weq fax10-16_1 nfa1-o 19.23 albii fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi iax10-16_0 wal fax10-16_1 iax10-16_0 weq fax10-16_1 wal iax10-16_0 wal fax10-16_1 fax10-16_0 weq fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 iax10-16_0 weq fax10-16_1 wal iax10-16_0 fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 iax10-16_0 weq fax10-16_1 wal wi fax10-16_1 iax10-16_0 a9ev fax10-16_1 iax10-16_0 weq fax10-16_1 wex fax10-16_1 iax10-16_0 weq fax10-16_1 wal pm2.27 ax-mp alimi fax10-16_1 iax10-16_0 weq fax10-16_1 fax10-16_0 weq fax10-16_1 iax10-16_0 fax10-16_1 iax10-16_0 weq iax10-16_0 wal fax10-16_1 fax10-16_0 weq fax10-16_1 fax10-16_1 iax10-16_0 weq fax10-16_1 fax10-16_0 weq iax10-16_0 fax10-16_0 iax10-16_0 fax10-16_0 fax10-16_1 equequ2 spv sps-o a7s syl sylbi a7s a5i-o 3syl $.
$}
$( Version of ~ dveel2 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 10-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d w z x $.
	$d w y $.
	idveel2ALT_0 $f set w $.
	fdveel2ALT_0 $f set x $.
	fdveel2ALT_1 $f set y $.
	fdveel2ALT_2 $f set z $.
	dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $= fdveel2ALT_2 idveel2ALT_0 wel fdveel2ALT_2 fdveel2ALT_1 wel fdveel2ALT_0 fdveel2ALT_1 idveel2ALT_0 fdveel2ALT_2 idveel2ALT_0 fdveel2ALT_0 ax17el fdveel2ALT_2 fdveel2ALT_1 idveel2ALT_0 ax17el idveel2ALT_0 fdveel2ALT_1 fdveel2ALT_2 elequ2 dvelimh $.
$}
$( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  We can start with any formula ` ph ` in which ` x ` is
       not free.  (Contributed by NM, 21-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fax11f_0 $f wff ph $.
	fax11f_1 $f set x $.
	fax11f_2 $f set y $.
	eax11f_0 $e |- ( ph -> A. x ph ) $.
	ax11f $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11f_1 fax11f_2 weq fax11f_1 wal wn fax11f_1 fax11f_2 weq fax11f_0 fax11f_1 fax11f_2 weq fax11f_0 wi fax11f_1 wal wi fax11f_0 fax11f_1 fax11f_2 weq fax11f_0 wi fax11f_1 eax11f_0 fax11f_0 fax11f_1 fax11f_2 weq ax-1 alrimih a1ii $.
$}
$( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for equality predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x u v $.
	$d y u v $.
	$d z u v $.
	$d w u v $.
	iax11eq_0 $f set v $.
	iax11eq_1 $f set u $.
	fax11eq_0 $f set x $.
	fax11eq_1 $f set y $.
	fax11eq_2 $f set z $.
	fax11eq_3 $f set w $.
	ax11eq $p |- ( -. A. x x = y -> ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $= fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wi wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wa fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wi wi fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq fax11eq_0 19.26 fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_0 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 wal fax11eq_0 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 fax11eq_0 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_0 equid a1i ax-gen a1i fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wb fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_0 weq fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_2 fax11eq_0 equequ1 fax11eq_0 fax11eq_3 fax11eq_2 equequ2 sylan9bb sps-o fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_0 weq wi fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 nfa1-o fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq wa fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_0 weq fax11eq_2 fax11eq_0 weq fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_2 fax11eq_0 equequ1 fax11eq_0 fax11eq_3 fax11eq_2 equequ2 sylan9bb sps-o imbi2d albid imbi12d adantr mpbii exp32 sylbir fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_0 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa fax11eq_0 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_0 fax11eq_3 weq fax11eq_1 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq fax11eq_1 fax11eq_3 weq wb fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 fax11eq_3 equequ1 ad2antll fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_1 fax11eq_3 weq fax11eq_1 fax11eq_3 weq fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_1 fax11eq_3 weq fax11eq_1 fax11eq_3 weq fax11eq_0 wal wi fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_1 fax11eq_3 weq fax11eq_1 fax11eq_3 weq fax11eq_0 wal wi fax11eq_1 fax11eq_3 fax11eq_0 ax12o impcom adantrr fax11eq_1 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 fax11eq_1 fax11eq_3 fax11eq_0 equtrr alimi syl6 sylbid adantll fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wb fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_2 fax11eq_3 equequ1 sps-o fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq wi fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 fax11eq_2 fax11eq_0 fax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_2 weq fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_2 fax11eq_3 equequ1 sps-o imbi2d dral2-o imbi12d ad2antrr mpbid exp32 fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wa fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wa fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_2 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa fax11eq_2 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_3 weq fax11eq_0 wal fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_1 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_1 weq wb fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 fax11eq_2 equequ2 ad2antll fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa wa fax11eq_2 fax11eq_1 weq fax11eq_2 fax11eq_1 weq fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_2 fax11eq_1 weq fax11eq_2 fax11eq_1 weq fax11eq_0 wal wi fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_2 fax11eq_1 weq fax11eq_2 fax11eq_1 weq fax11eq_0 wal wi fax11eq_2 fax11eq_1 fax11eq_0 ax12o imp adantrr fax11eq_2 fax11eq_1 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_1 weq fax11eq_0 fax11eq_1 fax11eq_2 equequ2 biimprcd alimi syl6 sylbid adantlr fax11eq_0 fax11eq_3 weq fax11eq_0 wal fax11eq_2 fax11eq_0 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wb fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_1 weq wa fax11eq_0 fax11eq_3 weq fax11eq_0 wal fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_3 fax11eq_2 equequ2 sps-o fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_0 weq wi fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 fax11eq_3 fax11eq_0 fax11eq_0 fax11eq_3 weq fax11eq_0 wal fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_3 weq fax11eq_2 fax11eq_0 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_0 fax11eq_3 fax11eq_2 equequ2 sps-o imbi2d dral2-o imbi12d ad2antlr mpbid exp32 fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wi fax11eq_0 fax11eq_1 weq fax11eq_0 wal wn fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_1 weq fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_1 fax11eq_3 weq iax11eq_1 wex fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi iax11eq_1 fax11eq_3 a9ev fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi iax11eq_1 fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_0 wex iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wi iax11eq_0 fax11eq_2 a9ev fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi wi iax11eq_0 fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa wa iax11eq_0 iax11eq_1 weq fax11eq_0 fax11eq_1 weq iax11eq_0 iax11eq_1 weq wi fax11eq_0 wal wi fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wi iax11eq_0 iax11eq_1 weq fax11eq_0 fax11eq_1 weq iax11eq_0 iax11eq_1 weq wi fax11eq_0 iax11eq_0 iax11eq_1 weq fax11eq_0 fax11eq_1 weq ax-1 alrimiv fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa wa iax11eq_0 iax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq iax11eq_0 iax11eq_1 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa iax11eq_0 iax11eq_1 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_0 iax11eq_1 weq fax11eq_2 iax11eq_1 weq iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq iax11eq_0 fax11eq_2 iax11eq_1 equequ1 iax11eq_1 fax11eq_3 fax11eq_2 equequ2 sylan9bb adantl fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq iax11eq_0 iax11eq_1 weq wi fax11eq_0 wal fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 wal wb fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa wa iax11eq_0 fax11eq_2 weq fax11eq_0 wal iax11eq_1 fax11eq_3 weq fax11eq_0 wal wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn wa iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa iax11eq_0 fax11eq_2 weq fax11eq_0 wal iax11eq_1 fax11eq_3 weq fax11eq_0 wal wa fax11eq_0 fax11eq_2 weq fax11eq_0 wal wn iax11eq_0 fax11eq_2 weq iax11eq_0 fax11eq_2 weq fax11eq_0 wal fax11eq_0 fax11eq_3 weq fax11eq_0 wal wn iax11eq_1 fax11eq_3 weq iax11eq_1 fax11eq_3 weq fax11eq_0 wal fax11eq_0 fax11eq_2 iax11eq_0 dveeq2-o fax11eq_0 fax11eq_3 iax11eq_1 dveeq2-o im2anan9 imp iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq fax11eq_0 19.26 sylibr iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa fax11eq_0 wal fax11eq_0 fax11eq_1 weq iax11eq_0 iax11eq_1 weq wi fax11eq_0 fax11eq_1 weq fax11eq_2 fax11eq_3 weq wi fax11eq_0 iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa fax11eq_0 nfa1-o iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa fax11eq_0 wal iax11eq_0 iax11eq_1 weq fax11eq_2 fax11eq_3 weq fax11eq_0 fax11eq_1 weq iax11eq_0 fax11eq_2 weq iax11eq_1 fax11eq_3 weq wa iax11eq_0 iax11eq_1 weq fax11eq_2 fax11eq_3 weq wb fax11eq_0 iax11eq_0 fax11eq_2 weq iax11eq_0 iax11eq_1 weq fax11eq_2 iax11eq_1 weq iax11eq_1 fax11eq_3 weq fax11eq_2 fax11eq_3 weq iax11eq_0 fax11eq_2 iax11eq_1 equequ1 iax11eq_1 fax11eq_3 fax11eq_2 equequ2 sylan9bb sps-o imbi2d albid syl imbi12d mpbii exp32 exlimdv mpi exlimdv mpi a1d a1d 4cases $.
$}
$( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for membership predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x u v $.
	$d y u v $.
	$d z u v $.
	$d w u v $.
	iax11el_0 $f set v $.
	iax11el_1 $f set u $.
	fax11el_0 $f set x $.
	fax11el_1 $f set y $.
	fax11el_2 $f set z $.
	fax11el_3 $f set w $.
	ax11el $p |- ( -. A. x x = y -> ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $= fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wi wi fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wa fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wi wi fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq fax11el_0 19.26 fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_0 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_0 wel fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel fax11el_1 fax11el_1 wel wb fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel fax11el_1 fax11el_0 wel fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 fax11el_0 elequ1 fax11el_0 fax11el_1 fax11el_1 elequ2 bitrd adantl fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal wi fax11el_0 fax11el_1 weq fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_1 fax11el_1 wel fax11el_1 fax11el_1 wel fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal iax11el_0 iax11el_0 wel fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 iax11el_0 iax11el_0 iax11el_0 wel fax11el_0 ax-17 fax11el_1 fax11el_1 wel iax11el_0 ax-17 iax11el_0 fax11el_1 weq iax11el_0 iax11el_0 wel fax11el_1 iax11el_0 wel fax11el_1 fax11el_1 wel iax11el_0 fax11el_1 iax11el_0 elequ1 iax11el_0 fax11el_1 fax11el_1 elequ2 bitrd dvelimf-o fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel fax11el_1 fax11el_0 wel fax11el_1 fax11el_1 wel fax11el_0 fax11el_1 fax11el_0 elequ1 fax11el_0 fax11el_1 fax11el_1 elequ2 bitrd biimprcd alimi syl6 adantr sylbid adantl fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wb fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_0 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 fax11el_0 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_2 weq fax11el_0 fax11el_0 wel fax11el_2 fax11el_0 wel fax11el_0 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_2 fax11el_0 elequ1 fax11el_0 fax11el_3 fax11el_2 elequ2 sylan9bb sps-o fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 fax11el_0 wel wi fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 nfa1-o fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_0 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 weq wa fax11el_0 fax11el_0 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_2 weq fax11el_0 fax11el_0 wel fax11el_2 fax11el_0 wel fax11el_0 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_2 fax11el_0 elequ1 fax11el_0 fax11el_3 fax11el_2 elequ2 sylan9bb sps-o imbi2d albid imbi12d adantr mpbid exp32 sylbir fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wn wa fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wn wa fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_0 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_0 fax11el_3 wel fax11el_1 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel fax11el_1 fax11el_3 wel wb fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 fax11el_3 elequ1 ad2antll fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_1 fax11el_3 wel fax11el_1 fax11el_3 wel fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_1 fax11el_3 wel fax11el_1 fax11el_3 wel fax11el_0 wal wi fax11el_0 fax11el_1 weq fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_1 fax11el_3 wel fax11el_1 fax11el_3 wel fax11el_0 wal wi fax11el_1 fax11el_3 fax11el_0 ax-15 impcom adantrr fax11el_1 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel fax11el_1 fax11el_3 wel fax11el_0 fax11el_1 fax11el_3 elequ1 biimprcd alimi syl6 sylbid adantll fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wb fax11el_0 fax11el_3 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_2 fax11el_3 elequ1 sps-o fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 wel wi fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 fax11el_2 fax11el_0 fax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_2 weq fax11el_0 fax11el_3 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_2 fax11el_3 elequ1 sps-o imbi2d dral2-o imbi12d ad2antrr mpbid exp32 fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wa fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wa fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_2 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_2 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal wi fax11el_0 fax11el_3 weq fax11el_0 wal fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_2 fax11el_0 wel fax11el_2 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel fax11el_2 fax11el_1 wel wb fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 fax11el_2 elequ2 ad2antll fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa wa fax11el_2 fax11el_1 wel fax11el_2 fax11el_1 wel fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_2 fax11el_1 wel fax11el_2 fax11el_1 wel fax11el_0 wal wi fax11el_0 fax11el_1 weq fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_2 fax11el_1 wel fax11el_2 fax11el_1 wel fax11el_0 wal wi fax11el_2 fax11el_1 fax11el_0 ax-15 imp adantrr fax11el_2 fax11el_1 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel fax11el_2 fax11el_1 wel fax11el_0 fax11el_1 fax11el_2 elequ2 biimprcd alimi syl6 sylbid adantlr fax11el_0 fax11el_3 weq fax11el_0 wal fax11el_2 fax11el_0 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wb fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_1 weq wa fax11el_0 fax11el_3 weq fax11el_0 wal fax11el_2 fax11el_0 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_2 fax11el_0 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_3 fax11el_2 elequ2 sps-o fax11el_0 fax11el_1 weq fax11el_2 fax11el_0 wel wi fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 fax11el_3 fax11el_0 fax11el_0 fax11el_3 weq fax11el_0 wal fax11el_2 fax11el_0 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_0 fax11el_3 weq fax11el_2 fax11el_0 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_0 fax11el_3 fax11el_2 elequ2 sps-o imbi2d dral2-o imbi12d ad2antlr mpbid exp32 fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wi fax11el_0 fax11el_1 weq fax11el_0 wal wn fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_1 weq fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_1 fax11el_3 weq iax11el_1 wex fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi iax11el_1 fax11el_3 a9ev fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi iax11el_1 fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_0 wex iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wi iax11el_0 fax11el_2 a9ev fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi wi iax11el_0 fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa wa iax11el_0 iax11el_1 wel fax11el_0 fax11el_1 weq iax11el_0 iax11el_1 wel wi fax11el_0 wal wi fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wi iax11el_0 iax11el_1 wel fax11el_0 fax11el_1 weq iax11el_0 iax11el_1 wel wi fax11el_0 iax11el_0 iax11el_1 wel fax11el_0 fax11el_1 weq ax-1 alrimiv fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa wa iax11el_0 iax11el_1 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq iax11el_0 iax11el_1 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa iax11el_0 iax11el_1 wel fax11el_2 fax11el_3 wel wb fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_0 iax11el_1 wel fax11el_2 iax11el_1 wel iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel iax11el_0 fax11el_2 iax11el_1 elequ1 iax11el_1 fax11el_3 fax11el_2 elequ2 sylan9bb adantl fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq iax11el_0 iax11el_1 wel wi fax11el_0 wal fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 wal wb fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa wa iax11el_0 fax11el_2 weq fax11el_0 wal iax11el_1 fax11el_3 weq fax11el_0 wal wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_2 weq fax11el_0 wal wn fax11el_0 fax11el_3 weq fax11el_0 wal wn wa iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa iax11el_0 fax11el_2 weq fax11el_0 wal iax11el_1 fax11el_3 weq fax11el_0 wal wa fax11el_0 fax11el_2 weq fax11el_0 wal wn iax11el_0 fax11el_2 weq iax11el_0 fax11el_2 weq fax11el_0 wal fax11el_0 fax11el_3 weq fax11el_0 wal wn iax11el_1 fax11el_3 weq iax11el_1 fax11el_3 weq fax11el_0 wal fax11el_0 fax11el_2 iax11el_0 dveeq2-o fax11el_0 fax11el_3 iax11el_1 dveeq2-o im2anan9 imp iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq fax11el_0 19.26 sylibr iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa fax11el_0 wal fax11el_0 fax11el_1 weq iax11el_0 iax11el_1 wel wi fax11el_0 fax11el_1 weq fax11el_2 fax11el_3 wel wi fax11el_0 iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa fax11el_0 nfa1-o iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa fax11el_0 wal iax11el_0 iax11el_1 wel fax11el_2 fax11el_3 wel fax11el_0 fax11el_1 weq iax11el_0 fax11el_2 weq iax11el_1 fax11el_3 weq wa iax11el_0 iax11el_1 wel fax11el_2 fax11el_3 wel wb fax11el_0 iax11el_0 fax11el_2 weq iax11el_0 iax11el_1 wel fax11el_2 iax11el_1 wel iax11el_1 fax11el_3 weq fax11el_2 fax11el_3 wel iax11el_0 fax11el_2 iax11el_1 elequ1 iax11el_1 fax11el_3 fax11el_2 elequ2 sylan9bb sps-o imbi2d albid syl imbi12d mpbii exp32 exlimdv mpi exlimdv mpi a1d a1d 4cases $.
$}
$( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Negation case.  (Contributed by NM,
       21-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	fax11indn_0 $f wff ph $.
	fax11indn_1 $f set x $.
	fax11indn_2 $f set y $.
	eax11indn_0 $e |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
	ax11indn $p |- ( -. A. x x = y -> ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $= fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 wn fax11indn_1 fax11indn_2 weq fax11indn_0 wn wi fax11indn_1 wal fax11indn_1 fax11indn_2 weq fax11indn_0 wn wa fax11indn_1 fax11indn_2 weq fax11indn_0 wn wa fax11indn_1 wex fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 wn wi fax11indn_1 wal fax11indn_1 fax11indn_2 weq fax11indn_0 wn wa fax11indn_1 19.8a fax11indn_1 fax11indn_2 weq fax11indn_0 wn wa fax11indn_1 wex fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 wn wi fax11indn_1 wal fax11indn_1 fax11indn_2 weq fax11indn_0 fax11indn_1 exanali fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 wn wi fax11indn_1 fax11indn_1 fax11indn_2 weq fax11indn_1 hbn1 fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 hbn1 fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal wn fax11indn_0 wn fax11indn_1 fax11indn_2 weq fax11indn_1 wal wn fax11indn_1 fax11indn_2 weq fax11indn_0 fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal wi fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal wn fax11indn_0 wn wi eax11indn_0 fax11indn_0 fax11indn_1 fax11indn_2 weq fax11indn_0 wi fax11indn_1 wal con3 syl6 com23 alrimdh syl5bi syl5 exp3a $.
$}
$( Induction step for constructing a substitution instance of ~ ax-11o
         without using ~ ax-11o .  Implication case.  (Contributed by NM,
         21-Jan-2007.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
${
	fax11indi_0 $f wff ph $.
	fax11indi_1 $f wff ps $.
	fax11indi_2 $f set x $.
	fax11indi_3 $f set y $.
	eax11indi_0 $e |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
	eax11indi_1 $e |- ( -. A. x x = y -> ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
	ax11indi $p |- ( -. A. x x = y -> ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $= fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 wal wi fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq wa fax11indi_0 fax11indi_1 fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 wal fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq wa fax11indi_0 wn fax11indi_2 fax11indi_3 weq fax11indi_0 wn wi fax11indi_2 wal fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 wal fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq fax11indi_0 wn fax11indi_2 fax11indi_3 weq fax11indi_0 wn wi fax11indi_2 wal wi fax11indi_0 fax11indi_2 fax11indi_3 eax11indi_0 ax11indn imp fax11indi_2 fax11indi_3 weq fax11indi_0 wn wi fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 fax11indi_0 wn fax11indi_0 fax11indi_1 wi fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 pm2.21 imim2i alimi syl6 fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq wa fax11indi_1 fax11indi_2 fax11indi_3 weq fax11indi_1 wi fax11indi_2 wal fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 wal fax11indi_2 fax11indi_3 weq fax11indi_2 wal wn fax11indi_2 fax11indi_3 weq fax11indi_1 fax11indi_2 fax11indi_3 weq fax11indi_1 wi fax11indi_2 wal wi eax11indi_1 imp fax11indi_2 fax11indi_3 weq fax11indi_1 wi fax11indi_2 fax11indi_3 weq fax11indi_0 fax11indi_1 wi wi fax11indi_2 fax11indi_1 fax11indi_0 fax11indi_1 wi fax11indi_2 fax11indi_3 weq fax11indi_1 fax11indi_0 ax-1 imim2i alimi syl6 jad ex $.
$}
$( Lemma for ~ ax11inda2 and ~ ax11inda .  (Contributed by NM,
       24-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	fax11indalem_0 $f wff ph $.
	fax11indalem_1 $f set x $.
	fax11indalem_2 $f set y $.
	fax11indalem_3 $f set z $.
	eax11indalem_0 $e |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
	ax11indalem $p |- ( -. A. y y = z -> ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $= fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi wi wi fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi wi wi fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi wi fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi fax11indalem_3 fax11indalem_1 fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_0 fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 wal wi fax11indalem_1 wal fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal fax11indalem_0 fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 wal wi fax11indalem_1 wal wi fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_0 fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 wal wi fax11indalem_1 fax11indalem_0 fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq ax-1 a5i-o a1i fax11indalem_0 fax11indalem_0 fax11indalem_3 fax11indalem_1 fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_0 biidd dral1-o fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 wal wi fax11indalem_3 fax11indalem_1 fax11indalem_1 fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_0 fax11indalem_3 wal fax11indalem_0 fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_0 fax11indalem_3 fax11indalem_1 fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_0 biidd dral1-o imbi2d dral2-o 3imtr4d aecoms-o a1d a1d adantr fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn wa fax11indalem_1 fax11indalem_2 weq wa fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn wa fax11indalem_1 fax11indalem_2 weq wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_0 fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal fax11indalem_3 wal wi fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq simplr fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal wn fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal wi fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_3 fax11indalem_1 aecom-o con3i fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal fax11indalem_3 fax11indalem_2 aecom-o con3i fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal wn fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal wi fax11indalem_1 fax11indalem_2 fax11indalem_3 ax12o imp syl2an imp adantlr fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal wa fax11indalem_0 fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal fax11indalem_3 fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_3 fax11indalem_1 fax11indalem_2 fax11indalem_3 hbnae-o fax11indalem_1 fax11indalem_2 weq fax11indalem_3 hba1-o hban fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal wi fax11indalem_1 fax11indalem_2 weq fax11indalem_3 ax-4 fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal wi eax11indalem_0 imp sylan2 alimdh syl2anc fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal wi fax11indalem_1 fax11indalem_2 weq fax11indalem_1 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_1 wal fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_3 wal fax11indalem_1 wal fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_3 fax11indalem_1 ax-7 fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi fax11indalem_1 fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_1 fax11indalem_1 fax11indalem_3 fax11indalem_1 hbnae-o fax11indalem_2 fax11indalem_3 fax11indalem_1 hbnae-o hban fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wnf fax11indalem_1 fax11indalem_2 weq fax11indalem_0 wi fax11indalem_3 wal fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 wal wi wb fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn wa fax11indalem_1 fax11indalem_2 weq fax11indalem_3 fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_3 fax11indalem_1 fax11indalem_3 fax11indalem_3 hbnae-o fax11indalem_2 fax11indalem_3 fax11indalem_3 hbnae-o hban fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal wn fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal wn fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal wi fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal wn fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal fax11indalem_1 fax11indalem_3 weq fax11indalem_1 wal fax11indalem_3 fax11indalem_1 aecom-o con3i fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal fax11indalem_2 fax11indalem_3 weq fax11indalem_2 wal fax11indalem_3 fax11indalem_2 aecom-o con3i fax11indalem_3 fax11indalem_1 weq fax11indalem_3 wal wn fax11indalem_3 fax11indalem_2 weq fax11indalem_3 wal wn fax11indalem_1 fax11indalem_2 weq fax11indalem_1 fax11indalem_2 weq fax11indalem_3 wal wi fax11indalem_1 fax11indalem_2 fax11indalem_3 ax12o imp syl2an nfdh fax11indalem_1 fax11indalem_2 weq fax11indalem_0 fax11indalem_3 19.21t syl albidh syl5ib ad2antrr syld exp31 pm2.61ian $.
$}
$( A proof of ~ ax11inda2 that is slightly more direct.  (Contributed by
       NM, 4-May-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d z y $.
	fax11inda2ALT_0 $f wff ph $.
	fax11inda2ALT_1 $f set x $.
	fax11inda2ALT_2 $f set y $.
	fax11inda2ALT_3 $f set z $.
	eax11inda2ALT_0 $e |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
	ax11inda2ALT $p |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $= fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi wi wi fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi wi fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 weq fax11inda2ALT_3 wal fax11inda2ALT_0 fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 wal wi fax11inda2ALT_1 wal fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal fax11inda2ALT_0 fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 wal wi fax11inda2ALT_1 wal wi fax11inda2ALT_3 fax11inda2ALT_1 weq fax11inda2ALT_3 wal fax11inda2ALT_0 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 wal wi fax11inda2ALT_1 fax11inda2ALT_0 fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq ax-1 a5i-o a1i fax11inda2ALT_0 fax11inda2ALT_0 fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 weq fax11inda2ALT_3 wal fax11inda2ALT_0 biidd dral1-o fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 wal wi fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 weq fax11inda2ALT_3 wal fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_0 fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_0 fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 weq fax11inda2ALT_3 wal fax11inda2ALT_0 biidd dral1-o imbi2d dral2-o 3imtr4d aecoms-o a1d a1d fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn wa fax11inda2ALT_1 fax11inda2ALT_2 weq wa fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn wa fax11inda2ALT_1 fax11inda2ALT_2 weq wa fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal fax11inda2ALT_0 fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal fax11inda2ALT_3 wal wi fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq simplr fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal wi fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_2 dveeq1-o naecoms-o imp adantlr fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal wa fax11inda2ALT_0 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_2 fax11inda2ALT_3 hbnae-o fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 hba1-o hban fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal wi fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 ax-4 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal wi eax11inda2ALT_0 imp sylan2 alimdh syl2anc fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal wi fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_1 wal fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_3 wal fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_3 fax11inda2ALT_1 ax-7 fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi fax11inda2ALT_1 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 hbnae-o fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wnf fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 wi fax11inda2ALT_3 wal fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 wal wi wb fax11inda2ALT_1 fax11inda2ALT_3 weq fax11inda2ALT_1 wal wn fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_3 hbnae-o fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_3 wal wi fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_3 fax11inda2ALT_1 fax11inda2ALT_2 dveeq1-o naecoms-o nfdh fax11inda2ALT_1 fax11inda2ALT_2 weq fax11inda2ALT_0 fax11inda2ALT_3 19.21t syl albidh syl5ib ad2antrr syld exp31 pm2.61i $.
$}
$( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax11inda .  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d z y $.
	fax11inda2_0 $f wff ph $.
	fax11inda2_1 $f set x $.
	fax11inda2_2 $f set y $.
	fax11inda2_3 $f set z $.
	eax11inda2_0 $e |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
	ax11inda2 $p |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $= fax11inda2_2 fax11inda2_3 weq fax11inda2_2 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_1 wal wn fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_1 wal wi wi wi fax11inda2_2 fax11inda2_3 weq fax11inda2_2 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_1 wal wi wi fax11inda2_1 fax11inda2_2 weq fax11inda2_1 wal wn fax11inda2_2 fax11inda2_3 weq fax11inda2_2 wal fax11inda2_0 fax11inda2_3 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_1 wal wi fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_2 fax11inda2_3 weq fax11inda2_2 wal fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_1 wal fax11inda2_0 fax11inda2_3 wal fax11inda2_1 fax11inda2_2 weq ax-1 fax11inda2_1 fax11inda2_2 weq fax11inda2_0 fax11inda2_3 wal wi fax11inda2_2 fax11inda2_3 fax11inda2_1 a16g-o syl5 a1d a1d fax11inda2_0 fax11inda2_1 fax11inda2_2 fax11inda2_3 eax11inda2_0 ax11indalem pm2.61i $.
$}
$( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax11inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.)  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d w ph $.
	$d w x $.
	$d w y $.
	$d w z $.
	fax11inda_0 $f wff ph $.
	fax11inda_1 $f set x $.
	fax11inda_2 $f set y $.
	fax11inda_3 $f set z $.
	fax11inda_4 $f set w $.
	eax11inda_0 $e |- ( -. A. x x = w -> ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
	ax11inda $p |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $= fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq fax11inda_4 wex fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi wi fax11inda_4 fax11inda_2 a9ev fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi wi fax11inda_4 fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi wi fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_1 fax11inda_4 weq fax11inda_1 wal wn fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi wi fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi wi fax11inda_0 fax11inda_1 fax11inda_4 fax11inda_3 eax11inda_0 ax11inda2 fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_1 fax11inda_4 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi wi fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_1 wal wn fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn wb fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_2 fax11inda_4 dveeq2-o imp fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_1 wal fax11inda_1 fax11inda_2 weq fax11inda_1 wal fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq fax11inda_1 fax11inda_4 fax11inda_2 weq fax11inda_1 hba1-o fax11inda_4 fax11inda_2 weq fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq wb fax11inda_1 fax11inda_4 fax11inda_2 fax11inda_1 equequ2 sps-o albidh notbid syl fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wi fax11inda_4 fax11inda_2 weq fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq wb fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 fax11inda_1 equequ2 adantl fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal fax11inda_0 fax11inda_3 wal fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq wa fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 wal wb fax11inda_1 fax11inda_2 weq fax11inda_1 wal wn fax11inda_4 fax11inda_2 weq fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_2 fax11inda_4 dveeq2-o imp fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal wi fax11inda_1 fax11inda_4 fax11inda_2 weq fax11inda_1 hba1-o fax11inda_4 fax11inda_2 weq fax11inda_1 wal fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq fax11inda_0 fax11inda_3 wal fax11inda_4 fax11inda_2 weq fax11inda_1 fax11inda_4 weq fax11inda_1 fax11inda_2 weq wb fax11inda_1 fax11inda_4 fax11inda_2 fax11inda_1 equequ2 sps-o imbi1d albidh syl imbi2d imbi12d imbi12d mpbii ex exlimdv mpi pm2.43i $.
$}
$( Recovery of ~ ax-11o from ~ ax11v without using ~ ax-11o .  The
       hypothesis is even weaker than ~ ax11v , with ` z ` both distinct from
       ` x ` _and_ not occurring in ` ph ` .  Thus, the hypothesis provides an
       alternate axiom that can be used in place of ~ ax-11o .  (Contributed by
       NM, 2-Feb-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	fax11v2-o_0 $f wff ph $.
	fax11v2-o_1 $f set x $.
	fax11v2-o_2 $f set y $.
	fax11v2-o_3 $f set z $.
	eax11v2-o_0 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
	ax11v2-o $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_3 wex fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wi wi fax11v2-o_3 fax11v2-o_2 a9ev fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wi wi fax11v2-o_3 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wi wi fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq wa fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 wal wi wi fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wi wi eax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq wa fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 wal wi fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wi fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_1 fax11v2-o_2 weq wb fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 fax11v2-o_1 equequ2 adantl fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq wa fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 wal fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal fax11v2-o_0 fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq wa fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 wal fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 wal fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 wal wb fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_1 wal wn fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 wal fax11v2-o_1 fax11v2-o_2 fax11v2-o_3 dveeq2-o imp fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 wal fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi fax11v2-o_1 fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 nfa1-o fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_0 wi fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 wi wb fax11v2-o_1 fax11v2-o_3 fax11v2-o_2 weq fax11v2-o_1 fax11v2-o_3 weq fax11v2-o_1 fax11v2-o_2 weq fax11v2-o_0 fax11v2-o_3 fax11v2-o_2 fax11v2-o_1 equequ2 imbi1d sps-o albid syl imbi2d imbi12d mpbii ex exlimdv mpi $.
$}
$( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 , without using
       ~ ax-11 or ~ ax-11o .  The hypothesis is even weaker than ~ ax-11 , with
       ` z ` both distinct from ` x ` and not occurring in ` ph ` .  Thus, the
       hypothesis provides an alternate axiom that can be used in place of
       ~ ax-11 , if we also hvae ~ ax-10o which this proof uses .  As theorem
       ~ ax11 shows, the distinct variable conditions are optional.  An open
       problem is whether we can derive this with ~ ax-10 instead of
       ~ ax-10o .  (Contributed by NM, 2-Feb-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x z $.
	$d y z $.
	$d z ph $.
	fax11a2-o_0 $f wff ph $.
	fax11a2-o_1 $f set x $.
	fax11a2-o_2 $f set y $.
	fax11a2-o_3 $f set z $.
	eax11a2-o_0 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
	ax11a2-o $p |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $= fax11a2-o_0 fax11a2-o_1 fax11a2-o_2 fax11a2-o_3 fax11a2-o_0 fax11a2-o_0 fax11a2-o_3 wal fax11a2-o_1 fax11a2-o_3 weq fax11a2-o_1 fax11a2-o_3 weq fax11a2-o_0 wi fax11a2-o_1 wal fax11a2-o_0 fax11a2-o_3 ax-17 eax11a2-o_0 syl5 ax11v2-o $.
$}
$( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See theorem ~ ax10from10o for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o or ~ ax10o-o ,
     except by theorems specifically studying the latter's properties.
     (Contributed by NM, 16-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax10o-o_0 $f wff ph $.
	fax10o-o_1 $f set x $.
	fax10o-o_2 $f set y $.
	ax10o-o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $= fax10o-o_1 fax10o-o_2 weq fax10o-o_1 wal fax10o-o_2 fax10o-o_1 weq fax10o-o_2 wal fax10o-o_0 fax10o-o_1 wal fax10o-o_2 fax10o-o_1 weq fax10o-o_0 wi fax10o-o_2 wal fax10o-o_0 fax10o-o_2 wal fax10o-o_1 fax10o-o_2 ax-10 fax10o-o_1 fax10o-o_2 weq fax10o-o_0 fax10o-o_1 wal fax10o-o_2 fax10o-o_1 weq fax10o-o_0 wi fax10o-o_2 wal wi fax10o-o_1 fax10o-o_0 fax10o-o_1 wal fax10o-o_2 fax10o-o_1 weq fax10o-o_0 wi fax10o-o_2 wal wi fax10o-o_2 fax10o-o_1 fax10o-o_0 fax10o-o_2 fax10o-o_1 ax11 equcoms sps-o fax10o-o_2 fax10o-o_1 weq fax10o-o_2 fax10o-o_1 weq fax10o-o_0 wi fax10o-o_0 fax10o-o_2 fax10o-o_2 fax10o-o_1 weq fax10o-o_0 pm2.27 al2imi sylsyld $.
$}

