$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-14_(Right_Membership_Equality).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Logical redundancy of ax-6 , ax-7 , ax-11 , ax-12

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The orginal axiom schemes of Tarski's predicate calculus are ~ ax-5 ,
  ~ ax-17 , ~ ax9v , ~ ax-8 , ~ ax-13 , and ~ ax-14 , together with rule
  ~ ax-gen .  See ~ http://us.metamath.org/mpeuni/mmset.html#compare .  They
  are given as axiom schemes B4 through B8 in [KalishMontague] p. 81.  These
  are shown to be logically complete by Theorem 1 of [KalishMontague] p. 85.

  The axiom system of set.mm includes the auxiliary axiom schemes ~ ax-6 ,
  ~ ax-7 , ~ ax-12 , and ~ ax-11 , which are not part of Tarski's axiom
  schemes.  They are used (and we conjecture are required) to make our system
  "metalogically complete" i.e. able to prove directly all possible schemes
  with wff and set metavariables, bundled or not, whose object-language
  instances are valid.  ( ~ ax-11 has been proved to be required; see
  ~ http://us.metamath.org/award2003.html#9a .  Metalogical independence of the
  other three are open problems.)

  (There are additional predicate calculus axiom schemes included in set.mm
  such as ~ ax-4 , but they can all be proved as theorems from the above.)

  Terminology:  Two set (individual) metavariables are "bundled" in an axiom or
  theorem scheme when there is no distinct variable constraint ($d) imposed on
  them.  (The term "bundled" is due to Raph Levien.)  For example, the ` x `
  and ` y ` in ~ ax9 are bundled, but they are not in ~ ax9v . We also say that
  a scheme is bundled when it has at least one pair of bundled set
  metavariables.  If distinct variable conditions are added to all set
  metavariable pairs in a bundled scheme, we call that the "principal" instance
  of the bundled scheme.  For example, ~ ax9v is the principal instance of
  ~ ax9 . Whenever a common variable is substituted for two or more bundled
  variables in an axiom or theorem scheme, we call the substitution instance
  "degenerate".  For example, the instance ` -. A. x -. x = x ` of ~ ax9 is
  degenerate.  An advantage of bundling is ease of use since there are fewer
  distinct variable restrictions ($d) to be concerned with.  There is also a
  small economy in being able to state principal and degenerate instances
  simultaneously.  A disadvantage is that bundling may present difficulties in
  translations to other proof languages, which typically lack the concept (in
  part because their variables often represent the variables of the object
  language rather than metavariables ranging over them).

  Because Tarski's axiom schemes are logically complete, they can be used to
  prove any object-language instance of ~ ax-6 , ~ ax-7 , ~ ax-11 , and ~ ax-12
  . "Translating" this to Metamath, it means that Tarski's axioms can prove any
  substitution instance of ~ ax-6 , ~ ax-7 , ~ ax-11 , or ~ ax-12 in which (1)
  there are no wff metavariables and (2) all set metavariables are mutually
  distinct i.e. are not bundled.  In effect this is mimicking the object
  language by pretending that each set metavariable is an object-language
  variable.  (There may also be specific instances with wff metavariables
  and/or bundling that are directly provable from Tarski's axiom schemes, but
  it isn't guaranteed.  Whether all of them are possible is part of the still
  open metalogical independence problem for our additional axiom schemes.)

  It can be useful to see how this can be done, both to show that our
  additional schemes are valid metatheorems of Tarski's system and to be able
  to translate object language instances of our proofs into proofs that would
  work with a system using only Tarski's original schemes.  In addition, it may
  (or may not) provide insight into the conjectured metalogical independence of
  our additional schemes.

  The new theorem schemes ~ ax6w , ~ ax7w , ~ ax11w , and ~ ax12w are
  derived using only Tarski's axiom schemes, showing that Tarski's schemes can
  be used to derive all substitution instances of ~ ax-6 , ~ ax-7 , ~ ax-11 ,
  and ~ ax-12 meeting conditions (1) and (2).  (The "w" suffix stands for "weak
  version".)  Each hypothesis of ~ ax6w , ~ ax7w , and ~ ax11w is of the
  form ` ( x = y -> ( ph <-> ps ) ) ` where ` ps ` is an auxiliary or "dummy"
  wff metavariable in which ` x ` doesn't occur.  We can show by induction on
  formula length that the hypotheses can be eliminated in all cases meeting
  conditions (1) and (2).  The example ~ ax11wdemo illustrates the techniques
  (equality theorems and bound variable renaming) used to achieve this.

  We also show the degenerate instances for axioms with bundled variables in
  ~ ax7dgen , ~ ax11dgen , ~ ax12dgen1 , ~ ax12dgen2 , ~ ax12dgen3 , and
  ~ ax12dgen4 . (Their proofs are trivial, but we include them to be thorough.)
  Combining the principal and degenerate cases _outside_ of Metamath, we show
  that the bundled schemes ~ ax-6 , ~ ax-7 , ~ ax-11 , and ~ ax-12 are schemes
  of Tarski's system, meaning that all object language instances they generate
  are theorems of Tarski's system.

  It is interesting that Tarski used the bundled scheme ~ ax-9 in an older
  system, so it seems the main purpose of his later ~ ax9v was just to show
  that the weaker unbundled form is sufficient rather than an aesthetic
  objection to bundled free and bound variables.  Since we adopt the
  bundled ~ ax-9 as our official axiom, we  show that the degenerate
  instance holds in ~ ax9dgen .

  The case of ~ sp is curious:  originally an axiom of Tarski's system, it
  was proved redundant by Lemma 9 of [KalishMontague] p. 86.  However, the
  proof is by induction on formula length, and the compact scheme form
  ` A. x ph -> ph ` apparently cannot be proved directly from Tarski's other
  axioms.  The best we can do seems to be ~ spw , again requiring
  substitution instances of ` ph ` that meet conditions (1) and (2) above.
  Note that our direct proof ~ sp requires ~ ax-11 , which is not part of
  Tarski's system.

$)
$( Tarski's system uses the weaker ~ ax9v instead of the bundled ~ ax-9 ,
       so here we show that the degenerate case of ~ ax-9 can be derived.
       (Contributed by NM, 23-Apr-2017.) $)
${
	fax9dgen_0 $f set x $.
	ax9dgen $p |- -. A. x -. x = x $= fax9dgen_0 fax9dgen_0 weq wn fax9dgen_0 wal fax9dgen_0 fax9dgen_0 weq fax9dgen_0 equid fax9dgen_0 fax9dgen_0 weq wn fax9dgen_0 fax9dgen_0 fax9dgen_0 weq fax9dgen_0 equid notnoti spfalw mt2 $.
$}
$( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 9-Apr-2017.) $)
${
	$d y ph $.
	$d x ps $.
	$d x y $.
	fax6w_0 $f wff ph $.
	fax6w_1 $f wff ps $.
	fax6w_2 $f set x $.
	fax6w_3 $f set y $.
	eax6w_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	ax6w $p |- ( -. A. x ph -> A. x -. A. x ph ) $= fax6w_0 fax6w_1 fax6w_2 fax6w_3 eax6w_0 hbn1w $.
$}
$( Weak version of ~ ax-7 from which we can prove any ~ ax-7 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  Unlike ~ ax-7 , this theorem requires that ` x ` and ` y ` be
       distinct i.e. are not bundled.  (Contributed by NM, 10-Apr-2017.) $)
${
	$d y z $.
	$d x y $.
	$d z ph $.
	$d y ps $.
	fax7w_0 $f wff ph $.
	fax7w_1 $f wff ps $.
	fax7w_2 $f set x $.
	fax7w_3 $f set y $.
	fax7w_4 $f set z $.
	eax7w_0 $e |- ( y = z -> ( ph <-> ps ) ) $.
	ax7w $p |- ( A. x A. y ph -> A. y A. x ph ) $= fax7w_0 fax7w_1 fax7w_2 fax7w_3 fax7w_4 eax7w_0 alcomiw $.
$}
$( Degenerate instance of ~ ax-7 where bundled variables ` x ` and ` y ` have
     a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax7dgen_0 $f wff ph $.
	fax7dgen_1 $f set x $.
	ax7dgen $p |- ( A. x A. x ph -> A. x A. x ph ) $= fax7dgen_0 fax7dgen_1 wal fax7dgen_1 wal id $.
$}
$( Lemma for weak version of ~ ax-11 .  Uses only Tarski's FOL axiom
       schemes.  In some cases, this lemma may lead to shorter proofs than
       ~ ax11w .  (Contributed by NM, 10-Apr-2017.) $)
${
	$d x ps $.
	fax11wlem_0 $f wff ph $.
	fax11wlem_1 $f wff ps $.
	fax11wlem_2 $f set x $.
	fax11wlem_3 $f set y $.
	eax11wlem_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	ax11wlem $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $= fax11wlem_0 fax11wlem_1 fax11wlem_2 fax11wlem_3 eax11wlem_0 fax11wlem_1 fax11wlem_2 ax-17 ax11i $.
$}
$( Weak version of ~ ax-11 from which we can prove any ~ ax-11 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  An instance of the first hypothesis will normally require that
       ` x ` and ` y ` be distinct (unless ` x ` does not occur in ` ph ` ).
       (Contributed by NM, 10-Apr-2017.) $)
${
	$d y z $.
	$d x ps $.
	$d z ph $.
	$d y ch $.
	fax11w_0 $f wff ph $.
	fax11w_1 $f wff ps $.
	fax11w_2 $f wff ch $.
	fax11w_3 $f set x $.
	fax11w_4 $f set y $.
	fax11w_5 $f set z $.
	eax11w_0 $e |- ( x = y -> ( ph <-> ps ) ) $.
	eax11w_1 $e |- ( y = z -> ( ph <-> ch ) ) $.
	ax11w $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $= fax11w_0 fax11w_4 wal fax11w_0 fax11w_3 fax11w_4 weq fax11w_3 fax11w_4 weq fax11w_0 wi fax11w_3 wal fax11w_0 fax11w_2 fax11w_4 fax11w_5 eax11w_1 spw fax11w_0 fax11w_1 fax11w_3 fax11w_4 eax11w_0 ax11wlem syl5 $.
$}
$( Degenerate instance of ~ ax-11 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax11dgen_0 $f wff ph $.
	fax11dgen_1 $f set x $.
	ax11dgen $p |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) ) $= fax11dgen_0 fax11dgen_1 wal fax11dgen_1 fax11dgen_1 weq fax11dgen_0 wi fax11dgen_1 wal wi fax11dgen_1 fax11dgen_1 weq fax11dgen_0 fax11dgen_1 fax11dgen_1 weq fax11dgen_0 wi fax11dgen_1 fax11dgen_0 fax11dgen_1 fax11dgen_1 weq ax-1 alimi a1i $.
$}
$( Example of an application of ~ ax11w that results in an instance of
       ~ ax-11 for a contrived formula with mixed free and bound variables,
       ` ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ` , in place of
       ` ph ` .  The proof illustrates bound variable renaming with ~ cbvalvw
       to obtain fresh variables to avoid distinct variable clashes.  Uses only
       Tarski's FOL axiom schemes.  (Contributed by NM, 14-Apr-2017.) $)
$v v $.
${
	$d x y z w v $.
	iax11wdemo_0 $f set w $.
	iax11wdemo_1 $f set v $.
	fax11wdemo_0 $f set x $.
	fax11wdemo_1 $f set y $.
	fax11wdemo_2 $f set z $.
	ax11wdemo $p |- ( x = y -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) ) $= fax11wdemo_0 fax11wdemo_1 wel fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_0 wal fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 wal w3a fax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 iax11wdemo_0 wel iax11wdemo_0 wal iax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 wal iax11wdemo_1 wal w3a fax11wdemo_0 iax11wdemo_1 wel fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_0 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 wal w3a fax11wdemo_0 fax11wdemo_1 iax11wdemo_1 fax11wdemo_0 fax11wdemo_1 weq fax11wdemo_0 fax11wdemo_1 wel fax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_0 wal fax11wdemo_2 iax11wdemo_0 wel iax11wdemo_0 wal fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 wal iax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 wal iax11wdemo_1 wal fax11wdemo_0 fax11wdemo_1 fax11wdemo_1 elequ1 fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_0 wal fax11wdemo_2 iax11wdemo_0 wel iax11wdemo_0 wal wb fax11wdemo_0 fax11wdemo_1 weq fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_2 iax11wdemo_0 wel fax11wdemo_0 iax11wdemo_0 fax11wdemo_0 iax11wdemo_0 fax11wdemo_2 elequ2 cbvalvw a1i fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 wal fax11wdemo_0 fax11wdemo_1 weq iax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 wal iax11wdemo_1 wal fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 iax11wdemo_1 fax11wdemo_1 iax11wdemo_1 weq fax11wdemo_1 fax11wdemo_0 wel iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 fax11wdemo_1 iax11wdemo_1 fax11wdemo_0 elequ1 albidv cbvalvw fax11wdemo_0 fax11wdemo_1 weq iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 wal iax11wdemo_1 fax11wdemo_0 fax11wdemo_1 weq iax11wdemo_1 fax11wdemo_0 wel iax11wdemo_1 fax11wdemo_1 wel fax11wdemo_2 fax11wdemo_0 fax11wdemo_1 iax11wdemo_1 elequ2 albidv albidv syl5bb 3anbi123d fax11wdemo_1 iax11wdemo_1 weq fax11wdemo_0 fax11wdemo_1 wel fax11wdemo_0 iax11wdemo_1 wel fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 wal fax11wdemo_2 fax11wdemo_0 wel fax11wdemo_0 wal fax11wdemo_1 iax11wdemo_1 fax11wdemo_0 elequ2 fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 wal wb fax11wdemo_1 iax11wdemo_1 weq fax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 wal fax11wdemo_1 iax11wdemo_1 fax11wdemo_1 iax11wdemo_1 weq fax11wdemo_1 fax11wdemo_0 wel iax11wdemo_1 fax11wdemo_0 wel fax11wdemo_2 fax11wdemo_1 iax11wdemo_1 fax11wdemo_0 elequ1 albidv cbvalvw a1i 3anbi13d ax11w $.
$}
$( Weak version (principal instance) of ~ ax-12 not involving bundling.
       Uses only Tarski's FOL axiom schemes.  The proof is trivial but is
       included to complete the set ~ ax6w , ~ ax7w , and ~ ax11w .
       (Contributed by NM, 10-Apr-2017.) $)
${
	$d x y z $.
	fax12w_0 $f set x $.
	fax12w_1 $f set y $.
	fax12w_2 $f set z $.
	ax12w $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $= fax12w_0 fax12w_1 weq wn fax12w_1 fax12w_2 weq fax12w_0 a17d $.
$}
$( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax12dgen1_0 $f set x $.
	fax12dgen1_1 $f set z $.
	ax12dgen1 $p |- ( -. x = x -> ( x = z -> A. x x = z ) ) $= fax12dgen1_0 fax12dgen1_0 weq fax12dgen1_0 fax12dgen1_1 weq fax12dgen1_0 fax12dgen1_1 weq fax12dgen1_0 wal wi fax12dgen1_0 equid pm2.24i $.
$}
$( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax12dgen2_0 $f set x $.
	fax12dgen2_1 $f set y $.
	ax12dgen2 $p |- ( -. x = y -> ( y = x -> A. x y = x ) ) $= fax12dgen2_1 fax12dgen2_0 weq fax12dgen2_0 fax12dgen2_1 weq fax12dgen2_0 fax12dgen2_1 weq wn fax12dgen2_1 fax12dgen2_0 weq fax12dgen2_0 wal fax12dgen2_1 fax12dgen2_0 equcomi fax12dgen2_0 fax12dgen2_1 weq fax12dgen2_1 fax12dgen2_0 weq fax12dgen2_0 wal pm2.21 syl5 $.
$}
$( Degenerate instance of ~ ax-12 where bundled variables ` y ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax12dgen3_0 $f set x $.
	fax12dgen3_1 $f set y $.
	ax12dgen3 $p |- ( -. x = y -> ( y = y -> A. x y = y ) ) $= fax12dgen3_0 fax12dgen3_1 weq wn fax12dgen3_1 fax12dgen3_1 weq fax12dgen3_1 fax12dgen3_1 weq fax12dgen3_0 wal fax12dgen3_1 fax12dgen3_1 weq fax12dgen3_0 fax12dgen3_1 equid ax-gen a1ii $.
$}
$( Degenerate instance of ~ ax-12 where bundled variables ` x ` , ` y ` , and
     ` z ` have a common substitution.  Uses only Tarski's FOL axiom schemes .
     (Contributed by NM, 13-Apr-2017.) $)
${
	fax12dgen4_0 $f set x $.
	ax12dgen4 $p |- ( -. x = x -> ( x = x -> A. x x = x ) ) $= fax12dgen4_0 fax12dgen4_0 ax12dgen1 $.
$}

