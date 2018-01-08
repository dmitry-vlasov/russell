
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Tarski_s_system_S2_(1_rule,_6_schemes)/Axiom_schemes_ax-14_(Right_Membership_Equality).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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

  ${
    $( Tarski's system uses the weaker ~ ax9v instead of the bundled ~ ax-9 ,
       so here we show that the degenerate case of ~ ax-9 can be derived.
       (Contributed by NM, 23-Apr-2017.) $)
    ax9dgen $p |- -. A. x -. x = x $=
      vx vx weq wn vx wal vx vx weq vx equid vx vx weq wn vx vx vx weq vx equid
      notnoti spfalw mt2 $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.
    ax6w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-6 from which we can prove any ~ ax-6 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  (Contributed by NM, 9-Apr-2017.) $)
    ax6w $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
      wph wps vx vy ax6w.1 hbn1w $.
  $}

  ${
    $d y z $.  $d x y $.  $d z ph $.  $d y ps $.
    ax7w.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Weak version of ~ ax-7 from which we can prove any ~ ax-7 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  Unlike ~ ax-7 , this theorem requires that ` x ` and ` y ` be
       distinct i.e. are not bundled.  (Contributed by NM, 10-Apr-2017.) $)
    ax7w $p |- ( A. x A. y ph -> A. y A. x ph ) $=
      wph wps vx vy vz ax7w.1 alcomiw $.
  $}

  $( Degenerate instance of ~ ax-7 where bundled variables ` x ` and ` y ` have
     a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax7dgen $p |- ( A. x A. x ph -> A. x A. x ph ) $=
    wph vx wal vx wal id $.

  ${
    $d x ps $.
    ax11wlemw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Lemma for weak version of ~ ax-11 .  Uses only Tarski's FOL axiom
       schemes.  In some cases, this lemma may lead to shorter proofs than
       ~ ax11w .  (Contributed by NM, 10-Apr-2017.) $)
    ax11wlem $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      wph wps vx vy ax11wlemw.1 wps vx ax-17 ax11i $.
  $}

  ${
    $d y z $.  $d x ps $.  $d z ph $.  $d y ch $.
    ax11w.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    ax11w.2 $e |- ( y = z -> ( ph <-> ch ) ) $.
    $( Weak version of ~ ax-11 from which we can prove any ~ ax-11 instance not
       involving wff variables or bundling.  Uses only Tarski's FOL axiom
       schemes.  An instance of the first hypothesis will normally require that
       ` x ` and ` y ` be distinct (unless ` x ` does not occur in ` ph ` ).
       (Contributed by NM, 10-Apr-2017.) $)
    ax11w $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
      wph vy wal wph vx vy weq vx vy weq wph wi vx wal wph wch vy vz ax11w.2
      spw wph wps vx vy ax11w.1 ax11wlem syl5 $.
  $}

  $( Degenerate instance of ~ ax-11 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax11dgen $p |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) ) $=
    wph vx wal vx vx weq wph wi vx wal wi vx vx weq wph vx vx weq wph wi vx wph
    vx vx weq ax-1 alimi a1i $.

  ${
    $d x y z w v $.
    $( Example of an application of ~ ax11w that results in an instance of
       ~ ax-11 for a contrived formula with mixed free and bound variables,
       ` ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ` , in place of
       ` ph ` .  The proof illustrates bound variable renaming with ~ cbvalvw
       to obtain fresh variables to avoid distinct variable clashes.  Uses only
       Tarski's FOL axiom schemes.  (Contributed by NM, 14-Apr-2017.) $)
    ax11wdemo $p |- ( x = y
              -> ( A. y ( x e. y /\ A. x z e. x /\ A. y A. z y e. x )
     -> A. x ( x = y -> ( x e. y /\ A. x z e. x /\ A. y A. z y e. x ) ) ) ) $=
      vx vy wel vz vx wel vx wal vy vx wel vz wal vy wal w3a vy vy wel vz vw
      wel vw wal vv vy wel vz wal vv wal w3a vx vv wel vz vx wel vx wal vv vx
      wel vz wal vv wal w3a vx vy vv vx vy weq vx vy wel vy vy wel vz vx wel vx
      wal vz vw wel vw wal vy vx wel vz wal vy wal vv vy wel vz wal vv wal vx
      vy vy elequ1 vz vx wel vx wal vz vw wel vw wal wb vx vy weq vz vx wel vz
      vw wel vx vw vx vw vz elequ2 cbvalvw a1i vy vx wel vz wal vy wal vv vx
      wel vz wal vv wal vx vy weq vv vy wel vz wal vv wal vy vx wel vz wal vv
      vx wel vz wal vy vv vy vv weq vy vx wel vv vx wel vz vy vv vx elequ1
      albidv cbvalvw vx vy weq vv vx wel vz wal vv vy wel vz wal vv vx vy weq
      vv vx wel vv vy wel vz vx vy vv elequ2 albidv albidv syl5bb 3anbi123d vy
      vv weq vx vy wel vx vv wel vy vx wel vz wal vy wal vv vx wel vz wal vv
      wal vz vx wel vx wal vy vv vx elequ2 vy vx wel vz wal vy wal vv vx wel vz
      wal vv wal wb vy vv weq vy vx wel vz wal vv vx wel vz wal vy vv vy vv weq
      vy vx wel vv vx wel vz vy vv vx elequ1 albidv cbvalvw a1i 3anbi13d ax11w
      $.
  $}

  ${
    $d x y z $.
    $( Weak version (principal instance) of ~ ax-12 not involving bundling.
       Uses only Tarski's FOL axiom schemes.  The proof is trivial but is
       included to complete the set ~ ax6w , ~ ax7w , and ~ ax11w .
       (Contributed by NM, 10-Apr-2017.) $)
    ax12w $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      vx vy weq wn vy vz weq vx a17d $.
  $}

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` y `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen1 $p |- ( -. x = x -> ( x = z -> A. x x = z ) ) $=
    vx vx weq vx vz weq vx vz weq vx wal wi vx equid pm2.24i $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen2 $p |- ( -. x = y -> ( y = x -> A. x y = x ) ) $=
    vy vx weq vx vy weq vx vy weq wn vy vx weq vx wal vy vx equcomi vx vy weq
    vy vx weq vx wal pm2.21 syl5 $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` y ` and ` z `
     have a common substitution.  Uses only Tarski's FOL axiom schemes.
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen3 $p |- ( -. x = y -> ( y = y -> A. x y = y ) ) $=
    vx vy weq wn vy vy weq vy vy weq vx wal vy vy weq vx vy equid ax-gen a1ii
    $.

  $( Degenerate instance of ~ ax-12 where bundled variables ` x ` , ` y ` , and
     ` z ` have a common substitution.  Uses only Tarski's FOL axiom schemes .
     (Contributed by NM, 13-Apr-2017.) $)
  ax12dgen4 $p |- ( -. x = x -> ( x = x -> A. x x = x ) ) $=
    vx vx ax12dgen1 $.



