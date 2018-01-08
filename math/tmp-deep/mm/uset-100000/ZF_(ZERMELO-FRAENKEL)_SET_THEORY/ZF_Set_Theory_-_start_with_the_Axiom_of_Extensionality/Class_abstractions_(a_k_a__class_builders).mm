
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Introduce_the_Axiom_of_Extensionality.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Class abstractions (a.k.a. class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new constants use in class definition. $)
  $c { $. $( Left brace $)
  $c | $.  $( Vertical bar $)
  $c } $. $( Right brace $)
  $( --- Start of old code before overloading prevention patch. $)
  $(
  @c class @. @( Class variable type @)
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Declare symbols as variables $)
  $v ./\ $.
  $v .\/ $.
  $v .<_ $.
  $v .< $.
  $v .+ $.
  $v .- $.
  $v .X. $.
  $v ./ $.
  $v .^ $.
  $v .0. $.
  $v .1. $.
  $v .|| $.
  $v .~ $.
  $v ._|_ $.
  $v .+^ $.
  $v .+b $.
  $v .(+) $.
  $v .* $.
  $v .x. $.
  $v .xb $.
  $v ., $.
  $v .(x) $.
  $v .0b $.

  $( Declare variable symbols that will be used to represent classes.  Note
     that later on ` R ` , ` S ` , ` F ` and ` G ` denote relations and
     functions, but these letters serve as mnemonics only and in fact behave
     no differently from the variables ` A ` through ` D ` . $)
  $v A $.
  $v B $.
  $v C $.
  $v D $.
  $v P $.
  $v Q $.
  $v R $.
  $v S $.
  $v T $.
  $v U $.

  $( Introduce the class builder or class abstraction notation ("the class of
     sets ` x ` such that ` ph ` is true").  Our class variables ` A ` ,
     ` B ` , etc. range over class builders (implicitly in the case of defined
     class terms such as ~ df-nul ).  Note that a set variable can be expressed
     as a class builder per theorem ~ cvjust , justifying the assignment of set
     variables to class variables via the use of ~ cv . $)
  cab $a class { x | ph } $.

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( A set variable is a class expression.  The syntax " ` class x ` " can be
     viewed as an abbreviation for " ` class { y | y e. x } ` " (a special case
     of ~ cab ), where ` y ` is distinct from ` x ` .  See the discussion under
     the definition of class in [Jech] p. 4.  Note that ` { y | y e. x } = x `
     by ~ cvjust . @)
  cv @a class x @.
  $)
  $( --- End of old code before overloading prevention patch. $)
  $( $j primitive 'cv' 'wceq' 'wcel' 'cab'; $)

  $( Let ` A ` be a class variable. $)
  cA $f class A $.
  $( Let ` B ` be a class variable. $)
  cB $f class B $.
  $( Let ` C ` be a class variable. $)
  cC $f class C $.

  $( Define a connective symbol for use as a class variable. $)
  c.pa $f class .|| $.

  $( Let ` D ` be a class variable. $)
  cD $f class D $.

  $( Define a connective symbol for use as a class variable. $)
  c.dv $f class ./ $.

  $( Let ` P ` be a class variable. $)
  cP $f class P $.

  $( Define a connective symbol for use as a class variable. $)
  c.pl $f class .+ $.

  $( Define a connective symbol for use as a class variable. $)
  c.pd $f class .+^ $.

  $( Define a connective symbol for use as a class variable. $)
  c.pb $f class .+b $.

  $( Define a connective symbol for use as a class variable. $)
  c.po $f class .(+) $.

  $( Let ` Q ` be a class variable. $)
  cQ $f class Q $.

  $( Define a connective symbol for use as a class variable. $)
  c.sm $f class .~ $.

  $( Let ` R ` be a class variable. $)
  cR $f class R $.
  $( Let ` S ` be a class variable. $)
  cS $f class S $.

  $( Define a connective symbol for use as a class variable. $)
  c.lt $f class .< $.

  $( Define a connective symbol for use as a class variable. $)
  c.xb $f class .xb $.

  $( Let ` T ` be a class variable. $)
  cT $f class T $.

  $( Define a connective symbol for use as a class variable. $)
  c.x $f class .x. $.

  $( Define a connective symbol for use as a class variable. $)
  c.xp $f class .X. $.

  $( Define a connective symbol for use as a class variable. $)
  c.xo $f class .(x) $.

  $( Let ` U ` be a class variable. $)
  cU $f class U $.

  $( Define a connective symbol for use as a class variable. $)
  c.1 $f class .1. $.

  $v e $.
  $v f $.
  $v g $.
  $v h $.
  $v i $.
  $v j $.
  $v k $.
  $v m $.
  $v n $.
  $v o $.
  $v E $.
  $v F $.
  $v G $.
  $v H $.
  $v I $.
  $v J $.
  $v K $.
  $v L $.
  $v M $.
  $v N $.
  $v V $.
  $v W $.
  $v X $.
  $v Y $.
  $v Z $.
  $v O $.
  $v s $.
  $v r $.
  $v q $.
  $v p $.
  $v a $.
  $v b $.
  $v c $.
  $v d $.
  $v l $.


  $( Let ` e ` be an individual variable. $)
  ve $f set e $.
  $( Let ` f ` be an individual variable. $)
  vf $f set f $.
  $( Let ` g ` be an individual variable. $)
  vg $f set g $.
  $( Let ` h ` be an individual variable. $)
  vh $f set h $.
  $( Let ` i ` be an individual variable. $)
  vi $f set i $.
  $( Let ` j ` be an individual variable. $)
  vj $f set j $.
  $( Let ` k ` be an individual variable. $)
  vk $f set k $.
  $( Let ` m ` be an individual variable. $)
  vm $f set m $.
  $( Let ` n ` be an individual variable. $)
  vn $f set n $.
  $( Let ` o ` be an individual variable. $)
  vo $f set o $.
  $( Let ` E ` be a class variable. $)
  cE $f class E $.

  $( Define a connective symbol for use as a class variable. $)
  c.ex $f class .^ $.

  $( Let ` F ` be a class variable. $)
  cF $f class F $.
  $( Let ` G ` be a class variable. $)
  cG $f class G $.
  $( Let ` H ` be a class variable. $)
  cH $f class H $.

  $( Define a connective symbol for use as a class variable. $)
  c.xi $f class ., $.

  $( Let ` I ` be a class variable. $)
  cI $f class I $.

  $( Define a connective symbol for use as a class variable. $)
  c.as $f class .* $.

  $( Let ` J ` be a class variable. $)
  cJ $f class J $.

  $( Define a connective symbol for use as a class variable. $)
  c.or $f class .\/ $.

  $( Let ` K ` be a class variable. $)
  cK $f class K $.
  $( Let ` L ` be a class variable. $)
  cL $f class L $.

  $( Define a connective symbol for use as a class variable. $)
  c.le $f class .<_ $.

  $( Let ` M ` be a class variable. $)
  cM $f class M $.

  $( Define a connective symbol for use as a class variable. $)
  c.an $f class ./\ $.

  $( Define a connective symbol for use as a class variable. $)
  c.mi $f class .- $.

  $( Let ` N ` be a class variable. $)
  cN $f class N $.

  $( Define a connective symbol for use as a class variable. $)
  c.pe $f class ._|_ $.

  $( Let ` O ` be a class variable. $)
  cO $f class O $.
  $( Let ` V ` be a class variable. $)
  cV $f class V $.
  $( Let ` W ` be a class variable. $)
  cW $f class W $.
  $( Let ` X ` be a class variable. $)
  cX $f class X $.
  $( Let ` Y ` be a class variable. $)
  cY $f class Y $.

  $( Define a connective symbol for use as a class variable. $)
  c.0 $f class .0. $.

  $( Define a connective symbol for use as a class variable. $)
  c.0b $f class .0b $.

  $( Let ` Z ` be a class variable. $)
  cZ $f class Z $.
  $( Let ` s ` be an individual variable. $)
  vs $f set s $.
  $( Let ` r ` be an individual variable. $)
  vr $f set r $.
  $( Let ` q ` be an individual variable. $)
  vq $f set q $.
  $( Let ` p ` be an individual variable. $)
  vp $f set p $.
  $( Let ` a ` be an individual variable. $)
  va $f set a $.
  $( Let ` b ` be an individual variable. $)
  vb $f set b $.
  $( Let ` c ` be an individual variable. $)
  vc $f set c $.
  $( Let ` d ` be an individual variable. $)
  vd $f set d $.
  $( Let ` l ` be an individual variable. $)
  vl $f set l $.

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include class equality. @)
  wceq @a wff A = B @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff definition to include the membership connective between
     classes. @)
  wcel @a wff A e. B @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( Define class abstraction notation (so-called by Quine), also called a
     "class builder" in the literature. ` x ` and ` y ` need not be distinct.
     Definition 2.1 of [Quine] p. 16.  Typically, ` ph ` will have ` y ` as a
     free variable, and " ` { y | ph } ` " is read "the class of all sets ` y `
     such that ` ph ( y ) ` is true."  We do not define ` { y | ph } ` in
     isolation but only as part of an expression that extends or "overloads"
     the ` e. ` relationship.

     This is our first use of the ` e. ` symbol to connect classes instead of
     sets.  The syntax definition ~ wcel , which extends or "overloads" the
     ~ wel definition connecting set variables, requires that both sides of
     ` e. ` be a class.  In ~ df-cleq and ~ df-clel , we introduce a new kind
     of variable (class variable) that can substituted with expressions such as
     ` { y | ph } ` .  In the present definition, the ` x ` on the left-hand
     side is a set variable.  Syntax definition ~ cv allows us to substitute a
     set variable ` x ` for a class variable: all sets are classes by ~ cvjust
     (but not necessarily vice-versa).  For a full description of how classes
     are introduced and how to recover the primitive language, see the
     discussion in Quine (and under ~ abeq2 for a quick overview).

     Because class variables can be substituted with compound expressions and
     set variables cannot, it is often useful to convert a theorem containing a
     free set variable to a more general version with a class variable.  This
     is done with theorems such as ~ vtoclg which is used, for example, to
     convert ~ elirrv to ~ elirr .

     This is called the "axiom of class comprehension" by [Levy] p. 338, who
     treats the theory of classes as an extralogical extension to our logic and
     set theory axioms.  He calls the construction ` { y | ph } ` a "class
     term".

     For a general discussion of the theory of classes, see
     ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
     5-Aug-1993.) $)
  df-clab $a |- ( x e. { y | ph } <-> [ x / y ] ph ) $.

  $( Simplification of class abstraction notation when the free and bound
     variables are identical.  (Contributed by NM, 5-Aug-1993.) $)
  abid $p |- ( x e. { x | ph } <-> ph ) $=
    vx cv wph vx cab wcel wph vx vx wsb wph wph vx vx df-clab wph vx sbid bitri
    $.

  ${
    $d x y $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 5-Aug-1993.) $)
    hbab1 $p |- ( y e. { x | ph } -> A. x y e. { x | ph } ) $=
      vy cv wph vx cab wcel wph vx vy wsb vx wph vy vx df-clab wph vx vy hbs1
      hbxfrbi $.

    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
    nfsab1 $p |- F/ x y e. { x | ph } $=
      vy cv wph vx cab wcel vx wph vx vy hbab1 nfi $.
  $}

  ${
    $d x z $.
    hbab.1 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by NM, 1-Mar-1995.) $)
    hbab $p |- ( z e. { y | ph } -> A. x z e. { y | ph } ) $=
      vz cv wph vy cab wcel wph vy vz wsb vx wph vz vy df-clab wph vy vz vx
      hbab.1 hbsb hbxfrbi $.
  $}

  ${
    $d x z $.
    nfsab.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
    nfsab $p |- F/ x z e. { y | ph } $=
      vz cv wph vy cab wcel vx wph vx vy vz wph vx nfsab.1 nfri hbab nfi $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y z $.
    df-cleq.1 $e |- ( A. x ( x e. y <-> x e. z ) -> y = z ) $.
    $( Define the equality connective between classes.  Definition 2.7 of
       [Quine] p. 18.  Also Definition 4.5 of [TakeutiZaring] p. 13; Chapter 4
       provides its justification and methods for eliminating it.  Note that
       its elimination will not necessarily result in a single wff in the
       original language but possibly a "scheme" of wffs.

       This is an example of a somewhat "risky" definition, meaning that it has
       a more complex than usual soundness justification (outside of Metamath),
       because it "overloads" or reuses the existing equality symbol rather
       than introducing a new symbol.  This allows us to make statements that
       may not hold for the original symbol.  For example, it permits us to
       deduce ` y = z <-> A. x ( x e. y <-> x e. z ) ` , which is not a theorem
       of logic but rather presupposes the Axiom of Extensionality (see theorem
       ~ axext4 ).  We therefore include this axiom as a hypothesis, so that
       the use of Extensionality is properly indicated.

       We could avoid this complication by introducing a new symbol, say =_2,
       in place of ` = ` .  This would also have the advantage of making
       elimination of the definition straightforward, so that we could
       eliminate Extensionality as a hypothesis.  We would then also have the
       advantage of being able to identify in various proofs exactly where
       Extensionality truly comes into play rather than just being an artifact
       of a definition.  One of our theorems would then be ` x ` =_2
       ` y <-> x = y ` by invoking Extensionality.

       However, to conform to literature usage, we retain this overloaded
       definition.  This also makes some proofs shorter and probably easier to
       read, without the constant switching between two kinds of equality.

       See also comments under ~ df-clab , ~ df-clel , and ~ abeq2 .

       In the form of ~ dfcleq , this is called the "axiom of extensionality"
       by [Levy] p. 338, who treats the theory of classes as an extralogical
       extension to our logic and set theory axioms.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
       15-Sep-1993.) $)
    df-cleq $a |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y z $.
    $( The same as ~ df-cleq with the hypothesis removed using the Axiom of
       Extensionality ~ ax-ext .  (Contributed by NM, 15-Sep-1993.) $)
    dfcleq $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      vx vy vz cA cB vy vz vx ax-ext df-cleq $.
  $}

  ${
    $d x y z $.
    $( Every set is a class.  Proposition 4.9 of [TakeutiZaring] p. 13.  This
       theorem shows that a set variable can be expressed as a class
       abstraction.  This provides a motivation for the class syntax
       construction ~ cv , which allows us to substitute a set variable for a
       class variable.  See also ~ cab and ~ df-clab .  Note that this is not a
       rigorous justification, because ~ cv is used as part of the proof of
       this theorem, but a careful argument can be made outside of the
       formalism of Metamath, for example as is done in Chapter 4 of Takeuti
       and Zaring.  See also the discussion under the definition of class in
       [Jech] p. 4 showing that "Every set can be considered to be a class."
       (Contributed by NM, 7-Nov-2006.) $)
    cvjust $p |- x = { y | y e. x } $=
      vx cv vy cv vx cv wcel vy cab wceq vz cv vx cv wcel vz cv vy cv vx cv
      wcel vy cab wcel wb vz vz vx cv vy cv vx cv wcel vy cab dfcleq vz cv vy
      cv vx cv wcel vy cab wcel vy cv vx cv wcel vy vz wsb vz cv vx cv wcel vy
      cv vx cv wcel vz vy df-clab vz vy vx elsb3 bitr2i mpgbir $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Define the membership connective between classes.  Theorem 6.3 of
       [Quine] p. 41, or Proposition 4.6 of [TakeutiZaring] p. 13, which we
       adopt as a definition.  See these references for its metalogical
       justification.  Note that like ~ df-cleq it extends or "overloads" the
       use of the existing membership symbol, but unlike ~ df-cleq it does not
       strengthen the set of valid wffs of logic when the class variables are
       replaced with set variables (see ~ cleljust ), so we don't include any
       set theory axiom as a hypothesis.  See also comments about the syntax
       under ~ df-clab .  Alternate definitions of ` A e. B ` (but that require
       either ` A ` or ` B ` to be a set) are shown by ~ clel2 , ~ clel3 , and
       ~ clel4 .

       This is called the "axiom of membership" by [Levy] p. 338, who treats
       the theory of classes as an extralogical extension to our logic and set
       theory axioms.

       For a general discussion of the theory of classes, see
       ~ http://us.metamath.org/mpeuni/mmset.html#class .  (Contributed by NM,
       5-Aug-1993.) $)
    df-clel $a |- ( A e. B <-> E. x ( x = A /\ x e. B ) ) $.
  $}

  ${
    $d x A $.  $d x B $.
    eqriv.1 $e |- ( x e. A <-> x e. B ) $.
    $( Infer equality of classes from equivalence of membership.  (Contributed
       by NM, 5-Aug-1993.) $)
    eqriv $p |- A = B $=
      cA cB wceq vx cv cA wcel vx cv cB wcel wb vx vx cA cB dfcleq eqriv.1
      mpgbir $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    eqrdv.1 $e |- ( ph -> ( x e. A <-> x e. B ) ) $.
    $( Deduce equality of classes from equivalence of membership.  (Contributed
       by NM, 17-Mar-1996.) $)
    eqrdv $p |- ( ph -> A = B ) $=
      wph vx cv cA wcel vx cv cB wcel wb vx wal cA cB wceq wph vx cv cA wcel vx
      cv cB wcel wb vx eqrdv.1 alrimiv vx cA cB dfcleq sylibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    eqrdav.1 $e |- ( ( ph /\ x e. A ) -> x e. C ) $.
    eqrdav.2 $e |- ( ( ph /\ x e. B ) -> x e. C ) $.
    eqrdav.3 $e |- ( ( ph /\ x e. C ) -> ( x e. A <-> x e. B ) ) $.
    $( Deduce equality of classes from an equivalence of membership that
       depends on the membership variable.  (Contributed by NM, 7-Nov-2008.) $)
    eqrdav $p |- ( ph -> A = B ) $=
      wph vx cA cB wph vx cv cA wcel vx cv cB wcel wph vx cv cA wcel wa vx cv
      cC wcel vx cv cB wcel eqrdav.1 wph vx cv cC wcel vx cv cA wcel vx cv cB
      wcel wph vx cv cC wcel wa vx cv cA wcel vx cv cB wcel eqrdav.3 biimpd
      impancom mpd wph vx cv cB wcel wa vx cv cC wcel vx cv cA wcel eqrdav.2
      wph vx cv cB wcel vx cv cC wcel vx cv cA wcel wi wph vx cv cC wcel vx cv
      cB wcel vx cv cA wcel wph vx cv cC wcel vx cv cA wcel vx cv cB wcel
      eqrdav.3 exbiri com23 imp mpd impbida eqrdv $.
  $}

  ${
    $d x A $.
    $( Law of identity (reflexivity of class equality).  Theorem 6.4 of [Quine]
       p. 41.

       This law is thought to have originated with Aristotle (_Metaphysics_,
       Zeta, 17, 1041 a, 10-20:  "Therefore, inquiring why a thing is itself,
       it's inquiring nothing; ... saying that the thing is itself constitutes
       the sole reasoning and the sole cause, in every case, to the question of
       why the man is man or the musician musician.").  (Thanks to Stefan Allan
       and Beno&icirc;t Jubin for this information.)  (Contributed by NM,
       5-Aug-1993.)  (Revised by Beno&icirc;t Jubin, 14-Oct-2017.) $)
    eqid $p |- A = A $=
      vx cA cA vx cv cA wcel biid eqriv $.
  $}

  $( Class identity law with antecedent.  (Contributed by NM, 21-Aug-2008.) $)
  eqidd $p |- ( ph -> A = A ) $=
    cA cA wceq wph cA eqid a1i $.

  ${
    $d x A $.  $d x B $.
    $( Commutative law for class equality.  Theorem 6.5 of [Quine] p. 41.
       (Contributed by NM, 5-Aug-1993.) $)
    eqcom $p |- ( A = B <-> B = A ) $=
      vx cv cA wcel vx cv cB wcel wb vx wal vx cv cB wcel vx cv cA wcel wb vx
      wal cA cB wceq cB cA wceq vx cv cA wcel vx cv cB wcel wb vx cv cB wcel vx
      cv cA wcel wb vx vx cv cA wcel vx cv cB wcel bicom albii vx cA cB dfcleq
      vx cB cA dfcleq 3bitr4i $.
  $}

  ${
    eqcoms.1 $e |- ( A = B -> ph ) $.
    $( Inference applying commutative law for class equality to an antecedent.
       (Contributed by NM, 5-Aug-1993.) $)
    eqcoms $p |- ( B = A -> ph ) $=
      cB cA wceq cA cB wceq wph cB cA eqcom eqcoms.1 sylbi $.
  $}

  ${
    eqcomi.1 $e |- A = B $.
    $( Inference from commutative law for class equality.  (Contributed by NM,
       5-Aug-1993.) $)
    eqcomi $p |- B = A $=
      cA cB wceq cB cA wceq eqcomi.1 cA cB eqcom mpbi $.
  $}

  ${
    eqcomd.1 $e |- ( ph -> A = B ) $.
    $( Deduction from commutative law for class equality.  (Contributed by NM,
       15-Aug-1994.) $)
    eqcomd $p |- ( ph -> B = A ) $=
      wph cA cB wceq cB cA wceq eqcomd.1 cA cB eqcom sylib $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality implies equivalence of equalities.  (Contributed by NM,
       5-Aug-1993.) $)
    eqeq1 $p |- ( A = B -> ( A = C <-> B = C ) ) $=
      cA cB wceq vx cv cA wcel vx cv cC wcel wb vx wal vx cv cB wcel vx cv cC
      wcel wb vx wal cA cC wceq cB cC wceq cA cB wceq vx cv cA wcel vx cv cC
      wcel wb vx cv cB wcel vx cv cC wcel wb vx cA cB wceq vx cv cA wcel vx cv
      cB wcel vx cv cC wcel cA cB wceq vx cv cA wcel vx cv cB wcel wb vx cA cB
      wceq vx cv cA wcel vx cv cB wcel wb vx wal vx cA cB dfcleq biimpi 19.21bi
      bibi1d albidv vx cA cC dfcleq vx cB cC dfcleq 3bitr4g $.
  $}

  ${
    eqeq1i.1 $e |- A = B $.
    $( Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqeq1i $p |- ( A = C <-> B = C ) $=
      cA cB wceq cA cC wceq cB cC wceq wb eqeq1i.1 cA cB cC eqeq1 ax-mp $.
  $}

  ${
    eqeq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) $)
    eqeq1d $p |- ( ph -> ( A = C <-> B = C ) ) $=
      wph cA cB wceq cA cC wceq cB cC wceq wb eqeq1d.1 cA cB cC eqeq1 syl $.
  $}

  $( Equality implies equivalence of equalities.  (Contributed by NM,
     5-Aug-1993.) $)
  eqeq2 $p |- ( A = B -> ( C = A <-> C = B ) ) $=
    cA cB wceq cA cC wceq cB cC wceq cC cA wceq cC cB wceq cA cB cC eqeq1 cC cA
    eqcom cC cB eqcom 3bitr4g $.

  ${
    eqeq2i.1 $e |- A = B $.
    $( Inference from equality to equivalence of equalities.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqeq2i $p |- ( C = A <-> C = B ) $=
      cA cB wceq cC cA wceq cC cB wceq wb eqeq2i.1 cA cB cC eqeq2 ax-mp $.
  $}

  ${
    eqeq2d.1 $e |- ( ph -> A = B ) $.
    $( Deduction from equality to equivalence of equalities.  (Contributed by
       NM, 27-Dec-1993.) $)
    eqeq2d $p |- ( ph -> ( C = A <-> C = B ) ) $=
      wph cA cB wceq cC cA wceq cC cB wceq wb eqeq2d.1 cA cB cC eqeq2 syl $.
  $}

  $( Equality relationship among 4 classes.  (Contributed by NM,
     3-Aug-1994.) $)
  eqeq12 $p |- ( ( A = B /\ C = D ) -> ( A = C <-> B = D ) ) $=
    cA cB wceq cA cC wceq cB cC wceq cC cD wceq cB cD wceq cA cB cC eqeq1 cC cD
    cB eqeq2 sylan9bb $.

  ${
    eqeq12i.1 $e |- A = B $.
    eqeq12i.2 $e |- C = D $.
    $( A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    eqeq12i $p |- ( A = C <-> B = D ) $=
      cA cB wceq cC cD wceq cA cC wceq cB cD wceq wb eqeq12i.1 eqeq12i.2 cA cB
      cC cD eqeq12 mp2an $.

    $( Theorem eqeq12i is the congruence law for equality. $)
    $( $j congruence 'eqeq12i'; $)
  $}

  ${
    eqeq12d.1 $e |- ( ph -> A = B ) $.
    eqeq12d.2 $e |- ( ph -> C = D ) $.
    $( A useful inference for substituting definitions into an equality.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    eqeq12d $p |- ( ph -> ( A = C <-> B = D ) ) $=
      wph cA cB wceq cC cD wceq cA cC wceq cB cD wceq wb eqeq12d.1 eqeq12d.2 cA
      cB cC cD eqeq12 syl2anc $.
  $}

  ${
    eqeqan12d.1 $e |- ( ph -> A = B ) $.
    eqeqan12d.2 $e |- ( ps -> C = D ) $.
    $( A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    eqeqan12d $p |- ( ( ph /\ ps ) -> ( A = C <-> B = D ) ) $=
      wph cA cB wceq cC cD wceq cA cC wceq cB cD wceq wb wps eqeqan12d.1
      eqeqan12d.2 cA cB cC cD eqeq12 syl2an $.
  $}

  ${
    eqeqan12rd.1 $e |- ( ph -> A = B ) $.
    eqeqan12rd.2 $e |- ( ps -> C = D ) $.
    $( A useful inference for substituting definitions into an equality.
       (Contributed by NM, 9-Aug-1994.) $)
    eqeqan12rd $p |- ( ( ps /\ ph ) -> ( A = C <-> B = D ) ) $=
      wph wps cA cC wceq cB cD wceq wb wph wps cA cB cC cD eqeqan12rd.1
      eqeqan12rd.2 eqeqan12d ancoms $.
  $}

  $( Transitive law for class equality.  Proposition 4.7(3) of [TakeutiZaring]
     p. 13.  (Contributed by NM, 25-Jan-2004.) $)
  eqtr $p |- ( ( A = B /\ B = C ) -> A = C ) $=
    cA cB wceq cA cC wceq cB cC wceq cA cB cC eqeq1 biimpar $.

  $( A transitive law for class equality.  (Contributed by NM, 20-May-2005.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  eqtr2 $p |- ( ( A = B /\ A = C ) -> B = C ) $=
    cA cB wceq cB cA wceq cA cC wceq cB cC wceq cA cB eqcom cB cA cC eqtr
    sylanb $.

  $( A transitive law for class equality.  (Contributed by NM, 20-May-2005.) $)
  eqtr3 $p |- ( ( A = C /\ B = C ) -> A = B ) $=
    cB cC wceq cA cC wceq cC cB wceq cA cB wceq cB cC eqcom cA cC cB eqtr
    sylan2b $.

  ${
    eqtri.1 $e |- A = B $.
    eqtri.2 $e |- B = C $.
    $( An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) $)
    eqtri $p |- A = C $=
      cA cB wceq cA cC wceq eqtri.1 cB cC cA eqtri.2 eqeq2i mpbi $.
  $}

  ${
    eqtr2i.1 $e |- A = B $.
    eqtr2i.2 $e |- B = C $.
    $( An equality transitivity inference.  (Contributed by NM,
       21-Feb-1995.) $)
    eqtr2i $p |- C = A $=
      cA cC cA cB cC eqtr2i.1 eqtr2i.2 eqtri eqcomi $.
  $}

  ${
    eqtr3i.1 $e |- A = B $.
    eqtr3i.2 $e |- A = C $.
    $( An equality transitivity inference.  (Contributed by NM, 6-May-1994.) $)
    eqtr3i $p |- B = C $=
      cB cA cC cA cB eqtr3i.1 eqcomi eqtr3i.2 eqtri $.
  $}

  ${
    eqtr4i.1 $e |- A = B $.
    eqtr4i.2 $e |- C = B $.
    $( An equality transitivity inference.  (Contributed by NM, 5-Aug-1993.) $)
    eqtr4i $p |- A = C $=
      cA cB cC eqtr4i.1 cC cB eqtr4i.2 eqcomi eqtri $.
  $}

  $( Register '=' as an equality for its type (class). $)
  $( $j equality 'wceq' from 'eqid' 'eqcomi' 'eqtri'; $)

  ${
    3eqtri.1 $e |- A = B $.
    3eqtri.2 $e |- B = C $.
    3eqtri.3 $e |- C = D $.
    $( An inference from three chained equalities.  (Contributed by NM,
       29-Aug-1993.) $)
    3eqtri $p |- A = D $=
      cA cB cD 3eqtri.1 cB cC cD 3eqtri.2 3eqtri.3 eqtri eqtri $.

    $( An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtrri $p |- D = A $=
      cA cC cD cA cB cC 3eqtri.1 3eqtri.2 eqtri 3eqtri.3 eqtr2i $.
  $}

  ${
    3eqtr2i.1 $e |- A = B $.
    3eqtr2i.2 $e |- C = B $.
    3eqtr2i.3 $e |- C = D $.
    $( An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.) $)
    3eqtr2i $p |- A = D $=
      cA cC cD cA cB cC 3eqtr2i.1 3eqtr2i.2 eqtr4i 3eqtr2i.3 eqtri $.

    $( An inference from three chained equalities.  (Contributed by NM,
       3-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr2ri $p |- D = A $=
      cA cC cD cA cB cC 3eqtr2i.1 3eqtr2i.2 eqtr4i 3eqtr2i.3 eqtr2i $.
  $}

  ${
    3eqtr3i.1 $e |- A = B $.
    3eqtr3i.2 $e |- A = C $.
    3eqtr3i.3 $e |- B = D $.
    $( An inference from three chained equalities.  (Contributed by NM,
       6-May-1994.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr3i $p |- C = D $=
      cB cC cD cA cB cC 3eqtr3i.1 3eqtr3i.2 eqtr3i 3eqtr3i.3 eqtr3i $.

    $( An inference from three chained equalities.  (Contributed by NM,
       15-Aug-2004.) $)
    3eqtr3ri $p |- D = C $=
      cB cD cC 3eqtr3i.3 cA cB cC 3eqtr3i.1 3eqtr3i.2 eqtr3i eqtr3i $.
  $}

  ${
    3eqtr4i.1 $e |- A = B $.
    3eqtr4i.2 $e |- C = A $.
    3eqtr4i.3 $e |- D = B $.
    $( An inference from three chained equalities.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr4i $p |- C = D $=
      cC cA cD 3eqtr4i.2 cD cB cA 3eqtr4i.3 3eqtr4i.1 eqtr4i eqtr4i $.

    $( An inference from three chained equalities.  (Contributed by NM,
       2-Sep-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr4ri $p |- D = C $=
      cD cA cC cD cB cA 3eqtr4i.3 3eqtr4i.1 eqtr4i 3eqtr4i.2 eqtr4i $.
  $}

  ${
    eqtrd.1 $e |- ( ph -> A = B ) $.
    eqtrd.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)
    eqtrd $p |- ( ph -> A = C ) $=
      wph cA cB wceq cA cC wceq eqtrd.1 wph cB cC cA eqtrd.2 eqeq2d mpbid $.
  $}

  ${
    eqtr2d.1 $e |- ( ph -> A = B ) $.
    eqtr2d.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM,
       18-Oct-1999.) $)
    eqtr2d $p |- ( ph -> C = A ) $=
      wph cA cC wph cA cB cC eqtr2d.1 eqtr2d.2 eqtrd eqcomd $.
  $}

  ${
    eqtr3d.1 $e |- ( ph -> A = B ) $.
    eqtr3d.2 $e |- ( ph -> A = C ) $.
    $( An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)
    eqtr3d $p |- ( ph -> B = C ) $=
      wph cB cA cC wph cA cB eqtr3d.1 eqcomd eqtr3d.2 eqtrd $.
  $}

  ${
    eqtr4d.1 $e |- ( ph -> A = B ) $.
    eqtr4d.2 $e |- ( ph -> C = B ) $.
    $( An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)
    eqtr4d $p |- ( ph -> A = C ) $=
      wph cA cB cC eqtr4d.1 wph cC cB eqtr4d.2 eqcomd eqtrd $.
  $}

  ${
    3eqtrd.1 $e |- ( ph -> A = B ) $.
    3eqtrd.2 $e |- ( ph -> B = C ) $.
    3eqtrd.3 $e |- ( ph -> C = D ) $.
    $( A deduction from three chained equalities.  (Contributed by NM,
       29-Oct-1995.) $)
    3eqtrd $p |- ( ph -> A = D ) $=
      wph cA cB cD 3eqtrd.1 wph cB cC cD 3eqtrd.2 3eqtrd.3 eqtrd eqtrd $.

    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtrrd $p |- ( ph -> D = A ) $=
      wph cA cC cD wph cA cB cC 3eqtrd.1 3eqtrd.2 eqtrd 3eqtrd.3 eqtr2d $.
  $}

  ${
    3eqtr2d.1 $e |- ( ph -> A = B ) $.
    3eqtr2d.2 $e |- ( ph -> C = B ) $.
    3eqtr2d.3 $e |- ( ph -> C = D ) $.
    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) $)
    3eqtr2d $p |- ( ph -> A = D ) $=
      wph cA cC cD wph cA cB cC 3eqtr2d.1 3eqtr2d.2 eqtr4d 3eqtr2d.3 eqtrd $.

    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-2006.) $)
    3eqtr2rd $p |- ( ph -> D = A ) $=
      wph cA cC cD wph cA cB cC 3eqtr2d.1 3eqtr2d.2 eqtr4d 3eqtr2d.3 eqtr2d $.
  $}

  ${
    3eqtr3d.1 $e |- ( ph -> A = B ) $.
    3eqtr3d.2 $e |- ( ph -> A = C ) $.
    3eqtr3d.3 $e |- ( ph -> B = D ) $.
    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr3d $p |- ( ph -> C = D ) $=
      wph cB cC cD wph cA cB cC 3eqtr3d.1 3eqtr3d.2 eqtr3d 3eqtr3d.3 eqtr3d $.

    $( A deduction from three chained equalities.  (Contributed by NM,
       14-Jan-2006.) $)
    3eqtr3rd $p |- ( ph -> D = C ) $=
      wph cB cD cC 3eqtr3d.3 wph cA cB cC 3eqtr3d.1 3eqtr3d.2 eqtr3d eqtr3d $.
  $}

  ${
    3eqtr4d.1 $e |- ( ph -> A = B ) $.
    3eqtr4d.2 $e |- ( ph -> C = A ) $.
    3eqtr4d.3 $e |- ( ph -> D = B ) $.
    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr4d $p |- ( ph -> C = D ) $=
      wph cC cA cD 3eqtr4d.2 wph cD cB cA 3eqtr4d.3 3eqtr4d.1 eqtr4d eqtr4d $.

    $( A deduction from three chained equalities.  (Contributed by NM,
       21-Sep-1995.) $)
    3eqtr4rd $p |- ( ph -> D = C ) $=
      wph cD cA cC wph cD cB cA 3eqtr4d.3 3eqtr4d.1 eqtr4d 3eqtr4d.2 eqtr4d $.
  $}

  ${
    syl5eq.1 $e |- A = B $.
    syl5eq.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)
    syl5eq $p |- ( ph -> A = C ) $=
      wph cA cB cC cA cB wceq wph syl5eq.1 a1i syl5eq.2 eqtrd $.
  $}

  ${
    syl5req.1 $e |- A = B $.
    syl5req.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)
    syl5req $p |- ( ph -> C = A ) $=
      wph cA cC wph cA cB cC syl5req.1 syl5req.2 syl5eq eqcomd $.
  $}

  ${
    syl5eqr.1 $e |- B = A $.
    syl5eqr.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)
    syl5eqr $p |- ( ph -> A = C ) $=
      wph cA cB cC cB cA syl5eqr.1 eqcomi syl5eqr.2 syl5eq $.
  $}

  ${
    syl5reqr.1 $e |- B = A $.
    syl5reqr.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)
    syl5reqr $p |- ( ph -> C = A ) $=
      wph cA cB cC cB cA syl5reqr.1 eqcomi syl5reqr.2 syl5req $.
  $}

  ${
    syl6eq.1 $e |- ( ph -> A = B ) $.
    syl6eq.2 $e |- B = C $.
    $( An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)
    syl6eq $p |- ( ph -> A = C ) $=
      wph cA cB cC syl6eq.1 cB cC wceq wph syl6eq.2 a1i eqtrd $.
  $}

  ${
    syl6req.1 $e |- ( ph -> A = B ) $.
    syl6req.2 $e |- B = C $.
    $( An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)
    syl6req $p |- ( ph -> C = A ) $=
      wph cA cC wph cA cB cC syl6req.1 syl6req.2 syl6eq eqcomd $.
  $}

  ${
    syl6eqr.1 $e |- ( ph -> A = B ) $.
    syl6eqr.2 $e |- C = B $.
    $( An equality transitivity deduction.  (Contributed by NM, 5-Aug-1993.) $)
    syl6eqr $p |- ( ph -> A = C ) $=
      wph cA cB cC syl6eqr.1 cC cB syl6eqr.2 eqcomi syl6eq $.
  $}

  ${
    syl6reqr.1 $e |- ( ph -> A = B ) $.
    syl6reqr.2 $e |- C = B $.
    $( An equality transitivity deduction.  (Contributed by NM,
       29-Mar-1998.) $)
    syl6reqr $p |- ( ph -> C = A ) $=
      wph cA cB cC syl6reqr.1 cC cB syl6reqr.2 eqcomi syl6req $.
  $}

  ${
    sylan9eq.1 $e |- ( ph -> A = B ) $.
    sylan9eq.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM, 8-May-1994.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sylan9eq $p |- ( ( ph /\ ps ) -> A = C ) $=
      wph cA cB wceq cB cC wceq cA cC wceq wps sylan9eq.1 sylan9eq.2 cA cB cC
      eqtr syl2an $.
  $}

  ${
    sylan9req.1 $e |- ( ph -> B = A ) $.
    sylan9req.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM,
       23-Jun-2007.) $)
    sylan9req $p |- ( ( ph /\ ps ) -> A = C ) $=
      wph wps cA cB cC wph cB cA sylan9req.1 eqcomd sylan9req.2 sylan9eq $.
  $}

  ${
    sylan9eqr.1 $e |- ( ph -> A = B ) $.
    sylan9eqr.2 $e |- ( ps -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM, 8-May-1994.) $)
    sylan9eqr $p |- ( ( ps /\ ph ) -> A = C ) $=
      wph wps cA cC wceq wph wps cA cB cC sylan9eqr.1 sylan9eqr.2 sylan9eq
      ancoms $.
  $}

  ${
    3eqtr3g.1 $e |- ( ph -> A = B ) $.
    3eqtr3g.2 $e |- A = C $.
    3eqtr3g.3 $e |- B = D $.
    $( A chained equality inference, useful for converting from definitions.
       (Contributed by NM, 15-Nov-1994.) $)
    3eqtr3g $p |- ( ph -> C = D ) $=
      wph cC cB cD wph cC cA cB 3eqtr3g.2 3eqtr3g.1 syl5eqr 3eqtr3g.3 syl6eq $.
  $}

  ${
    3eqtr3a.1 $e |- A = B $.
    3eqtr3a.2 $e |- ( ph -> A = C ) $.
    3eqtr3a.3 $e |- ( ph -> B = D ) $.
    $( A chained equality inference, useful for converting from definitions.
       (Contributed by Mario Carneiro, 6-Nov-2015.) $)
    3eqtr3a $p |- ( ph -> C = D ) $=
      wph cA cC cD 3eqtr3a.2 wph cA cB cD 3eqtr3a.1 3eqtr3a.3 syl5eq eqtr3d $.
  $}

  ${
    3eqtr4g.1 $e |- ( ph -> A = B ) $.
    3eqtr4g.2 $e |- C = A $.
    3eqtr4g.3 $e |- D = B $.
    $( A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 5-Aug-1993.) $)
    3eqtr4g $p |- ( ph -> C = D ) $=
      wph cC cB cD wph cC cA cB 3eqtr4g.2 3eqtr4g.1 syl5eq 3eqtr4g.3 syl6eqr $.
  $}

  ${
    3eqtr4a.1 $e |- A = B $.
    3eqtr4a.2 $e |- ( ph -> C = A ) $.
    3eqtr4a.3 $e |- ( ph -> D = B ) $.
    $( A chained equality inference, useful for converting to definitions.
       (Contributed by NM, 2-Feb-2007.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    3eqtr4a $p |- ( ph -> C = D ) $=
      wph cC cB cD wph cC cA cB 3eqtr4a.2 3eqtr4a.1 syl6eq 3eqtr4a.3 eqtr4d $.
  $}

  ${
    eq2tr.1 $e |- ( A = C -> D = F ) $.
    eq2tr.2 $e |- ( B = D -> C = G ) $.
    $( A compound transitive inference for class equality.  (Contributed by NM,
       22-Jan-2004.) $)
    eq2tri $p |- ( ( A = C /\ B = F ) <-> ( B = D /\ A = G ) ) $=
      cA cC wceq cB cD wceq wa cB cD wceq cA cC wceq wa cA cC wceq cB cF wceq
      wa cB cD wceq cA cG wceq wa cA cC wceq cB cD wceq ancom cA cC wceq cB cD
      wceq cB cF wceq cA cC wceq cD cF cB eq2tr.1 eqeq2d pm5.32i cB cD wceq cA
      cC wceq cA cG wceq cB cD wceq cC cG cA eq2tr.2 eqeq2d pm5.32i 3bitr3i $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) $)
    eleq1 $p |- ( A = B -> ( A e. C <-> B e. C ) ) $=
      cA cB wceq vx cv cA wceq vx cv cC wcel wa vx wex vx cv cB wceq vx cv cC
      wcel wa vx wex cA cC wcel cB cC wcel cA cB wceq vx cv cA wceq vx cv cC
      wcel wa vx cv cB wceq vx cv cC wcel wa vx cA cB wceq vx cv cA wceq vx cv
      cB wceq vx cv cC wcel cA cB vx cv eqeq2 anbi1d exbidv vx cA cC df-clel vx
      cB cC df-clel 3bitr4g $.

    $( Equality implies equivalence of membership.  (Contributed by NM,
       5-Aug-1993.) $)
    eleq2 $p |- ( A = B -> ( C e. A <-> C e. B ) ) $=
      cA cB wceq vx cv cC wceq vx cv cA wcel wa vx wex vx cv cC wceq vx cv cB
      wcel wa vx wex cC cA wcel cC cB wcel cA cB wceq vx cv cC wceq vx cv cA
      wcel wa vx cv cC wceq vx cv cB wcel wa vx cA cB wceq vx cv cA wcel vx cv
      cB wcel vx cv cC wceq cA cB wceq vx cv cA wcel vx cv cB wcel wb vx cA cB
      wceq vx cv cA wcel vx cv cB wcel wb vx wal vx cA cB dfcleq biimpi 19.21bi
      anbi2d exbidv vx cC cA df-clel vx cC cB df-clel 3bitr4g $.
  $}

  $( Equality implies equivalence of membership.  (Contributed by NM,
     31-May-1999.) $)
  eleq12 $p |- ( ( A = B /\ C = D ) -> ( A e. C <-> B e. D ) ) $=
    cA cB wceq cA cC wcel cB cC wcel cC cD wceq cB cD wcel cA cB cC eleq1 cC cD
    cB eleq2 sylan9bb $.

  ${
    eleq1i.1 $e |- A = B $.
    $( Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)
    eleq1i $p |- ( A e. C <-> B e. C ) $=
      cA cB wceq cA cC wcel cB cC wcel wb eleq1i.1 cA cB cC eleq1 ax-mp $.

    $( Inference from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)
    eleq2i $p |- ( C e. A <-> C e. B ) $=
      cA cB wceq cC cA wcel cC cB wcel wb eleq1i.1 cA cB cC eleq2 ax-mp $.

    ${
      eleq12i.2 $e |- C = D $.
      $( Inference from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) $)
      eleq12i $p |- ( A e. C <-> B e. D ) $=
        cA cC wcel cA cD wcel cB cD wcel cC cD cA eleq12i.2 eleq2i cA cB cD
        eleq1i.1 eleq1i bitri $.

      $( Theorem eleq12i is the congruence law for elementhood. $)
      $( $j congruence 'eleq12i'; $)
    $}
  $}

  ${
    eleq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction from equality to equivalence of membership.  (Contributed by
       NM, 5-Aug-1993.) $)
    eleq1d $p |- ( ph -> ( A e. C <-> B e. C ) ) $=
      wph cA cB wceq cA cC wcel cB cC wcel wb eleq1d.1 cA cB cC eleq1 syl $.

    $( Deduction from equality to equivalence of membership.  (Contributed by
       NM, 27-Dec-1993.) $)
    eleq2d $p |- ( ph -> ( C e. A <-> C e. B ) ) $=
      wph cA cB wceq cC cA wcel cC cB wcel wb eleq1d.1 cA cB cC eleq2 syl $.

    ${
      eleq12d.2 $e |- ( ph -> C = D ) $.
      $( Deduction from equality to equivalence of membership.  (Contributed by
         NM, 31-May-1994.) $)
      eleq12d $p |- ( ph -> ( A e. C <-> B e. D ) ) $=
        wph cA cC wcel cA cD wcel cB cD wcel wph cC cD cA eleq12d.2 eleq2d wph
        cA cB cD eleq1d.1 eleq1d bitrd $.
    $}
  $}

  $( A transitive-type law relating membership and equality.  (Contributed by
     NM, 9-Apr-1994.) $)
  eleq1a $p |- ( A e. B -> ( C = A -> C e. B ) ) $=
    cC cA wceq cC cB wcel cA cB wcel cC cA cB eleq1 biimprcd $.

  ${
    eqeltr.1 $e |- A = B $.
    eqeltr.2 $e |- B e. C $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqeltri $p |- A e. C $=
      cA cC wcel cB cC wcel eqeltr.2 cA cB cC eqeltr.1 eleq1i mpbir $.
  $}

  ${
    eqeltrr.1 $e |- A = B $.
    eqeltrr.2 $e |- A e. C $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqeltrri $p |- B e. C $=
      cB cA cC cA cB eqeltrr.1 eqcomi eqeltrr.2 eqeltri $.
  $}

  ${
    eleqtr.1 $e |- A e. B $.
    eleqtr.2 $e |- B = C $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eleqtri $p |- A e. C $=
      cA cB wcel cA cC wcel eleqtr.1 cB cC cA eleqtr.2 eleq2i mpbi $.
  $}

  ${
    eleqtrr.1 $e |- A e. B $.
    eleqtrr.2 $e |- C = B $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eleqtrri $p |- A e. C $=
      cA cB cC eleqtrr.1 cC cB eleqtrr.2 eqcomi eleqtri $.
  $}

  ${
    eqeltrd.1 $e |- ( ph -> A = B ) $.
    eqeltrd.2 $e |- ( ph -> B e. C ) $.
    $( Substitution of equal classes into membership relation, deduction form.
       (Contributed by Raph Levien, 10-Dec-2002.) $)
    eqeltrd $p |- ( ph -> A e. C ) $=
      wph cA cC wcel cB cC wcel eqeltrd.2 wph cA cB cC eqeltrd.1 eleq1d mpbird
      $.
  $}

  ${
    eqeltrrd.1 $e |- ( ph -> A = B ) $.
    eqeltrrd.2 $e |- ( ph -> A e. C ) $.
    $( Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)
    eqeltrrd $p |- ( ph -> B e. C ) $=
      wph cB cA cC wph cA cB eqeltrrd.1 eqcomd eqeltrrd.2 eqeltrd $.
  $}

  ${
    eleqtrd.1 $e |- ( ph -> A e. B ) $.
    eleqtrd.2 $e |- ( ph -> B = C ) $.
    $( Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)
    eleqtrd $p |- ( ph -> A e. C ) $=
      wph cA cB wcel cA cC wcel eleqtrd.1 wph cB cC cA eleqtrd.2 eleq2d mpbid
      $.
  $}

  ${
    eleqtrrd.1 $e |- ( ph -> A e. B ) $.
    eleqtrrd.2 $e |- ( ph -> C = B ) $.
    $( Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)
    eleqtrrd $p |- ( ph -> A e. C ) $=
      wph cA cB cC eleqtrrd.1 wph cC cB eleqtrrd.2 eqcomd eleqtrd $.
  $}

  ${
    3eltr3.1 $e |- A e. B $.
    3eltr3.2 $e |- A = C $.
    3eltr3.3 $e |- B = D $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr3i $p |- C e. D $=
      cA cC cD 3eltr3.2 cA cB cD 3eltr3.1 3eltr3.3 eleqtri eqeltrri $.
  $}

  ${
    3eltr4.1 $e |- A e. B $.
    3eltr4.2 $e |- C = A $.
    3eltr4.3 $e |- D = B $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr4i $p |- C e. D $=
      cC cA cD 3eltr4.2 cA cB cD 3eltr4.1 3eltr4.3 eleqtrri eqeltri $.
  $}

  ${
    3eltr3d.1 $e |- ( ph -> A e. B ) $.
    3eltr3d.2 $e |- ( ph -> A = C ) $.
    3eltr3d.3 $e |- ( ph -> B = D ) $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr3d $p |- ( ph -> C e. D ) $=
      wph cA cC cD 3eltr3d.2 wph cA cB cD 3eltr3d.1 3eltr3d.3 eleqtrd eqeltrrd
      $.
  $}

  ${
    3eltr4d.1 $e |- ( ph -> A e. B ) $.
    3eltr4d.2 $e |- ( ph -> C = A ) $.
    3eltr4d.3 $e |- ( ph -> D = B ) $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr4d $p |- ( ph -> C e. D ) $=
      wph cC cA cD 3eltr4d.2 wph cA cB cD 3eltr4d.1 3eltr4d.3 eleqtrrd eqeltrd
      $.
  $}

  ${
    3eltr3g.1 $e |- ( ph -> A e. B ) $.
    3eltr3g.2 $e |- A = C $.
    3eltr3g.3 $e |- B = D $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr3g $p |- ( ph -> C e. D ) $=
      wph cA cB wcel cC cD wcel 3eltr3g.1 cA cC cB cD 3eltr3g.2 3eltr3g.3
      eleq12i sylib $.
  $}

  ${
    3eltr4g.1 $e |- ( ph -> A e. B ) $.
    3eltr4g.2 $e |- C = A $.
    3eltr4g.3 $e |- D = B $.
    $( Substitution of equal classes into membership relation.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    3eltr4g $p |- ( ph -> C e. D ) $=
      wph cA cB wcel cC cD wcel 3eltr4g.1 cC cA cD cB 3eltr4g.2 3eltr4g.3
      eleq12i sylibr $.
  $}

  ${
    syl5eqel.1 $e |- A = B $.
    syl5eqel.2 $e |- ( ph -> B e. C ) $.
    $( B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl5eqel $p |- ( ph -> A e. C ) $=
      wph cA cB cC cA cB wceq wph syl5eqel.1 a1i syl5eqel.2 eqeltrd $.
  $}

  ${
    syl5eqelr.1 $e |- B = A $.
    syl5eqelr.2 $e |- ( ph -> B e. C ) $.
    $( B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl5eqelr $p |- ( ph -> A e. C ) $=
      wph cA cB cC cB cA syl5eqelr.1 eqcomi syl5eqelr.2 syl5eqel $.
  $}

  ${
    syl5eleq.1 $e |- A e. B $.
    syl5eleq.2 $e |- ( ph -> B = C ) $.
    $( B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl5eleq $p |- ( ph -> A e. C ) $=
      wph cA cB cC cA cB wcel wph syl5eleq.1 a1i syl5eleq.2 eleqtrd $.
  $}

  ${
    syl5eleqr.1 $e |- A e. B $.
    syl5eleqr.2 $e |- ( ph -> C = B ) $.
    $( B membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl5eleqr $p |- ( ph -> A e. C ) $=
      wph cA cB cC syl5eleqr.1 wph cC cB syl5eleqr.2 eqcomd syl5eleq $.
  $}

  ${
    syl6eqel.1 $e |- ( ph -> A = B ) $.
    syl6eqel.2 $e |- B e. C $.
    $( A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl6eqel $p |- ( ph -> A e. C ) $=
      wph cA cB cC syl6eqel.1 cB cC wcel wph syl6eqel.2 a1i eqeltrd $.
  $}

  ${
    syl6eqelr.1 $e |- ( ph -> B = A ) $.
    syl6eqelr.2 $e |- B e. C $.
    $( A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl6eqelr $p |- ( ph -> A e. C ) $=
      wph cA cB cC wph cB cA syl6eqelr.1 eqcomd syl6eqelr.2 syl6eqel $.
  $}

  ${
    syl6eleq.1 $e |- ( ph -> A e. B ) $.
    syl6eleq.2 $e |- B = C $.
    $( A membership and equality inference.  (Contributed by NM,
       4-Jan-2006.) $)
    syl6eleq $p |- ( ph -> A e. C ) $=
      wph cA cB cC syl6eleq.1 cB cC wceq wph syl6eleq.2 a1i eleqtrd $.
  $}

  ${
    syl6eleqr.1 $e |- ( ph -> A e. B ) $.
    syl6eleqr.2 $e |- C = B $.
    $( A membership and equality inference.  (Contributed by NM,
       24-Apr-2005.) $)
    syl6eleqr $p |- ( ph -> A e. C ) $=
      wph cA cB cC syl6eleqr.1 cC cB syl6eleqr.2 eqcomi syl6eleq $.
  $}

  ${
    eleq2s.1 $e |- ( A e. B -> ph ) $.
    eleq2s.2 $e |- C = B $.
    $( Substitution of equal classes into a membership antecedent.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    eleq2s $p |- ( A e. C -> ph ) $=
      cA cC wcel cA cB wcel wph cC cB cA eleq2s.2 eleq2i eleq2s.1 sylbi $.
  $}

  ${
    eqneltrd.1 $e |- ( ph -> A = B ) $.
    eqneltrd.2 $e |- ( ph -> -. B e. C ) $.
    $( If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    eqneltrd $p |- ( ph -> -. A e. C ) $=
      wph cA cC wcel cB cC wcel eqneltrd.2 wph cA cB cC eqneltrd.1 eleq1d
      mtbird $.
  $}

  ${
    eqneltrrd.1 $e |- ( ph -> A = B ) $.
    eqneltrrd.2 $e |- ( ph -> -. A e. C ) $.
    $( If a class is not an element of another class, an equal class is also
       not an element.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    eqneltrrd $p |- ( ph -> -. B e. C ) $=
      wph cA cC wcel cB cC wcel eqneltrrd.2 wph cA cB cC eqneltrrd.1 eleq1d
      mtbid $.
  $}

  ${
    neleqtrd.1 $e |- ( ph -> -. C e. A ) $.
    neleqtrd.2 $e |- ( ph -> A = B ) $.
    $( If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    neleqtrd $p |- ( ph -> -. C e. B ) $=
      wph cC cA wcel cC cB wcel neleqtrd.1 wph cA cB cC neleqtrd.2 eleq2d mtbid
      $.
  $}

  ${
    neleqtrrd.1 $e |- ( ph -> -. C e. B ) $.
    neleqtrrd.2 $e |- ( ph -> A = B ) $.
    $( If a class is not an element of another class, it is also not an element
       of an equal class.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    neleqtrrd $p |- ( ph -> -. C e. A ) $=
      wph cC cA wcel cC cB wcel neleqtrrd.1 wph cA cB cC neleqtrrd.2 eleq2d
      mtbird $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    cleqh.1 $e |- ( y e. A -> A. x y e. A ) $.
    cleqh.2 $e |- ( y e. B -> A. x y e. B ) $.
    $( Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.) $)
    cleqh $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      cA cB wceq vy cv cA wcel vy cv cB wcel wb vy wal vx cv cA wcel vx cv cB
      wcel wb vx wal vy cA cB dfcleq vx cv cA wcel vx cv cB wcel wb vx wal vy
      cv cA wcel vy cv cB wcel wb vy wal vx cv cA wcel vx cv cB wcel wb vy cv
      cA wcel vy cv cB wcel wb vx vy vx cv cA wcel vx cv cB wcel wb vy ax-17 vy
      cv cA wcel vy cv cB wcel wb vy cv cA wcel vy cv cB wcel wi vy cv cB wcel
      vy cv cA wcel wi wa vx vy cv cA wcel vy cv cB wcel dfbi2 vy cv cA wcel vy
      cv cB wcel wi vy cv cB wcel vy cv cA wcel wi vx vy cv cA wcel vy cv cB
      wcel vx cleqh.1 cleqh.2 hbim vy cv cB wcel vy cv cA wcel vx cleqh.2
      cleqh.1 hbim hban hbxfrbi vx vy weq vx cv cA wcel vx cv cB wcel wb vy cv
      cA wcel vy cv cB wcel wb vx vy weq vx cv cA wcel vy cv cA wcel vx cv cB
      wcel vy cv cB wcel vx cv vy cv cA eleq1 vx cv vy cv cB eleq1 bibi12d
      biimpd cbv3h vy cv cA wcel vy cv cB wcel wb vx cv cA wcel vx cv cB wcel
      wb vy vx vy cv cA wcel vy cv cB wcel wb vy cv cA wcel vy cv cB wcel wi vy
      cv cB wcel vy cv cA wcel wi wa vx vy cv cA wcel vy cv cB wcel dfbi2 vy cv
      cA wcel vy cv cB wcel wi vy cv cB wcel vy cv cA wcel wi vx vy cv cA wcel
      vy cv cB wcel vx cleqh.1 cleqh.2 hbim vy cv cB wcel vy cv cA wcel vx
      cleqh.2 cleqh.1 hbim hban hbxfrbi vx cv cA wcel vx cv cB wcel wb vy ax-17
      vy vx weq vx cv cA wcel vx cv cB wcel wb vy cv cA wcel vy cv cB wcel wb
      vx cv cA wcel vx cv cB wcel wb vy cv cA wcel vy cv cB wcel wb wb vx vy vx
      vy weq vx cv cA wcel vy cv cA wcel vx cv cB wcel vy cv cB wcel vx cv vy
      cv cA eleq1 vx cv vy cv cB eleq1 bibi12d equcoms biimprd cbv3h impbii
      bitr4i $.
  $}

  $( A way of showing two classes are not equal.  (Contributed by NM,
     1-Apr-1997.) $)
  nelneq $p |- ( ( A e. C /\ -. B e. C ) -> -. A = B ) $=
    cA cC wcel cA cB wceq cB cC wcel cA cB wceq cA cC wcel cB cC wcel cA cB cC
    eleq1 biimpcd con3and $.

  $( A way of showing two classes are not equal.  (Contributed by NM,
     12-Jan-2002.) $)
  nelneq2 $p |- ( ( A e. B /\ -. A e. C ) -> -. B = C ) $=
    cA cB wcel cB cC wceq cA cC wcel cB cC wceq cA cB wcel cA cC wcel cB cC cA
    eleq2 biimpcd con3and $.

  ${
    $d x y $.  $d y A $.
    $( Lemma for ~ eqsb3 .  (Contributed by Rodolfo Medina, 28-Apr-2010.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    eqsb3lem $p |- ( [ x / y ] y = A <-> x = A ) $=
      vy cv cA wceq vx cv cA wceq vy vx vx cv cA wceq vy nfv vy cv vx cv cA
      eqeq1 sbie $.
  $}

  ${
    $d y A $.  $d w y $.  $d w A $.  $d x w $.
    $( Substitution applied to an atomic wff (class version of ~ equsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.) $)
    eqsb3 $p |- ( [ x / y ] y = A <-> x = A ) $=
      vy cv cA wceq vy vw wsb vw vx wsb vw cv cA wceq vw vx wsb vy cv cA wceq
      vy vx wsb vx cv cA wceq vy cv cA wceq vy vw wsb vw cv cA wceq vw vx vw vy
      cA eqsb3lem sbbii vy cv cA wceq vy vx vw vy cv cA wceq vw nfv sbco2 vx vw
      cA eqsb3lem 3bitr3i $.
  $}

  ${
    $d y A $.  $d w y $.  $d w A $.  $d w x $.
    $( Substitution applied to an atomic wff (class version of ~ elsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.)  (Proof shortened by
       Andrew Salmon, 14-Jun-2011.) $)
    clelsb3 $p |- ( [ x / y ] y e. A <-> x e. A ) $=
      vw cv cA wcel vw vy wsb vy vx wsb vw cv cA wcel vw vx wsb vy cv cA wcel
      vy vx wsb vx cv cA wcel vw cv cA wcel vw vx vy vw cv cA wcel vy nfv sbco2
      vw cv cA wcel vw vy wsb vy cv cA wcel vy vx vw cv cA wcel vy cv cA wcel
      vw vy vy cv cA wcel vw nfv vw cv vy cv cA eleq1 sbie sbbii vw cv cA wcel
      vx cv cA wcel vw vx vx cv cA wcel vw nfv vw cv vx cv cA eleq1 sbie
      3bitr3i $.
  $}

  ${
    hbxfr.1 $e |- A = B $.
    hbxfr.2 $e |- ( y e. B -> A. x y e. B ) $.
    $( A utility lemma to transfer a bound-variable hypothesis builder into a
       definition.  See ~ hbxfrbi for equivalence version.  (Contributed by NM,
       21-Aug-2007.) $)
    hbxfreq $p |- ( y e. A -> A. x y e. A ) $=
      vy cv cA wcel vy cv cB wcel vx cA cB vy cv hbxfr.1 eleq2i hbxfr.2 hbxfrbi
      $.
  $}

  ${
    $d w y A $.  $d w x z $.
    hblem.1 $e |- ( y e. A -> A. x y e. A ) $.
    $( Change the free variable of a hypothesis builder.  Lemma for ~ nfcrii .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    hblem $p |- ( z e. A -> A. x z e. A ) $=
      vy cv cA wcel vy vz wsb vy cv cA wcel vy vz wsb vx wal vz cv cA wcel vz
      cv cA wcel vx wal vy cv cA wcel vy vz vx hblem.1 hbsb vz vy cA clelsb3 vy
      cv cA wcel vy vz wsb vz cv cA wcel vx vz vy cA clelsb3 albii 3imtr3i $.
  $}

  ${
    $d x A y $.  $d ph y $.
    $( Equality of a class variable and a class abstraction (also called a
       class builder).  Theorem 5.1 of [Quine] p. 34.  This theorem shows the
       relationship between expressions with class abstractions and expressions
       with class variables.  Note that ~ abbi and its relatives are among
       those useful for converting theorems with class variables to equivalent
       theorems with wff variables, by first substituting a class abstraction
       for each class variable.

       Class variables can always be eliminated from a theorem to result in an
       equivalent theorem with wff variables, and vice-versa.  The idea is
       roughly as follows.  To convert a theorem with a wff variable ` ph `
       (that has a free variable ` x ` ) to a theorem with a class variable
       ` A ` , we substitute ` x e. A ` for ` ph ` throughout and simplify,
       where ` A ` is a new class variable not already in the wff.  An example
       is the conversion of ~ zfauscl to ~ inex1 (look at the instance of
       ~ zfauscl that occurs in the proof of ~ inex1 ).  Conversely, to convert
       a theorem with a class variable ` A ` to one with ` ph ` , we substitute
       ` { x | ph } ` for ` A ` throughout and simplify, where ` x ` and ` ph `
       are new set and wff variables not already in the wff.  An example is
       ~ cp , which derives a formula containing wff variables from
       substitution instances of the class variables in its equivalent
       formulation ~ cplem2 .  For more information on class variables, see
       Quine pp. 15-21 and/or Takeuti and Zaring pp. 10-13.  (Contributed by
       NM, 5-Aug-1993.) $)
    abeq2 $p |- ( A = { x | ph } <-> A. x ( x e. A <-> ph ) ) $=
      cA wph vx cab wceq vx cv cA wcel vx cv wph vx cab wcel wb vx wal vx cv cA
      wcel wph wb vx wal vx vy cA wph vx cab vy cv cA wcel vx ax-17 wph vx vy
      hbab1 cleqh vx cv cA wcel vx cv wph vx cab wcel wb vx cv cA wcel wph wb
      vx vx cv wph vx cab wcel wph vx cv cA wcel wph vx abid bibi2i albii bitri
      $.
  $}

  ${
    $d x A y $.  $d ph y $.
    $( Equality of a class variable and a class abstraction.  (Contributed by
       NM, 20-Aug-1993.) $)
    abeq1 $p |- ( { x | ph } = A <-> A. x ( ph <-> x e. A ) ) $=
      cA wph vx cab wceq vx cv cA wcel wph wb vx wal wph vx cab cA wceq wph vx
      cv cA wcel wb vx wal wph vx cA abeq2 wph vx cab cA eqcom wph vx cv cA
      wcel wb vx cv cA wcel wph wb vx wph vx cv cA wcel bicom albii 3bitr4i $.
  $}

  ${
    abeqi.1 $e |- A = { x | ph } $.
    $( Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 3-Apr-1996.) $)
    abeq2i $p |- ( x e. A <-> ph ) $=
      vx cv cA wcel vx cv wph vx cab wcel wph cA wph vx cab vx cv abeqi.1
      eleq2i wph vx abid bitri $.
  $}

  ${
    abeqri.1 $e |- { x | ph } = A $.
    $( Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 31-Jul-1994.) $)
    abeq1i $p |- ( ph <-> x e. A ) $=
      wph vx cv wph vx cab wcel vx cv cA wcel wph vx abid wph vx cab cA vx cv
      abeqri.1 eleq2i bitr3i $.
  $}

  ${
    abeqd.1 $e |- ( ph -> A = { x | ps } ) $.
    $( Equality of a class variable and a class abstraction (deduction).
       (Contributed by NM, 16-Nov-1995.) $)
    abeq2d $p |- ( ph -> ( x e. A <-> ps ) ) $=
      wph vx cv cA wcel vx cv wps vx cab wcel wps wph cA wps vx cab vx cv
      abeqd.1 eleq2d wps vx abid syl6bb $.
  $}

  ${
    $d ph y $.  $d ps y $.  $d x y $.
    $( Equivalent wff's correspond to equal class abstractions.  (Contributed
       by NM, 25-Nov-2013.)  (Revised by Mario Carneiro, 11-Aug-2016.) $)
    abbi $p |- ( A. x ( ph <-> ps ) <-> { x | ph } = { x | ps } ) $=
      wph vx cab wps vx cab wceq vy cv wph vx cab wcel vy cv wps vx cab wcel wb
      vy wal wph wps wb vx wal vy wph vx cab wps vx cab dfcleq vy cv wph vx cab
      wcel vy cv wps vx cab wcel wb wph wps wb vy vx vy cv wph vx cab wcel vy
      cv wps vx cab wcel vx wph vx vy nfsab1 wps vx vy nfsab1 nfbi wph wps wb
      vy nfv vy cv vx cv wceq vy cv wph vx cab wcel wph vy cv wps vx cab wcel
      wps vy cv wph vx cab wcel wph vx vy wsb vy cv vx cv wceq wph wph vy vx
      df-clab wph vy vx sbequ12r syl5bb vy cv wps vx cab wcel wps vx vy wsb vy
      cv vx cv wceq wps wps vy vx df-clab wps vy vx sbequ12r syl5bb bibi12d
      cbval bitr2i $.
  $}

  ${
    $d x A $.
    abbiri.1 $e |- ( x e. A <-> ph ) $.
    $( Equality of a class variable and a class abstraction (inference rule).
       (Contributed by NM, 5-Aug-1993.) $)
    abbi2i $p |- A = { x | ph } $=
      cA wph vx cab wceq vx cv cA wcel wph wb vx wph vx cA abeq2 abbiri.1
      mpgbir $.
  $}

  ${
    abbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalent wff's yield equal class abstractions (inference rule).
       (Contributed by NM, 5-Aug-1993.) $)
    abbii $p |- { x | ph } = { x | ps } $=
      wph wps wb wph vx cab wps vx cab wceq vx wph wps vx abbi abbii.1 mpgbi $.

    $( Theorem abbii is the congruence law for class abstraction. $)
    $( $j congruence 'abbii'; $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps y $.  $d ch y $.  $( ` y ` is a dummy var. $)
    abbid.1 $e |- F/ x ph $.
    abbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    abbid $p |- ( ph -> { x | ps } = { x | ch } ) $=
      wph wps wch wb vx wal wps vx cab wch vx cab wceq wph wps wch wb vx
      abbid.1 abbid.2 alrimi wps wch vx abbi sylib $.
  $}

  ${
    $d x ph $.
    abbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal class abstractions (deduction rule).
       (Contributed by NM, 10-Aug-1993.) $)
    abbidv $p |- ( ph -> { x | ps } = { x | ch } ) $=
      wph wps wch vx wph vx nfv abbidv.1 abbid $.
  $}

  ${
    $d x y A $.  $d ph x y $.  $d ps y $.  $( ` y ` is a dummy var. $)
    abbirdv.1 $e |- ( ph -> ( x e. A <-> ps ) ) $.
    $( Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) $)
    abbi2dv $p |- ( ph -> A = { x | ps } ) $=
      wph vx cv cA wcel wps wb vx wal cA wps vx cab wceq wph vx cv cA wcel wps
      wb vx abbirdv.1 alrimiv wps vx cA abeq2 sylibr $.
  $}

  ${
    $d x y A $.  $d ph x y $.  $d ps y $.  $( ` y ` is a dummy var. $)
    abbildv.1 $e |- ( ph -> ( ps <-> x e. A ) ) $.
    $( Deduction from a wff to a class abstraction.  (Contributed by NM,
       9-Jul-1994.) $)
    abbi1dv $p |- ( ph -> { x | ps } = A ) $=
      wph wps vx cv cA wcel wb vx wal wps vx cab cA wceq wph wps vx cv cA wcel
      wb vx abbildv.1 alrimiv wps vx cA abeq1 sylibr $.
  $}

  ${
    $d x A $.
    $( A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 26-Dec-1993.) $)
    abid2 $p |- { x | x e. A } = A $=
      cA vx cv cA wcel vx cab vx cv cA wcel vx cA vx cv cA wcel biid abbi2i
      eqcomi $.
  $}

  ${
    $d x z $.  $d y z $.  $d ph z $.  $d ps z $.
    cbvab.1 $e |- F/ y ph $.
    cbvab.2 $e |- F/ x ps $.
    cbvab.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by Andrew Salmon, 11-Jul-2011.) $)
    cbvab $p |- { x | ph } = { y | ps } $=
      vz wph vx cab wps vy cab wph vx vz wsb wps vy vz wsb vz cv wph vx cab
      wcel vz cv wps vy cab wcel wph wps vy vz wsb vx vz wps vy vz vx cbvab.2
      nfsb wph wps vy vx wsb vx cv vz cv wceq wps vy vz wsb wps wph vy vx
      cbvab.1 vy cv vx cv wceq wph wps wph wps wb vx vy cbvab.3 equcoms bicomd
      sbie wps vx vz vy sbequ syl5bbr sbie wph vz vx df-clab wps vz vy df-clab
      3bitr4i eqriv $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvabv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-May-1999.) $)
    cbvabv $p |- { x | ph } = { y | ps } $=
      wph wps vx vy wph vy nfv wps vx nfv cbvabv.1 cbvab $.
  $}

  ${
    $d x A y $.  $d ph y $.
    $( Membership of a class variable in a class abstraction.  (Contributed by
       NM, 23-Dec-1993.) $)
    clelab $p |- ( A e. { x | ph } <-> E. x ( x = A /\ ph ) ) $=
      vy cv cA wceq vy cv wph vx cab wcel wa vy wex vy cv cA wceq wph vx vy wsb
      wa vy wex cA wph vx cab wcel vx cv cA wceq wph wa vx wex vy cv cA wceq vy
      cv wph vx cab wcel wa vy cv cA wceq wph vx vy wsb wa vy vy cv wph vx cab
      wcel wph vx vy wsb vy cv cA wceq wph vy vx df-clab anbi2i exbii vy cA wph
      vx cab df-clel vx cv cA wceq wph wa vy cv cA wceq wph vx vy wsb wa vx vy
      vx cv cA wceq wph wa vy nfv vy cv cA wceq wph vx vy wsb vx vy cv cA wceq
      vx nfv wph vx vy nfs1v nfan vx cv vy cv wceq vx cv cA wceq vy cv cA wceq
      wph wph vx vy wsb vx cv vy cv cA eqeq1 wph vx vy sbequ12 anbi12d cbvex
      3bitr4i $.
  $}

  ${
    $d y A $.  $d y ph $.  $d x y $.
    $( Membership of a class abstraction in another class.  (Contributed by NM,
       17-Jan-2006.) $)
    clabel $p |- ( { x | ph } e. A <->
                 E. y ( y e. A /\ A. x ( x e. y <-> ph ) ) ) $=
      wph vx cab cA wcel vy cv wph vx cab wceq vy cv cA wcel wa vy wex vy cv cA
      wcel vx cv vy cv wcel wph wb vx wal wa vy wex vy wph vx cab cA df-clel vy
      cv wph vx cab wceq vy cv cA wcel wa vy cv cA wcel vx cv vy cv wcel wph wb
      vx wal wa vy vy cv wph vx cab wceq vx cv vy cv wcel wph wb vx wal vy cv
      cA wcel wph vx vy cv abeq2 anbi2ci exbii bitri $.
  $}

  ${
    $d z A $.  $d z x $.  $d z y $.
    $( The right-hand side of the second equality is a way of representing
       proper substitution of ` y ` for ` x ` into a class variable.
       (Contributed by NM, 14-Sep-2003.) $)
    sbab $p |- ( x = y -> A = { z | [ y / x ] z e. A } ) $=
      vx cv vy cv wceq vz cv cA wcel vx vy wsb vz cA vz cv cA wcel vx vy
      sbequ12 abbi2dv $.
  $}


