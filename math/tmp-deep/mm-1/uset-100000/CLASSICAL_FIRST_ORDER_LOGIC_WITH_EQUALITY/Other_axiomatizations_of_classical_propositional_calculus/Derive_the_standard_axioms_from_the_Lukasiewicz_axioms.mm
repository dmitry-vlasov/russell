$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_Meredith_s_sole_axiom.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Used to rederive standard propositional axioms from Lukasiewicz'.
       (Contributed by NM, 23-Dec-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_luklem1 $f wff ph $.
	f1_luklem1 $f wff ps $.
	f2_luklem1 $f wff ch $.
	e0_luklem1 $e |- ( ph -> ps ) $.
	e1_luklem1 $e |- ( ps -> ch ) $.
	p_luklem1 $p |- ( ph -> ch ) $= e1_luklem1 e0_luklem1 f0_luklem1 f1_luklem1 f2_luklem1 p_luk-1 f0_luklem1 f1_luklem1 a_wi f1_luklem1 f2_luklem1 a_wi f0_luklem1 f2_luklem1 a_wi a_wi a_ax-mp f1_luklem1 f2_luklem1 a_wi f0_luklem1 f2_luklem1 a_wi a_ax-mp $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_luklem2 $f wff ph $.
	f1_luklem2 $f wff ps $.
	f2_luklem2 $f wff ch $.
	f3_luklem2 $f wff th $.
	p_luklem2 $p |- ( ( ph -> -. ps ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $= f0_luklem2 f1_luklem2 a_wn f2_luklem2 p_luk-1 f1_luklem2 f2_luklem2 p_luk-3 f1_luklem2 f1_luklem2 a_wn f2_luklem2 a_wi f0_luklem2 f2_luklem2 a_wi p_luk-1 f1_luklem2 f1_luklem2 a_wn f2_luklem2 a_wi a_wi f1_luklem2 a_wn f2_luklem2 a_wi f0_luklem2 f2_luklem2 a_wi a_wi f1_luklem2 f0_luklem2 f2_luklem2 a_wi a_wi a_wi a_ax-mp f0_luklem2 f1_luklem2 a_wn a_wi f1_luklem2 a_wn f2_luklem2 a_wi f0_luklem2 f2_luklem2 a_wi a_wi f1_luklem2 f0_luklem2 f2_luklem2 a_wi a_wi p_luklem1 f1_luklem2 f0_luklem2 f2_luklem2 a_wi f3_luklem2 p_luk-1 f0_luklem2 f1_luklem2 a_wn a_wi f1_luklem2 f0_luklem2 f2_luklem2 a_wi a_wi f0_luklem2 f2_luklem2 a_wi f3_luklem2 a_wi f1_luklem2 f3_luklem2 a_wi a_wi p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_luklem3 $f wff ph $.
	f1_luklem3 $f wff ps $.
	f2_luklem3 $f wff ch $.
	f3_luklem3 $f wff th $.
	p_luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $= f0_luklem3 f3_luklem3 a_wn p_luk-3 f0_luklem3 a_wn f3_luklem3 f1_luklem3 f2_luklem3 p_luklem2 f0_luklem3 f0_luklem3 a_wn f3_luklem3 a_wn a_wi f0_luklem3 a_wn f1_luklem3 a_wi f2_luklem3 a_wi f3_luklem3 f2_luklem3 a_wi a_wi p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_luklem4 $f wff ph $.
	f1_luklem4 $f wff ps $.
	p_luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $= f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi p_luk-2 f0_luklem4 p_luk-2 f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f1_luklem4 a_wn p_luklem3 f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi f1_luklem4 a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi a_wi a_ax-mp f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi f1_luklem4 a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi a_ax-mp f1_luklem4 a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f1_luklem4 p_luk-1 f1_luklem4 a_wn f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi a_wi f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f1_luklem4 a_wi f1_luklem4 a_wn f1_luklem4 a_wi a_wi a_ax-mp f1_luklem4 p_luk-2 f0_luklem4 a_wn f0_luklem4 a_wi f0_luklem4 a_wi f1_luklem4 a_wi f1_luklem4 a_wn f1_luklem4 a_wi f1_luklem4 p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_luklem5 $f wff ph $.
	f1_luklem5 $f wff ps $.
	p_luklem5 $p |- ( ph -> ( ps -> ph ) ) $= f0_luklem5 f0_luklem5 f0_luklem5 f1_luklem5 p_luklem3 f0_luklem5 f1_luklem5 f0_luklem5 a_wi p_luklem4 f0_luklem5 f0_luklem5 a_wn f0_luklem5 a_wi f0_luklem5 a_wi f1_luklem5 f0_luklem5 a_wi a_wi f1_luklem5 f0_luklem5 a_wi p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_luklem6 $f wff ph $.
	f1_luklem6 $f wff ps $.
	p_luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= f0_luklem6 f0_luklem6 f1_luklem6 a_wi f1_luklem6 p_luk-1 f0_luklem6 f1_luklem6 a_wi a_wn f1_luklem6 a_wn p_luklem5 f1_luklem6 a_wn f0_luklem6 f1_luklem6 a_wi f1_luklem6 f1_luklem6 p_luklem2 f1_luklem6 f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi p_luklem4 f1_luklem6 a_wn f0_luklem6 f1_luklem6 a_wi a_wn a_wi f1_luklem6 a_wn f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi p_luklem1 f0_luklem6 f1_luklem6 a_wi a_wn f1_luklem6 a_wn f0_luklem6 f1_luklem6 a_wi a_wn a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi p_luklem1 f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi p_luk-1 f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi a_wi a_wi a_ax-mp f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi p_luk-1 f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi a_wi a_ax-mp f0_luklem6 f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi p_luklem4 f0_luklem6 f1_luklem6 a_wi a_wn f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi a_wi a_ax-mp f0_luklem6 f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi f1_luklem6 a_wi f0_luklem6 f1_luklem6 a_wi a_wi f0_luklem6 f1_luklem6 a_wi p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_luklem7 $f wff ph $.
	f1_luklem7 $f wff ps $.
	f2_luklem7 $f wff ch $.
	p_luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= f0_luklem7 f1_luklem7 f2_luklem7 a_wi f2_luklem7 p_luk-1 f1_luklem7 f1_luklem7 f2_luklem7 a_wi p_luklem5 f1_luklem7 f2_luklem7 a_wi f1_luklem7 f2_luklem7 p_luk-1 f1_luklem7 f1_luklem7 f2_luklem7 a_wi f1_luklem7 a_wi f1_luklem7 f2_luklem7 a_wi f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi a_wi p_luklem1 f1_luklem7 f2_luklem7 a_wi f2_luklem7 p_luklem6 f1_luklem7 f1_luklem7 f2_luklem7 a_wi f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi a_wi f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi p_luklem1 f1_luklem7 f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi f0_luklem7 f2_luklem7 a_wi p_luk-1 f1_luklem7 f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi a_wi f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi f0_luklem7 f2_luklem7 a_wi a_wi f1_luklem7 f0_luklem7 f2_luklem7 a_wi a_wi a_wi a_ax-mp f0_luklem7 f1_luklem7 f2_luklem7 a_wi a_wi f1_luklem7 f2_luklem7 a_wi f2_luklem7 a_wi f0_luklem7 f2_luklem7 a_wi a_wi f1_luklem7 f0_luklem7 f2_luklem7 a_wi a_wi p_luklem1 $.
$}

$(Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_luklem8 $f wff ph $.
	f1_luklem8 $f wff ps $.
	f2_luklem8 $f wff ch $.
	p_luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= f2_luklem8 f0_luklem8 f1_luklem8 p_luk-1 f2_luklem8 f0_luklem8 a_wi f0_luklem8 f1_luklem8 a_wi f2_luklem8 f1_luklem8 a_wi p_luklem7 f2_luklem8 f0_luklem8 a_wi f0_luklem8 f1_luklem8 a_wi f2_luklem8 f1_luklem8 a_wi a_wi a_wi f0_luklem8 f1_luklem8 a_wi f2_luklem8 f0_luklem8 a_wi f2_luklem8 f1_luklem8 a_wi a_wi a_wi a_ax-mp $.
$}

$(Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_ax1 $f wff ph $.
	f1_ax1 $f wff ps $.
	p_ax1 $p |- ( ph -> ( ps -> ph ) ) $= f0_ax1 f1_ax1 p_luklem5 $.
$}

$(Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_ax2 $f wff ph $.
	f1_ax2 $f wff ps $.
	f2_ax2 $f wff ch $.
	p_ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= f0_ax2 f1_ax2 f2_ax2 p_luklem7 f1_ax2 f0_ax2 f2_ax2 a_wi f0_ax2 p_luklem8 f0_ax2 f2_ax2 p_luklem6 f0_ax2 f0_ax2 f2_ax2 a_wi a_wi f0_ax2 f2_ax2 a_wi f0_ax2 f1_ax2 a_wi p_luklem8 f0_ax2 f0_ax2 f2_ax2 a_wi a_wi f0_ax2 f2_ax2 a_wi a_wi f0_ax2 f1_ax2 a_wi f0_ax2 f0_ax2 f2_ax2 a_wi a_wi a_wi f0_ax2 f1_ax2 a_wi f0_ax2 f2_ax2 a_wi a_wi a_wi a_ax-mp f1_ax2 f0_ax2 f2_ax2 a_wi a_wi f0_ax2 f1_ax2 a_wi f0_ax2 f0_ax2 f2_ax2 a_wi a_wi a_wi f0_ax2 f1_ax2 a_wi f0_ax2 f2_ax2 a_wi a_wi p_luklem1 f0_ax2 f1_ax2 f2_ax2 a_wi a_wi f1_ax2 f0_ax2 f2_ax2 a_wi a_wi f0_ax2 f1_ax2 a_wi f0_ax2 f2_ax2 a_wi a_wi p_luklem1 $.
$}

$(Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_ax3 $f wff ph $.
	f1_ax3 $f wff ps $.
	p_ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= f0_ax3 a_wn f1_ax3 f0_ax3 f0_ax3 p_luklem2 f0_ax3 f1_ax3 f0_ax3 a_wi p_luklem4 f0_ax3 a_wn f1_ax3 a_wn a_wi f0_ax3 a_wn f0_ax3 a_wi f0_ax3 a_wi f1_ax3 f0_ax3 a_wi a_wi f1_ax3 f0_ax3 a_wi p_luklem1 $.
$}


