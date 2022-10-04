#!/usr/bin/env sh

./eval.py -j 8 --progress --prelude CompCert/   \
  powerpc/Stacklayout.v powerpc/CombineOp.v powerpc/Archi.v powerpc/ConstpropOpproof.v \
  powerpc/SelectLongproof.v powerpc/Conventions1.v powerpc/Asmgenproof1.v powerpc/extractionMachdep.v \
  powerpc/Asmgenproof.v powerpc/Machregs.v powerpc/Builtins1.v powerpc/Op.v powerpc/CombineOpproof.v \
  powerpc/NeedOp.v powerpc/SelectOpproof.v powerpc/ValueAOp.v powerpc/Asmgen.v powerpc/Asm.v driver/Complements.v \
  driver/Compopts.v driver/Compiler.v MenhirLib/Validator_complete.v MenhirLib/Alphabet.v MenhirLib/Interpreter_correct.v \
  MenhirLib/Validator_classes.v MenhirLib/Grammar.v MenhirLib/Validator_safe.v MenhirLib/Automaton.v MenhirLib/Main.v \
  MenhirLib/Interpreter.v MenhirLib/Interpreter_complete.v x86_32/Archi.v backend/CleanupLabels.v backend/Lineartyping.v \
  backend/Tailcall.v backend/ValueDomain.v backend/LTL.v backend/Linearize.v backend/Bounds.v backend/Renumberproof.v \
  backend/Linearizeproof.v backend/Deadcodeproof.v backend/Tunneling.v backend/Mach.v backend/Inlining.v backend/RTLgen.v \
  backend/Locations.v backend/CSEdomain.v backend/SelectDiv.v backend/Debugvar.v backend/Inliningspec.v backend/Selectionproof.v \
  backend/Selection.v backend/SplitLongproof.v backend/CSE.v backend/RTLgenspec.v backend/RTLtyping.v backend/Conventions.v \
  backend/RTLgenproof.v backend/CminorSel.v backend/Asmgenproof0.v backend/Tailcallproof.v backend/Cminortyping.v backend/Kildall.v \
  backend/Liveness.v backend/Cminor.v backend/SelectDivproof.v backend/Tunnelingproof.v backend/Inliningproof.v backend/Renumber.v \
  backend/Debugvarproof.v backend/Unusedglobproof.v backend/Deadcode.v backend/Unusedglob.v backend/ValueAnalysis.v \
  backend/Constpropproof.v backend/Stackingproof.v backend/SplitLong.v backend/Linear.v backend/Allocation.v \
  backend/CleanupLabelsproof.v backend/NeedDomain.v backend/RTL.v backend/Registers.v backend/Allocproof.v backend/Constprop.v \
  backend/CSEproof.v backend/Stacking.v common/Smallstep.v common/AST.v common/Builtins.v common/Values.v common/Linking.v \
  common/Separation.v common/Memory.v common/Memdata.v common/Subtyping.v common/Switch.v common/Builtins0.v common/Memtype.v \
  common/Globalenvs.v common/Events.v common/Determinism.v common/Behaviors.v common/Errors.v common/Unityping.v x86/Stacklayout.v \
  x86/CombineOp.v x86/ConstpropOpproof.v x86/SelectLongproof.v x86/Conventions1.v x86/Asmgenproof1.v x86/extractionMachdep.v \
  x86/Asmgenproof.v x86/Machregs.v x86/Builtins1.v x86/Op.v x86/CombineOpproof.v x86/NeedOp.v x86/SelectOpproof.v x86/ValueAOp.v \
  x86/Asmgen.v x86/Asm.v cfrontend/Cshmgen.v cfrontend/Cminorgen.v cfrontend/Cop.v cfrontend/Initializersproof.v \
  cfrontend/Cshmgenproof.v cfrontend/Csyntax.v cfrontend/Ctyping.v cfrontend/Ctypes.v cfrontend/Cminorgenproof.v cfrontend/Clight.v \
  cfrontend/Initializers.v cfrontend/SimplExpr.v cfrontend/Cexec.v cfrontend/SimplExprspec.v cfrontend/Csharpminor.v cfrontend/Csem.v \
  cfrontend/SimplExprproof.v cfrontend/ClightBigstep.v cfrontend/SimplLocals.v cfrontend/SimplLocalsproof.v cfrontend/Cstrategy.v \
  lib/FSetAVLplus.v lib/IEEE754_extra.v lib/Ordered.v lib/UnionFind.v lib/Postorder.v lib/Parmov.v lib/Integers.v lib/Maps.v lib/Lattice.v \
  lib/IntvSets.v lib/Axioms.v lib/Decidableplus.v lib/Floats.v lib/Iteration.v lib/Wfsimpl.v lib/Zbits.v lib/BoolEqual.v lib/Coqlib.v \
  lib/Intv.v lib/Heaps.v arm/Stacklayout.v arm/CombineOp.v arm/Archi.v arm/ConstpropOpproof.v arm/SelectLongproof.v arm/Conventions1.v \
  arm/Asmgenproof1.v arm/extractionMachdep.v arm/Asmgenproof.v arm/Machregs.v arm/Builtins1.v arm/Op.v arm/CombineOpproof.v arm/NeedOp.v \
  arm/SelectOpproof.v arm/ValueAOp.v arm/Asmgen.v arm/Asm.v export/Ctypesdefs.v export/Clightdefs.v export/Csyntaxdefs.v \
  flocq/Prop/Mult_error.v flocq/Prop/Double_rounding.v flocq/Prop/Div_sqrt_error.v flocq/Prop/Plus_error.v flocq/Prop/Relative.v \
  flocq/Prop/Round_odd.v flocq/Prop/Sterbenz.v flocq/Core/Generic_fmt.v flocq/Core/FLX.v flocq/Core/FIX.v flocq/Core/Zaux.v \
  flocq/Core/Digits.v flocq/Core/Core.v flocq/Core/Defs.v flocq/Core/Float_prop.v flocq/Core/FTZ.v flocq/Core/FLT.v flocq/Core/Round_NE.v \
  flocq/Core/Raux.v flocq/Core/Round_pred.v flocq/Core/Ulp.v flocq/Calc/Div.v flocq/Calc/Sqrt.v flocq/Calc/Operations.v flocq/Calc/Bracket.v \
  flocq/Calc/Round.v flocq/IEEE754/SpecFloatCompat.v flocq/IEEE754/Binary.v flocq/IEEE754/Bits.v flocq/Version.v cparser/Cabs.v \
  cparser/Parser.v riscV/Stacklayout.v riscV/CombineOp.v riscV/Archi.v riscV/ConstpropOpproof.v riscV/SelectLongproof.v riscV/Conventions1.v \
  riscV/Asmgenproof1.v riscV/extractionMachdep.v riscV/Asmgenproof.v riscV/Machregs.v riscV/Builtins1.v riscV/Op.v riscV/CombineOpproof.v \
  riscV/NeedOp.v riscV/SelectOpproof.v riscV/ValueAOp.v riscV/Asmgen.v riscV/Asm.v extraction/extraction.v aarch64/SelectLong.v \
  aarch64/Stacklayout.v aarch64/CombineOp.v aarch64/SelectOp.v aarch64/ConstpropOp.v aarch64/Archi.v aarch64/ConstpropOpproof.v \
  aarch64/SelectLongproof.v aarch64/Conventions1.v aarch64/Asmgenproof1.v aarch64/extractionMachdep.v aarch64/Asmgenproof.v aarch64/Machregs.v\
  aarch64/Builtins1.v aarch64/Op.v aarch64/CombineOpproof.v aarch64/NeedOp.v aarch64/SelectOpproof.v aarch64/ValueAOp.v aarch64/Asmgen.v \
  aarch64/Asm.v x86_64/Archi.v 