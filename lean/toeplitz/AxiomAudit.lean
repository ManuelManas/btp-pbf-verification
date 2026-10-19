import Lemma24
import Proposition29
import Proposition215
import SeriesLimits
import SemiInfiniteBasic
import InverseSections
import InverseMinors
import AdjacentRatios
import UniformMinors
import ExtractionDeterminants
import ExtractionPositive
import UniformPerturbation
import PlannedColumns
import GlobalConstruction
import PositiveLimits
import OneFactorFormula
import FormalizedTheorem
import OrderedMinors
import PrefixBounds
import Necessity
import TwoSidedCriterion
import RecurrenceParameters
import DenseParameters
import ParameterChart
import UnrestrictedDeterminant
import CompleteResults
import BidiagonalSwap
import FactorReordering
import ToeplitzSymbol
import PositiveMinors
import NegativeRoots
import PBFMinors
import BandStructure
import ToeplitzTheorem
import ManuscriptTheorem
import ToeplitzTail
import FlagComplement
import CanonicalLowerInverse
import MetelmannFromFlags
import ForwardConversion
import LowerOperatorBridge
import BTPToPBF
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "BTP." || (name.toString.splitOn ".BTP.").length > 1 || name.toString.startsWith "PBFStability." || (name.toString.splitOn ".PBFStability.").length > 1 then
      if info.isTheorem then
        count := count + 1
        let axs ← collectAxioms name
        for ax in axs do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        logInfo m!"AUDIT {name}: {axs.toList}"
  logInfo m!"TOTAL_THEOREMS {count}: only propext, Classical.choice, Quot.sound"
