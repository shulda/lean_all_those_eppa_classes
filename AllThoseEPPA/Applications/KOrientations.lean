import AllThoseEPPA.Applications.KOrientations.Graph
import AllThoseEPPA.Applications.KOrientations.GraphPermutations
import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup
import AllThoseEPPA.Applications.KOrientations.FirstStageAutomorphismBridge
import AllThoseEPPA.Applications.KOrientations.AuxiliaryAction
import AllThoseEPPA.Applications.KOrientations.SecondWitness
import AllThoseEPPA.Applications.KOrientations.SecondStageRelationTransfer
import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier
import AllThoseEPPA.Applications.KOrientations.ReconstructionVertexAction
import AllThoseEPPA.Applications.KOrientations.SecondStageIncidence
import AllThoseEPPA.Applications.KOrientations.SecondStageMatching
import AllThoseEPPA.Applications.KOrientations.RootMatchingRelation
import AllThoseEPPA.Applications.KOrientations.RootMatchingEquiv
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction
import AllThoseEPPA.Applications.KOrientations.SecondStageRootDigraph
import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import AllThoseEPPA.Applications.KOrientations.Closures
import AllThoseEPPA.Applications.KOrientations.ClosureMinimal
import AllThoseEPPA.Applications.KOrientations.Encoding
import AllThoseEPPA.Applications.KOrientations.StructureBridge
import AllThoseEPPA.Applications.KOrientations.ClosedSubstructures
import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import AllThoseEPPA.Applications.KOrientations.PatternTransport
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulGraph
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulFunctions
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulUnary
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulTransitive
import AllThoseEPPA.Applications.KOrientations.FaithfulReachability
import AllThoseEPPA.Applications.KOrientations.FaithfulSuccessorExact
import AllThoseEPPA.Applications.KOrientations.FaithfulOutdegree
import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.Applications.KOrientations.FirstWitness

/-!
# EPPA for \(k\)-orientations with \(d\)-closures — application umbrella

The project intentionally lives under
\`AllThoseEPPA/Applications/KOrientations/\` and is developed separately
from the already certified main EPPA theorems.

This file currently imports the graph/closure foundations and their
exact interpretations in the paper's `Structure` language.
It does **not** assert that the full EPPA application is formalized.

Mathematical source: Section \`sec:orientations\` in *All those EPPA
classes*, with the October 2026 audit in the separate manuscript
repository. The next planned layers are the \(s\)- and \(d\)-language
structures, the two faithful coherent EPPA constructions, and
the choice-free reconstruction \`(x,W)\`.
-/
