-- The statements of the paper's main results. Each file imports only
-- `Pairwise/Definitions.lean` and `AES/AES.lean`.
import PairwiseIndependence.Theorem3
import PairwiseIndependence.Theorem4
import PairwiseIndependence.Theorem5
import PairwiseIndependence.Corollary2
import PairwiseIndependence.KeliherSui
-- Their proofs.
import PairwiseIndependence.Pairwise.SharkBound
import PairwiseIndependence.AesBounds.SuperboxBound
import PairwiseIndependence.AesBounds.FourRoundBound
import PairwiseIndependence.AesBounds.PairwiseBound
import PairwiseIndependence.KeliherSui.UpperBound
-- Lemma 7: the third singular value in the paper's Theorem 3 equals `‖Dˢ − U‖`.
import PairwiseIndependence.Pairwise.SingularValuesTail
-- Validation of the AES implementation against FIPS 197.
import PairwiseIndependence.AES.SboxFieldCertificate
import PairwiseIndependence.AES.ReferenceVectors

/-! Each statement is proved, using only the axioms listed. -/

#print axioms PairwiseIndependence.theorem3_shark
#print axioms PairwiseIndependence.theorem4_aesSuperbox
#print axioms PairwiseIndependence.theorem5_aesFourRounds
#print axioms PairwiseIndependence.corollary2_aesCipher
#print axioms PairwiseIndependence.keliherSui_aesSuperbox
