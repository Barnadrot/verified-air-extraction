import DivRemFV.ExtractorBinding
import DivRemFV.Statement

#print axioms DivRemFV.four_canonical_of_bounds
#print axioms DivRemFV.signed64_inputs_canonical
#print axioms DivRemFV.signed64_raw_row_sound
#print axioms DivRemFV.signed64_raw_sound
#print axioms DivRemFV.signed64_raw_component_iff
#print axioms DivRemFV.signed64_noncanonical_input_rejected
#print axioms DivRemFV.signed64_div_port_sound
#print axioms DivRemFV.signed64_rem_port_sound
#print axioms DivRemFV.ComponentBoundary64.raw_component
#print axioms DivRemFV.ComponentBoundary64.selected_holds
#print axioms DivRemFV.ComponentBoundary64.incoming_holds
#print axioms DivRemFV.ComponentBoundary64.div_call_sound
#print axioms DivRemFV.ComponentBoundary64.rem_call_sound
#print axioms DivRemFV.ExtractorBinding.raw_component
#print axioms DivRemFV.ExtractorBinding.div_call_sound
#print axioms DivRemFV.ExtractorBinding.rem_call_sound

-- The added contracts use the unchanged, explicitly reviewed ISA operations.
example (a b : DivRemFV.Limbs64) :
    DivRemFV.signedQuotient (DivRemFV.decodeFour a) (DivRemFV.decodeFour b) =
      DivRemFV.Statement.quotient (DivRemFV.decodeFour a) (DivRemFV.decodeFour b) := rfl

example (a b : DivRemFV.Limbs64) :
    DivRemFV.signedRemainder (DivRemFV.decodeFour a) (DivRemFV.decodeFour b) =
      DivRemFV.Statement.remainder (DivRemFV.decodeFour a) (DivRemFV.decodeFour b) := rfl
