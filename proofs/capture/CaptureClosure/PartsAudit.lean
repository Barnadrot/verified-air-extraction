import CaptureClosure.Proof.RecursiveCapture
import CaptureClosure.Proof.SimpleWire
import CaptureClosure.Proof.NameWire
import CaptureClosure.Proof.WireNumbers
import CaptureClosure.Proof.ArgsWire
import CaptureClosure.Proof.EncodeTerm
import CaptureClosure.Proof.ColumnModel
import CaptureClosure.Proof.RowWire
import CaptureClosure.Proof.RawRegisterReads
import CaptureClosure.Proof.Rejection
import CaptureClosure.Proof.ColumnCapture
import CaptureClosure.Proof.ConstraintReads
import CaptureClosure.Proof.OptionReads
import CaptureClosure.Proof.ByteContract
import CaptureClosure.Proof.UIntRef
import CaptureClosure.Proof.PortWire
import CaptureClosure.Proof.SourceContract
import CaptureClosure.Proof.ConstraintRejection

#print axioms Perennial.divremfv.internal.airdata.SourceCapture.captureArgsBody_source
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_args
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.sum_capture
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.product_capture
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.difference_capture
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_term
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_word
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_bool
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_option_none
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_option_some
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_name
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_constant
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_column
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.zigzag_word_value
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_args
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.wire_term
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.encode_term
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_option
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_column_record
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_column
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_row
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.name_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.isNative_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.width_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.isInput_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.isOutput_correct
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.reject_nil_term
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.reject_other_term
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.reject_unknown_wire
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_option_some_frac
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.native_record
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.input_record
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.output_record
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_column
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.name_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.name_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.name_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.name_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.util.Option.hasValue_correct
#print axioms Perennial.github_com.LFDT_Lineth.zkc.pkg.util.Option.unwrap_correct
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.word_byte_values
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.all_byte_values
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_uint_ref
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.append_port
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_column_ids
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_bus
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_lookup
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_static_row
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_columns
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_rows
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_module
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_modules
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_domain
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_lookup_ports
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_bus_ports
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_entry
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_constraints
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_all_constraints
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_artifact
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_port
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_module
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_entry
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_artifact
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.serialize_checked_artifact
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.capture_to_checked_wire
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.output_term_bounded
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.artifact_bounded
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.reject_other_constraint
#print axioms Perennial.divremfv.internal.airdata.SourceCapture.reject_nil_constraint
