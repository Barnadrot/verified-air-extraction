import DivRemFV.CaptureSyntax
import DivRemFV.TermWire

namespace DivRemFV.CaptureSyntax

mutual
  def Term.native : Term → NativeImport.Term
    | .constant value => .constant value
    | .column index shift => .column index shift
    | .sum args => .sum args.native
    | .difference first rest => .difference first.native rest.native
    | .product args => .product args.native
  def Args.native : Args → NativeImport.Args
    | .nil => .nil
    | .cons head tail => .cons head.native tail.native
end

mutual
  theorem Term.wire_correspondence (t : Term) : TermWire.encodeTerm t.native = t.words := by
    cases t with
    | constant value => rfl
    | column index shift => rfl
    | sum args | product args => simp only [Term.native,TermWire.encodeTerm,Args.wire_correspondence,Term.words]
    | difference head tail =>
      simp only [Term.native,TermWire.encodeTerm,Term.wire_correspondence,Args.wire_correspondence,Term.words]
  theorem Args.wire_correspondence (a : Args) : TermWire.encodeArgs a.native = a.words := by
    cases a with
    | nil => rfl
    | cons head tail =>
      simp only [Args.native,TermWire.encodeArgs,Term.wire_correspondence,Args.wire_correspondence,Args.words]
end

theorem checked_term_translation (t : Term) (tables : Tables) (mid : Nat) (row : Int) :
    t.native.translate.evalField tables mid row = t.native.eval tables mid row :=
  NativeImport.Term.translate_eval tables mid row t.native

end DivRemFV.CaptureSyntax
