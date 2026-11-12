import DivRemFV.Arithmetic

namespace DivRemFV

inductive Operation where
  | div | divu | rem | remu | divw | divuw | remw | remuw
  deriving DecidableEq, Repr

def signedQuotient {width : Nat} (a b : BitVec width) : BitVec width :=
  if b = 0 then BitVec.allOnes width
  else if a = BitVec.intMin width ∧ b = BitVec.allOnes width then BitVec.intMin width
  else BitVec.ofInt width (a.toInt.tdiv b.toInt)

def signedRemainder {width : Nat} (a b : BitVec width) : BitVec width :=
  if b = 0 then a
  else if a = BitVec.intMin width ∧ b = BitVec.allOnes width then 0
  else BitVec.ofInt width (a.toInt.tmod b.toInt)

def isaResult (op : Operation) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .div => signedQuotient a b
  | .divu => if b = 0 then BitVec.allOnes 64 else a.udiv b
  | .rem => signedRemainder a b
  | .remu => if b = 0 then a else a.umod b
  | .divw => (signedQuotient (a.setWidth 32) (b.setWidth 32)).signExtend 64
  | .divuw =>
    (if b.setWidth 32 = 0 then BitVec.allOnes 32
      else (a.setWidth 32).udiv (b.setWidth 32)).signExtend 64
  | .remw => (signedRemainder (a.setWidth 32) (b.setWidth 32)).signExtend 64
  | .remuw =>
    (if b.setWidth 32 = 0 then a.setWidth 32
      else (a.setWidth 32).umod (b.setWidth 32)).signExtend 64

abbrev Registers := Fin 32 → BitVec 64

structure MachineState where
  pc : BitVec 64
  registers : Registers

structure DivisionInstruction where
  op : Operation
  rs1 : Fin 32
  rs2 : Fin 32
  rd : Fin 32

def readRegister (registers : Registers) (index : Fin 32) : BitVec 64 :=
  if index = 0 then 0 else registers index

def writeRegister (registers : Registers) (index : Fin 32) (value : BitVec 64) : Registers :=
  fun current => if current = 0 then 0 else if current = index then value else registers current

def isaStep (instruction : DivisionInstruction) (state : MachineState) : MachineState :=
  { pc := state.pc + 4
    registers := writeRegister state.registers instruction.rd
      (isaResult instruction.op (readRegister state.registers instruction.rs1)
        (readRegister state.registers instruction.rs2)) }

abbrev LimbTuple := Fin 4 → Scalar

def encodeWord (word : BitVec 64) : LimbTuple :=
  fun index => ⟨encode64 word index, Nat.lt_trans (encode64_canonical word index) (by decide)⟩

def ComponentContract
    (accepts : Operation → LimbTuple → LimbTuple → LimbTuple → Prop) : Prop :=
  ∀ op a b output, accepts op (encodeWord a) (encodeWord b) output ↔
    output = encodeWord (isaResult op a b)

def InstructionContract (step : DivisionInstruction → MachineState → MachineState → Prop) : Prop :=
  ∀ instruction before after, step instruction before after ↔ after = isaStep instruction before

theorem isaStep_x0 (instruction : DivisionInstruction) (state : MachineState) :
    (isaStep instruction state).registers 0 = 0 := by
  simp [isaStep, writeRegister]

theorem isaStep_preserves (instruction : DivisionInstruction) (state : MachineState)
    (index : Fin 32) (nonzero : index ≠ 0) (other : index ≠ instruction.rd) :
    (isaStep instruction state).registers index = state.registers index := by
  simp [isaStep, writeRegister, nonzero, other]

end DivRemFV
