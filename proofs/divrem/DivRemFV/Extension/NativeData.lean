import DivRemFV.NativeImport
import DivRemFV.Extension.Artifact

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace DivRemFV.Extension.NativeData
open DivRemFV.NativeImport

def n12204 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.column 8 (0)) (.cons (.column 1 (0)) .nil)) .nil)))
def n12205 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.sum (.cons (.column 7 (0)) (.cons (.product (.cons (.constant ⟨32768,by decide⟩) (.cons (.column 6 (0)) .nil))) .nil))) (.cons (.column 0 (0)) .nil)) .nil)))
def n12206 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.column 5 (0)) (.cons (.column 1 (0)) .nil)) (.cons (.column 6 (0)) .nil))))
def n12207 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.column 4 (0)) (.cons (.column 0 (0)) .nil)) (.cons (.column 6 (0)) .nil))))
def n12208 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.sum (.cons (.product (.cons (.difference (.constant ⟨65535,by decide⟩) (.cons (.column 3 (0)) .nil)) (.cons (.column 6 (0)) .nil))) (.cons (.product (.cons (.difference (.constant ⟨65535,by decide⟩) (.cons (.column 2 (0)) .nil)) (.cons (.column 6 (0)) .nil))) .nil))) .nil)))
def n12209 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.constant ⟨1,by decide⟩) (.cons (.column 6 (0)) .nil)) (.cons (.difference (.column 5 (0)) (.cons (.column 1 (0)) .nil)) .nil))))
def n12210 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.difference (.constant ⟨1,by decide⟩) (.cons (.column 6 (0)) .nil)) (.cons (.difference (.column 4 (0)) (.cons (.column 0 (0)) .nil)) .nil))))
def n12211 : RawConstraint := .vanishing 67 none (.product (.cons (.column 9 (0)) (.cons (.sum (.cons (.product (.cons (.difference (.constant ⟨1,by decide⟩) (.cons (.column 6 (0)) .nil)) (.cons (.column 3 (0)) .nil))) (.cons (.product (.cons (.difference (.constant ⟨1,by decide⟩) (.cons (.column 6 (0)) .nil)) (.cons (.column 2 (0)) .nil))) .nil))) .nil)))
def n12212 : RawConstraint := .lookup [⟨67, none, #[0]⟩] [⟨98, none, #[0]⟩]
def n12213 : RawConstraint := .lookup [⟨67, none, #[1]⟩] [⟨98, none, #[0]⟩]
def n12214 : RawConstraint := .lookup [⟨67, none, #[2]⟩] [⟨98, none, #[0]⟩]
def n12215 : RawConstraint := .lookup [⟨67, none, #[3]⟩] [⟨98, none, #[0]⟩]
def n12216 : RawConstraint := .lookup [⟨67, none, #[4]⟩] [⟨98, none, #[0]⟩]
def n12217 : RawConstraint := .lookup [⟨67, none, #[5]⟩] [⟨98, none, #[0]⟩]
def n12218 : RawConstraint := .vanishing 67 none (.difference (.product (.cons (.column 6 (0)) (.cons (.column 6 (0)) .nil))) (.cons (.column 6 (0)) .nil))
def n12219 : RawConstraint := .lookup [⟨67, none, #[7]⟩] [⟨97, none, #[0]⟩]
def n12220 : RawConstraint := .lookup [⟨67, none, #[8]⟩] [⟨98, none, #[0]⟩]
def n12221 : RawConstraint := .vanishing 67 none (.difference (.product (.cons (.column 9 (0)) (.cons (.column 9 (0)) .nil))) (.cons (.column 9 (0)) .nil))

def rawConstraints : List RawConstraint := [
  n12204,
  n12205,
  n12206,
  n12207,
  n12208,
  n12209,
  n12210,
  n12211,
  n12212,
  n12213,
  n12214,
  n12215,
  n12216,
  n12217,
  n12218,
  n12219,
  n12220,
  n12221]

theorem translated_constraints : rawConstraints.map RawConstraint.translate = DivRemFV.Extension.constraints := by rfl

theorem native_constraints_iff (tables : Tables) :
    RawConstraintsHold tables rawConstraints ↔ ConstraintsHold tables DivRemFV.Extension.constraints := by
  rw [← translated_constraints]
  exact (translate_constraints_holds tables rawConstraints).symm

end DivRemFV.Extension.NativeData
