import DivRemFV.Air

namespace DivRemFV.Generated

def incoming9618 : Constraint := .lookup [⟨41, some 131, #[32, 33, 34, 35, 36, 37, 38, 39, 55, 56, 57, 58]⟩] [⟨62, some 43, #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩]
def incoming9620 : Constraint := .lookup [⟨41, some 132, #[32, 33, 34, 35, 36, 37, 38, 39, 55, 56, 57, 58]⟩] [⟨61, some 121, #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩]
def incoming9622 : Constraint := .lookup [⟨41, some 133, #[32, 33, 34, 35, 36, 37, 38, 39, 55, 56, 57, 58]⟩] [⟨62, some 43, #[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15]⟩]
def incoming9624 : Constraint := .lookup [⟨41, some 134, #[32, 33, 34, 35, 36, 37, 38, 39, 55, 56, 57, 58]⟩] [⟨61, some 121, #[0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15]⟩]
def incoming9645 : Constraint := .lookup [⟨41, some 142, #[48, 49, 52, 53, 41, 54]⟩] [⟨64, some 23, #[0, 1, 2, 3, 4, 5]⟩]
def incoming9648 : Constraint := .lookup [⟨41, some 143, #[48, 49, 52, 53, 41, 54]⟩] [⟨63, some 51, #[0, 1, 2, 3, 4, 5]⟩]
def incoming9651 : Constraint := .lookup [⟨41, some 144, #[48, 49, 52, 53, 41, 54]⟩] [⟨64, some 23, #[0, 1, 2, 3, 6, 7]⟩]
def incoming9654 : Constraint := .lookup [⟨41, some 145, #[48, 49, 52, 53, 41, 54]⟩] [⟨63, some 51, #[0, 1, 2, 3, 6, 7]⟩]
def incoming11986 : Constraint := .lookup [⟨62, some 43, #[25, 26, 27, 28, 29, 30, 31, 32, 16, 17, 18, 19, 20, 21, 22, 23]⟩] [⟨61, some 121, #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]⟩]
def incoming12116 : Constraint := .lookup [⟨64, some 23, #[13, 14, 15, 16, 8, 9, 10, 11]⟩] [⟨63, some 51, #[0, 1, 2, 3, 4, 5, 6, 7]⟩]

def incomingConstraints : List Constraint := [incoming9618,incoming9620,incoming9622,incoming9624,incoming9645,incoming9648,incoming9651,incoming9654,incoming11986,incoming12116]

def callTarget (call : Constraint) : Port :=
  match call with
  | .lookup _ [target] => target
  | _ => ⟨0,none,#[]⟩

end DivRemFV.Generated
