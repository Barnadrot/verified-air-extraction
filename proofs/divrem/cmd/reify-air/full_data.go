package main

import (
	"divremfv/internal/airdata"
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

func writeFullData(helpers airdata.Artifact) {
	data, err := os.ReadFile("artifacts/air.json")
	check(err)
	var full airdata.Artifact
	check(json.Unmarshal(data, &full))
	check(full.Validate())
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.NativeData\nimport DivRemFV.Extension.NativeData\nimport DivRemFV.Generated.Incoming\n\nset_option maxRecDepth 32768\nset_option maxHeartbeats 12000000\n\nnamespace DivRemFV.FullData\nopen DivRemFV.NativeImport\n\n")
	for _, c := range full.Constraints {
		fmt.Fprintf(&out, "def n%d : RawConstraint := %s\n", c.ID, nativeConstraint(c))
	}
	const blockSize = 128
	blocks := (len(full.Constraints) + blockSize - 1) / blockSize
	for block := 0; block < blocks; block++ {
		fmt.Fprintf(&out, "\ndef block%d : Array RawConstraint := #[", block)
		for i := block * blockSize; i < len(full.Constraints) && i < (block+1)*blockSize; i++ {
			if i > block*blockSize {
				out.WriteString(",")
			}
			fmt.Fprintf(&out, "n%d", full.Constraints[i].ID)
		}
		out.WriteString("]\n")
	}
	out.WriteString("\ndef allBlocks : Array (Array RawConstraint) := #[")
	for block := 0; block < blocks; block++ {
		if block > 0 {
			out.WriteString(",")
		}
		fmt.Fprintf(&out, "block%d", block)
	}
	out.WriteString("]\n\n")
	fmt.Fprintf(&out, "def constraintCount : Nat := %d\n\ndef constraintAt (index : Nat) : RawConstraint :=\n  ((allBlocks[index/128]?.getD #[])[index%%128]?.getD (.lookup [] []))\n\ndef FullConstraintsHold (tables : Tables) : Prop :=\n  ∀ index,index < constraintCount → (constraintAt index).Holds tables\n\n", len(full.Constraints))
	fmt.Fprintf(&out, "theorem block_sizes : allBlocks.map Array.size = #[")
	for block := 0; block < blocks; block++ {
		if block > 0 {
			out.WriteString(",")
		}
		size := blockSize
		if block == blocks-1 {
			size = len(full.Constraints) - block*blockSize
		}
		fmt.Fprintf(&out, "%d", size)
	}
	out.WriteString("] := by rfl\n\n")
	for _, selection := range []struct {
		name, reference string
		artifact        airdata.Artifact
	}{
		{"helpers", "Generated", helpers},
		{"extension", "Extension", mustExtension(full)},
	} {
		fmt.Fprintf(&out, "def %sIndices : List Nat := [", selection.name)
		for i, c := range selection.artifact.Constraints {
			if i > 0 {
				out.WriteString(",")
			}
			fmt.Fprintf(&out, "%d", c.ID)
		}
		out.WriteString("]\n\n")
		fmt.Fprintf(&out, "theorem %s_indices_bounded : ∀ index ∈ %sIndices,index < constraintCount := by decide\n\n", selection.name, selection.name)
		fmt.Fprintf(&out, "theorem %s_match : %sIndices.map constraintAt = DivRemFV.%s.NativeData.rawConstraints := by rfl\n\n", selection.name, selection.name, selection.reference)
		fmt.Fprintf(&out, "theorem %s_projection (tables : Tables) (accepted : FullConstraintsHold tables) :\n    ConstraintsHold tables DivRemFV.%s.constraints := by\n  apply (DivRemFV.%s.NativeData.native_constraints_iff tables).1\n  rw [← %s_match]\n  exact indexed_project_holds tables constraintAt constraintCount %sIndices %s_indices_bounded accepted\n\n", selection.name, selection.reference, selection.reference, selection.name, selection.name, selection.name)
	}
	out.WriteString("end DivRemFV.FullData\n")
	check(os.WriteFile("DivRemFV/FullData.lean", []byte(out.String()), 0644))
}

func mustExtension(full airdata.Artifact) airdata.Artifact {
	part, _, _, err := full.Slice([]string{"sgn_extension_u32_u64"})
	check(err)
	return part
}
