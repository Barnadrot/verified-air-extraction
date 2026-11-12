package main

import (
	"bytes"
	"divremfv/internal/airdata"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
)

var reificationScope = "Generated"

func writeScoped(name, source string) {
	source = strings.ReplaceAll(source, "DivRemFV.Generated", "DivRemFV."+reificationScope)
	if reificationScope == "Instruction" {
		source = strings.Replace(source, "import DivRemFV.RowSemantics", "import DivRemFV.Instruction.Ranges", 1)
	}
	directory := filepath.Join("DivRemFV", reificationScope)
	check(os.MkdirAll(directory, 0755))
	path := filepath.Join(directory, name+".lean")
	previous, err := os.ReadFile(path)
	if err == nil && bytes.Equal(previous, []byte(source)) {
		return
	}
	check(os.WriteFile(path, []byte(source), 0644))
}

func writeSignExtension() {
	data, err := os.ReadFile("artifacts/air.json")
	check(err)
	var full airdata.Artifact
	check(json.Unmarshal(data, &full))
	part, _, _, err := full.Slice([]string{"sgn_extension_u32_u64"})
	check(err)
	data, err = json.MarshalIndent(part, "", "  ")
	check(err)
	check(os.WriteFile("artifacts/sign-extension-air.json", append(data, '\n'), 0644))
	old := reificationScope
	reificationScope = "Extension"
	defer func() { reificationScope = old }()
	writeArtifact(part)
	writeIntegerRows(part)
	writeConstruction(part)
	writeBoundsMap(part)
	writeReverseRows(part)
	writeNativeData(part)
}
