package goose_test

import (
	"bytes"
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose"
)

// The package ID has already been rendered with LeanPkgId. A basename such as
// array must not acquire the renaming used for ordinary Go term identifiers.
func TestPackageIDWithShadowedBasename(t *testing.T) {
	const dir = "./testdata/examples/array"
	files, errs, err := goose.TranslatePackages(dir, dir, ".")
	if err != nil || len(files) != 1 || len(errs) != 1 || errs[0] != nil {
		t.Fatalf("translation failed: %v, %v", err, errs)
	}
	var output bytes.Buffer
	files[0].Write(&output)
	want := "(package.init pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.array)"
	if !strings.Contains(output.String(), want) {
		t.Fatalf("initializer does not use the declared package ID: missing %s", want)
	}
}
