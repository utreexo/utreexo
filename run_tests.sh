#!/usr/bin/env bash
# The script does automatic checking on a Go package and its sub-packages.
set -ex

env GORACE="halt_on_error=1" go test -race ./...

# Compile the build-tag variants the host test run above does not. go test
# only builds the files matching the host (linux/amd64), so a missing method
# or type in a platform-specific file stays hidden until a downstream build.
# go vet compiles both source and test files for each target without running
# them, covering:
#   windows/amd64: the !unix fallback (swisstable_fallback.go)
#   darwin/amd64:  the unix && !linux mmap path (mmap_other.go)
#   linux/arm64:   the unix && !amd64 generic path (swisstable_generic.go)
# CGO_ENABLED=0 keeps the check from needing a C cross-compiler for each
# target, matching how the release builds compile this module.
for platform in windows/amd64 darwin/amd64 linux/arm64; do
	env CGO_ENABLED=0 GOOS="${platform%/*}" GOARCH="${platform#*/}" go vet ./...
done

# Automatic checks
# Linters (staticcheck includes gosimple checks)
golangci-lint run --enable-only=staticcheck,unconvert,ineffassign,govet

# Formatter check
golangci-lint fmt --diff -E gofmt
