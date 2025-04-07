#!/usr/bin/env bash
# The script does automatic checking on a Go package and its sub-packages.
set -ex

env GORACE="halt_on_error=1" go test -race ./...

# Automatic checks
golangci-lint run --disable-all \
--enable=gofmt \
--enable=gosimple \
--enable=unconvert \
--enable=ineffassign \
--enable=govet
