#!/usr/bin/env bash
# The script does automatic checking on a Go package and its sub-packages.
set -ex

env GORACE="halt_on_error=1" go test -race -covermode atomic -coverprofile=profile.cov ./...

# Automatic checks
golangci-lint run --disable-all --deadline=10m \
--enable=gofmt \
--enable=gosimple \
--enable=unconvert \
--enable=ineffassign \
--enable=govet
