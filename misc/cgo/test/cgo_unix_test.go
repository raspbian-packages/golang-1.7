// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build !windows

package cgotest

import "testing"

func TestSigaltstack(t *testing.T) { testSigaltstack(t) }
func TestSigprocmask(t *testing.T) { testSigprocmask(t) }
