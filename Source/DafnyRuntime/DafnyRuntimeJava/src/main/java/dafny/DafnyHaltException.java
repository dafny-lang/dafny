// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

public class DafnyHaltException extends RuntimeException {

    public DafnyHaltException(String message) {
        super(message);
    }
}