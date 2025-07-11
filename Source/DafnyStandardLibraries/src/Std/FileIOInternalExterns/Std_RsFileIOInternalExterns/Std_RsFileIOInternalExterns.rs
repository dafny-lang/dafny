/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

use dafny_runtime::*;
use std::fs;
use std::path::Path;

pub struct _default {}

impl _default {
    /// Attempts to read all bytes from the file at the given path
    pub fn INTERNAL__ReadBytesFromFile(
        path: &Sequence<DafnyCharUTF16>,
    ) -> (bool, Sequence<u8>, Sequence<DafnyCharUTF16>) {
        let path_str = dafny_runtime::string_of_dafny_string(path);
        
        match fs::read(&path_str) {
            Ok(bytes) => {
                let bytes_seq = Sequence::from_array_owned(bytes);
                (false, bytes_seq, Sequence::new())
            }
            Err(e) => {
                let error_msg = dafny_runtime::string_to_dafny_string(&e.to_string());
                (true, Sequence::new(), error_msg)
            }
        }
    }

    /// Attempts to write all given bytes to the file at the given path
    pub fn INTERNAL__WriteBytesToFile(
        path: &Sequence<DafnyCharUTF16>,
        bytes: &Sequence<u8>,
    ) -> (bool, Sequence<DafnyCharUTF16>) {
        let path_str = dafny_runtime::string_of_dafny_string(path);
        
        // Create parent directories if they don't exist
        if let Some(parent) = Path::new(&path_str).parent() {
            if let Err(e) = fs::create_dir_all(parent) {
                let error_msg = dafny_runtime::string_to_dafny_string(&e.to_string());
                return (true, error_msg);
            }
        }
        
        // Convert Sequence<u8> to Vec<u8>
        let bytes_vec: Vec<u8> = bytes.iter().collect();
        
        match fs::write(&path_str, bytes_vec) {
            Ok(()) => (false, Sequence::new()),
            Err(e) => {
                let error_msg = dafny_runtime::string_to_dafny_string(&e.to_string());
                (true, error_msg)
            }
        }
    }
}

// Dummy export for compatibility
pub struct Dummy__ {}
