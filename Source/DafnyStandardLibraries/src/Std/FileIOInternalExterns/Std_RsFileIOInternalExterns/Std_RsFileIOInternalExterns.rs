/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

use dafny_runtime::*;
use dafny_runtime::dafny_runtime_conversions::unicode_chars_true::dafny_string_to_string;
use std::fs;
use std::path::Path;

pub struct _default {}

impl _default {
    /// Attempts to read all bytes from the file at the given path
    pub fn _INTERNAL_ReadBytesFromFile(
        path: &DafnyString,
    ) -> (bool, Sequence<u8>, DafnyString) {
        let path_str = dafny_string_to_string(path);
        
        match fs::read(&path_str) {
            Ok(bytes) => {
                let bytes_seq: Sequence<u8> = bytes.into_iter().collect();
                (false, bytes_seq, string_of(""))
            }
            Err(e) => {
                let error_msg = string_of(&e.to_string());
                let empty_seq: Sequence<u8> = vec![].into_iter().collect();
                (true, empty_seq, error_msg)
            }
        }
    }

    /// Attempts to write all given bytes to the file at the given path
    pub fn _INTERNAL_WriteBytesToFile(
        path: &DafnyString,
        bytes: &Sequence<u8>,
    ) -> (bool, DafnyString) {
        let path_str = dafny_string_to_string(path);
        
        // Create parent directories if they don't exist
        if let Some(parent) = Path::new(&path_str).parent() {
            if let Err(e) = fs::create_dir_all(parent) {
                let error_msg = string_of(&e.to_string());
                return (true, error_msg);
            }
        }
        
        // Convert Sequence<u8> to Vec<u8>
        let bytes_vec: Vec<u8> = bytes.iter().collect();
        
        match fs::write(&path_str, bytes_vec) {
            Ok(()) => (false, string_of("")),
            Err(e) => {
                let error_msg = string_of(&e.to_string());
                (true, error_msg)
            }
        }
    }
}

// Dummy export for compatibility
pub struct Dummy__ {}
