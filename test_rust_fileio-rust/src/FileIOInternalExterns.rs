/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

use dafny_runtime::*;
use dafny_runtime::dafny_runtime_conversions::unicode_chars_true::*;
use std::fs;

pub struct _default {}

impl _default {
    pub fn _INTERNAL_ReadBytesFromFile(
        path: &Sequence<DafnyChar>,
    ) -> (bool, Sequence<u8>, Sequence<DafnyChar>) {
        let path_str = dafny_string_to_string(path);
        
        match fs::read(&path_str) {
            Ok(bytes) => {
                let bytes_seq = Sequence::from_array_owned(bytes);
                (false, bytes_seq, Sequence::from_array_owned(vec![]))
            }
            Err(e) => {
                let error_msg = string_to_dafny_string(&e.to_string());
                (true, Sequence::from_array_owned(vec![]), error_msg)
            }
        }
    }

    pub fn _INTERNAL_WriteBytesToFile(
        path: &Sequence<DafnyChar>,
        bytes: &Sequence<u8>,
    ) -> (bool, Sequence<DafnyChar>) {
        let path_str = dafny_string_to_string(path);
        let bytes_vec = bytes.to_array();
        
        match fs::write(&path_str, &*bytes_vec) {
            Ok(()) => {
                (false, Sequence::from_array_owned(vec![]))
            }
            Err(e) => {
                let error_msg = string_to_dafny_string(&e.to_string());
                (true, error_msg)
            }
        }
    }
}