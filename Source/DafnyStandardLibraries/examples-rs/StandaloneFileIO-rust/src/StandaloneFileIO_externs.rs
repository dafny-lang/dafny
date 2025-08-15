/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

use dafny_runtime::*;
use dafny_runtime::dafny_runtime_conversions::unicode_chars_true::*;
use std::fs;

pub struct _default {}

impl _default {
    pub fn ReadBytesFromFile(
        path: &Sequence<DafnyChar>,
    ) -> Rc<crate::StandaloneFileIO::Result<Sequence<u8>, Sequence<DafnyChar>>> {
        let path_str = dafny_string_to_string(path);
        
        match fs::read(&path_str) {
            Ok(bytes) => {
                let bytes_seq = Sequence::from_array_owned(bytes);
                Rc::new(crate::StandaloneFileIO::Result::Success {
                    value: bytes_seq
                })
            }
            Err(e) => {
                let error_msg = string_to_dafny_string(&e.to_string());
                Rc::new(crate::StandaloneFileIO::Result::Failure {
                    error: error_msg
                })
            }
        }
    }
}
