// RUN: %exits-with 4 %verify '--log-format:csv;log.csv' "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
