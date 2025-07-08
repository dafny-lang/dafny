from __future__ import print_function

import os
import sys
import subprocess

def in_color(green, text):
  return ("\x1B[01;32m" if green else "\x1B[01;31m") + text + "\x1B[0m"

def in_red(text):
  return in_color(False, text)

def in_green(text):
  return in_color(True, text)

def get_result(test):
  proc = subprocess.Popen(["./" + test], stdin=subprocess.PIPE,
      stdout=subprocess.PIPE)
  out, err = proc.communicate()
  ret = proc.wait()

  if ret != 0:
    return in_red("ERROR")

  with open(test + ".expect", "rb") as f:
    expected_out = f.read()

  if out != expected_out:
    return in_red("WRONG")
  return in_green("correct")

def run_test(test):
  print(test, " ... ", get_result(test))

def run_tests(tests):
  for test in tests:
    run_test(test)

if __name__ == "__main__":
  run_tests(sys.argv[1:])
