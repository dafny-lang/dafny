#include "DafnyRuntime.h"

void print_true();

int main(int argc, char* argv[]) {
  (void)dafny_get_args(argc, argv);
  print_true();
  std::cout << std::endl;
  return 0;
}
