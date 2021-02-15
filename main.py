from dimacs_parser import *

def main():
    input = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
    formula, n_vars = dimacs_parse(input)
    print(formula, n_vars)

if __name__ == "__main__":
    main()