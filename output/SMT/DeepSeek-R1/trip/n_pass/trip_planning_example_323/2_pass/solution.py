from z3 import Solver, Bool, Or, And, Not, Implies, Sum, If, sat
import sys

def main():
    s = Solver()
    days = 16
    L = [Bool(f"L_{i}") for i in range(days)]
    O = [Bool(f"O_{i}") for i in range(days)]
    S = [Bool(f"S_{i}") for i in range(days)]
    P = [Bool(f"P_{i}") for i in range(days)]
    
    for i in range(days):
        s.add(Or(L[i], O[i], S[i], P[i]))
        total = Sum(If(L[i], 1, 0), If(O[i], 1, 0), If(S[i], 1, 0), If(P[i], 1, 0))
        s.add(Or(total == 1, total == 2))
        s.add(Not(And(L[i], P[i])))
        s.add(Not(And(S[i], P[i])))
    
    split_indices = [6, 7, 8, 9, 10]
    non_split_indices = list(range(0, 6)) + list(range(11, days))
    for i in split_indices:
        s.add(S[i] == True)
    for i in non_split_indices:
        s.add(S[i] == False)
    
    s.add(Sum([If(L[i], 1, 0) for i in range(days)]) == 7)
    s.add(Sum([If(O[i], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(P[i], 1, 0) for i in range(days)]) == 5)
    
    s.add(Or([L[i] for i in range(0, 7)]))
    
    total_day6 = Sum(If(L[6], 1, 0), If(O[6], 1, 0), If(S[6], 1, 0), If(P[6], 1, 0))
    s.add(total_day6 == 2)
    total_day10 = Sum(If(L[10], 1, 0), If(O[10], 1, 0), If(S[10], 1, 0), If(P[10], 1, 0))
    s.add(total_day10 == 2)
    
    if s.check() == sat:
        m = s.model()
        for i in range(days):
            cities = []
            if m.evaluate(L[i]):
                cities.append("London")
            if m.evaluate(O[i]):
                cities.append("Oslo")
            if m.evaluate(S[i]):
                cities.append("Split")
            if m.evaluate(P[i]):
                cities.append("Porto")
            print(f"Day {i+1}: {', '.join(cities)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()