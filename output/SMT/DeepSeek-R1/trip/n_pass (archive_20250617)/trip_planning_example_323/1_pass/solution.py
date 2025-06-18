from z3 import *

def main():
    s = Solver()
    days = 16
    L = [Bool(f"L_{i}") for i in range(1, days+1)]
    O = [Bool(f"O_{i}") for i in range(1, days+1)]
    S = [Bool(f"S_{i}") for i in range(1, days+1)]
    P = [Bool(f"P_{i}") for i in range(1, days+1)]
    
    for i in range(days):
        s.add(Or(L[i], O[i], S[i], P[i]))
        total = Sum([If(L[i], 1, 0), If(O[i], 1, 0), If(S[i], 1, 0), If(P[i], 1, 0)])
        s.add(Or(total == 1, total == 2))
        s.add(Implies(total == 2, 
                     Or(And(L[i], O[i]), 
                        And(L[i], S[i]), 
                        And(O[i], S[i]), 
                        And(O[i], P[i]))))
    
    split_indices = [6, 7, 8, 9, 10]
    for i in split_indices:
        s.add(S[i] == True)
    
    non_split_indices = list(range(0, 6)) + list(range(11, days))
    for i in non_split_indices:
        s.add(S[i] == False)
    
    s.add(Sum([If(L[i], 1, 0) for i in range(days)]) == 7)
    s.add(Sum([If(O[i], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(P[i], 1, 0) for i in range(days)]) == 5)
    
    s.add(Or([L[i] for i in range(0, 7)]))
    
    s.add(Sum([If(L[6], 1, 0), If(O[6], 1, 0), If(S[6], 1, 0), If(P[6], 1, 0)]) == 2)
    s.add(Sum([If(L[10], 1, 0), If(O[10], 1, 0), If(S[10], 1, 0), If(P[10], 1, 0)]) == 2)
    
    if s.check() == sat:
        m = s.model()
        for i in range(days):
            cities = []
            if is_true(m.evaluate(L[i])):
                cities.append("London")
            if is_true(m.evaluate(O[i])):
                cities.append("Oslo")
            if is_true(m.evaluate(S[i])):
                cities.append("Split")
            if is_true(m.evaluate(P[i])):
                cities.append("Porto")
            print(f"Day {i+1}: {', '.join(cities)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()