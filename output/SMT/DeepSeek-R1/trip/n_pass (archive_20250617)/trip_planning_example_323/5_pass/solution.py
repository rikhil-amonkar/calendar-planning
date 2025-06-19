from z3 import Solver, Bool, Or, And, Not, Implies, Sum, If, sat

def main():
    s = Solver()
    days = 16
    cities = ['London', 'Oslo', 'Split', 'Porto']
    L = [Bool(f"L_{i}") for i in range(days)]
    O = [Bool(f"O_{i}") for i in range(days)]
    S = [Bool(f"S_{i}") for i in range(days)]
    P = [Bool(f"P_{i}") for i in range(days)]
    city_vars = {'London': L, 'Oslo': O, 'Split': S, 'Porto': P}
    
    for i in range(days):
        s.add(Or(L[i], O[i], S[i], P[i]))
        total = Sum(If(L[i], 1, 0), If(O[i], 1, 0), If(S[i], 1, 0), If(P[i], 1, 0))
        s.add(Or(total == 1, total == 2))
        s.add(Implies(total == 2, Or(
            And(L[i], O[i]),
            And(L[i], S[i]),
            And(O[i], S[i]),
            And(O[i], P[i])
        )))
    
    split_indices = [6, 7, 8, 9, 10]
    non_split_indices = list(range(0, 6)) + list(range(11, days))
    for i in split_indices:
        s.add(S[i])
    for i in non_split_indices:
        s.add(Not(S[i]))
    
    s.add(Sum([If(L[i], 1, 0) for i in range(days)]) == 7)
    s.add(Sum([If(O[i], 1, 0) for i in range(days)]) == 2)
    s.add(Sum([If(P[i], 1, 0) for i in range(days)]) == 5)
    
    s.add(Or([L[i] for i in range(0, 7)]))
    
    total_day6 = Sum(If(L[6], 1, 0), If(O[6], 1, 0), If(S[6], 1, 0), If(P[6], 1, 0))
    s.add(total_day6 == 2)
    total_day10 = Sum(If(L[10], 1, 0), If(O[10], 1, 0), If(S[10], 1, 0), If(P[10], 1, 0))
    s.add(total_day10 == 2)
    
    adj_list = {
        'London': ['Oslo', 'Split'],
        'Oslo': ['London', 'Split', 'Porto'],
        'Split': ['London', 'Oslo'],
        'Porto': ['Oslo']
    }
    
    allowed_pairs_set = set()
    edges = [('London', 'Oslo'), ('London', 'Split'), ('Oslo', 'Split'), ('Oslo', 'Porto')]
    for (a, b) in edges:
        allowed_pairs_set.add((a, b))
        allowed_pairs_set.add((b, a))
    
    for i in range(days - 1):
        for city in cities:
            next_day_present = city_vars[city][i+1]
            prev_day_options = [city_vars[city][i]]
            for adj_city in adj_list[city]:
                prev_day_options.append(city_vars[adj_city][i])
            s.add(Implies(next_day_present, Or(prev_day_options)))
    
    for i in range(days - 1):
        for (A, B) in allowed_pairs_set:
            s.add(Implies(
                And(city_vars[A][i], Not(city_vars[B][i]), 
                city_vars[B][i+1], Not(city_vars[A][i+1])),
                Or(
                    And(city_vars[A][i], city_vars[B][i]),
                    And(city_vars[A][i+1], city_vars[B][i+1])
                )
            ))
    
    if s.check() == sat:
        m = s.model()
        for i in range(days):
            present_cities = []
            if m.evaluate(L[i]):
                present_cities.append("London")
            if m.evaluate(O[i]):
                present_cities.append("Oslo")
            if m.evaluate(S[i]):
                present_cities.append("Split")
            if m.evaluate(P[i]):
                present_cities.append("Porto")
            print(f"Day {i+1}: {', '.join(present_cities)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()