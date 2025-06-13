from z3 import *

def main():
    n_days = 10
    cities = ["Mykonos", "Vienna", "Venice"]
    n_cities = len(cities)
    adj = [[1], [0, 2], [1]]  # Mykonos(0)-Vienna(1), Vienna(1)-Venice(2)
    
    s = Solver()
    in_city = [[Bool(f"in_{i}_{c}") for c in range(n_cities)] for i in range(n_days)]
    
    # Constraint 1: Each day is either one city or two adjacent cities
    for i in range(n_days):
        one_city = Or(
            And(in_city[i][0], Not(in_city[i][1]), Not(in_city[i][2])),
            And(in_city[i][1], Not(in_city[i][0]), Not(in_city[i][2])),
            And(in_city[i][2], Not(in_city[i][0]), Not(in_city[i][1]))
        )
        two_cities = Or(
            And(in_city[i][0], in_city[i][1], Not(in_city[i][2])),
            And(in_city[i][1], in_city[i][2], Not(in_city[i][0]))
        )
        s.add(Or(one_city, two_cities))
    
    # Constraint 2: Exactly two travel days (days in two adjacent cities)
    travel_days = []
    for i in range(n_days):
        is_travel = Or(
            And(in_city[i][0], in_city[i][1], Not(in_city[i][2])),
            And(in_city[i][1], in_city[i][2], Not(in_city[i][0]))
        )
        travel_days.append(If(is_travel, 1, 0))
    s.add(Sum(travel_days) == 2)
    
    # Constraint 3: Total days per city
    total_mykonos = Sum([If(in_city[i][0], 1, 0) for i in range(n_days)])
    total_vienna = Sum([If(in_city[i][1], 1, 0) for i in range(n_days)])
    total_venice = Sum([If(in_city[i][2], 1, 0) for i in range(n_days)])
    s.add(total_mykonos == 2)
    s.add(total_vienna == 4)
    s.add(total_venice == 6)
    
    # Constraint 4: Workshop in Venice between days 5-10 (indices 4-9) must be a full day
    s.add(Or([And(in_city[i][2], Not(in_city[i][0]), Not(in_city[i][1])) for i in range(4, 10)]))
    
    # Constraint 5: Connectivity for consecutive days
    for c in range(n_cities):
        for i in range(n_days - 1):
            # Leaving city c: if in c on day i but not on day i+1, then day i must include an adjacent city
            s.add(Implies(
                And(in_city[i][c], Not(in_city[i+1][c])),
                Or([in_city[i][d] for d in adj[c]])
            ))
            # Entering city c: if not in c on day i but in c on day i+1, then day i+1 must include an adjacent city
            s.add(Implies(
                And(Not(in_city[i][c]), in_city[i+1][c]),
                Or([in_city[i+1][d] for d in adj[c]])
            ))
    
    if s.check() == sat:
        m = s.model()
        for i in range(n_days):
            present = []
            for c in range(n_cities):
                if m.evaluate(in_city[i][c]):
                    present.append(cities[c])
            print(f"Day {i+1}: {', '.join(present)}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()