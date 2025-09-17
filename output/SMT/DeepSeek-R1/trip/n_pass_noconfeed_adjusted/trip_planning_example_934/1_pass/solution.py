from z3 import *
import json

def main():
    # City mapping
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    n_days = 17

    # Direct flights: list of pairs (city1, city2) by index
    direct_flights = [
        (0, 6), (1, 6), (0, 3), (1, 3), (2, 3), (6, 3), (1, 5), (3, 4), (5, 0), (1, 4), (1, 0), (0, 4), (2, 1)
    ]

    # Create a Z3 solver
    solver = Solver()

    # Array s for sleeping city each night (days 1 to 17)
    s = [Int('s_%d' % i) for i in range(n_days)]

    # Constraint: each s[i] is between 0 and 6
    for i in range(n_days):
        solver.add(And(s[i] >= 0, s[i] <= 6))

    # Constraint for direct flights between consecutive cities
    for i in range(1, n_days):
        cond = Implies(s[i] != s[i-1], 
                       Or([Or(And(s[i-1] == c1, s[i] == c2), And(s[i-1] == c2, s[i] == c1)) for (c1, c2) in direct_flights]))
        solver.add(cond)

    # Define in_city matrix: in_city[d][c] is True if city c is visited on day d (0-indexed)
    in_city = [[Bool('in_city_%d_%d' % (d, c)) for c in range(7)] for d in range(n_days)]

    # Constraints for in_city
    for d in range(n_days):
        if d == 0:
            for c in range(7):
                solver.add(in_city[d][c] == (s[0] == c))
        else:
            for c in range(7):
                solver.add(in_city[d][c] == Or(s[d] == c, And(s[d-1] != s[d], s[d-1] == c)))

    # Total days per city
    total_days = [Int('total_days_%d' % c) for c in range(7)]
    for c in range(7):
        solver.add(total_days[c] == Sum([If(in_city[d][c], 1, 0) for d in range(n_days)]))

    # Required total days per city
    solver.add(total_days[0] == 5)  # Brussels
    solver.add(total_days[1] == 2)  # Rome
    solver.add(total_days[2] == 3)  # Dubrovnik
    solver.add(total_days[3] == 5)  # Geneva
    solver.add(total_days[4] == 2)  # Budapest
    solver.add(total_days[5] == 4)  # Riga
    solver.add(total_days[6] == 2)  # Valencia

    # Specific day constraints
    # Brussels between day 7 and 11 (0-indexed days 6 to 10)
    for d in range(6, 11):
        solver.add(in_city[d][0] == True)
    
    # Budapest between day 16 and 17 (0-indexed days 15 and 16)
    for d in [15, 16]:
        solver.add(in_city[d][4] == True)
    
    # Riga between day 4 and 7 (0-indexed days 3 to 6)
    for d in range(3, 7):
        solver.add(in_city[d][5] == True)

    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        sleeping_cities = []
        for i in range(n_days):
            sleeping_cities.append(model.evaluate(s[i]).as_long())
        
        itinerary = []
        start = 0
        current_city = sleeping_cities[0]
        for i in range(1, n_days):
            if sleeping_cities[i] != current_city:
                day_range = f"Day {start+1}-{i}" if start+1 != i else f"Day {start+1}"
                itinerary.append({"day_range": day_range, "place": cities[current_city]})
                start = i
                current_city = sleeping_cities[i]
        day_range = f"Day {start+1}-{n_days}" if start+1 != n_days else f"Day {start+1}"
        itinerary.append({"day_range": day_range, "place": cities[current_city]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()