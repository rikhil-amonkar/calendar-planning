import json
from z3 import *

def main():
    # Cities and their indices
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
    n = 7

    # Durations for each city (by index)
    dur = [5, 3, 3, 5, 3, 4, 5]

    # Allowed directed flights: list of tuples (u, v)
    allowed_edges = [
        (0, 1), (1, 0),  # Berlin-Split
        (0, 3), (3, 0),  # Berlin-Riga
        (0, 4), (4, 0),  # Berlin-Lisbon
        (0, 5), (5, 0),  # Berlin-Tallinn
        (1, 6), (6, 1),  # Split-Lyon
        (2, 3), (3, 2),  # Bucharest-Riga
        (2, 4), (4, 2),  # Bucharest-Lisbon
        (3, 4), (4, 3),  # Riga-Lisbon
        (6, 2), (2, 6),  # Lyon-Bucharest
        (6, 4), (4, 6),  # Lyon-Lisbon
        (3, 5)            # Riga->Tallinn
    ]

    # Create Z3 variables for the sequence: city0, city1, ... city6
    city_vars = [Int(f'city_{i}') for i in range(n)]

    s = Solver()

    # Each city must be between 0 and 6
    for i in range(n):
        s.add(And(city_vars[i] >= 0, city_vars[i] < n))

    # All cities distinct
    s.add(Distinct(city_vars))

    # First city must be Berlin (index 0)
    s.add(city_vars[0] == 0)

    # Flight constraints for consecutive cities
    for i in range(n - 1):
        constraints = []
        for u, v in allowed_edges:
            constraints.append(And(city_vars[i] == u, city_vars[i + 1] == v))
        s.add(Or(constraints))

    # Build start day expressions for each position in the sequence
    # For a city at position i, start_day = 1 + sum_{j=0}^{i-1} (dur[city_vars[j]] - 1)
    start_exprs = [None] * n
    for i in range(n):
        if i == 0:
            start_exprs[i] = 1
        else:
            terms = [dur[city_vars[j]] - 1 for j in range(i)]
            start_exprs[i] = 1 + Sum(terms) if terms else 1

    # Constraints for Lyon (index 6) and Bucharest (index 2)
    for i in range(n):
        s.add(Implies(city_vars[i] == 6, And(start_exprs[i] >= 3, start_exprs[i] <= 11)))
        s.add(Implies(city_vars[i] == 2, And(start_exprs[i] >= 11, start_exprs[i] <= 15)))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        seq = [model[city_vars[i]].as_long() for i in range(n)]
        
        # Compute start and end days for each city in the sequence
        start_days = []
        end_days = []
        cum = 0
        for i in range(n):
            if i == 0:
                start_day = 1
            else:
                start_day = 1 + cum
            duration = dur[seq[i]]
            end_day = start_day + duration - 1
            start_days.append(start_day)
            end_days.append(end_day)
            cum += (duration - 1)
        
        # Generate itinerary: for each day, list all cities visited
        itinerary_list = []
        for day in range(1, 23):  # Days 1 to 22
            for i in range(n):
                if start_days[i] <= day <= end_days[i]:
                    city_name = cities[seq[i]]
                    itinerary_list.append({"day": day, "city": city_name})
        
        # Output as JSON
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()