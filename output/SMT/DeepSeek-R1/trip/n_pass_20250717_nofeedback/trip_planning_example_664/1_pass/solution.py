from z3 import *

def main():
    # City names and their indices
    city_names = ["Bucharest", "Tallinn", "Seville", "Stockholm", "Munich", "Milan"]
    n_days = 18
    n_cities = 6

    # Create Z3 variables: c[d][i] is True if in city i on day d
    c = [[Bool(f"c_{d}_{i}") for i in range(n_cities)] for d in range(1, n_days+1)]
    
    # Define the direct flight edges (undirected, stored with i < j)
    edges = set()
    edges.add((0, 4))  # Bucharest - Munich
    edges.add((1, 3))  # Tallinn - Stockholm
    edges.add((1, 4))  # Tallinn - Munich
    edges.add((2, 4))  # Seville - Munich
    edges.add((2, 5))  # Seville - Milan
    edges.add((3, 4))  # Stockholm - Munich
    edges.add((3, 5))  # Stockholm - Milan
    edges.add((4, 5))  # Munich - Milan

    solver = Solver()

    # Constraint 1: Each day, the traveler is in exactly 1 or 2 cities
    for d in range(n_days):
        day_vars = c[d]
        total = Sum([If(day_vars[i], 1, 0) for i in range(n_cities)])
        solver.add(total >= 1, total <= 2)

    # Constraint 2: Total days per city
    req_durations = [4, 2, 5, 5, 5, 2]  # Bucharest, Tallinn, Seville, Stockholm, Munich, Milan
    for i in range(n_cities):
        total_days = Sum([If(c[d][i], 1, 0) for d in range(n_days)])
        solver.add(total_days == req_durations[i])

    # Constraint 3: If in two cities on the same day, they must be connected by a direct flight
    for d in range(n_days):
        for i in range(n_cities):
            for j in range(i+1, n_cities):
                if (i, j) not in edges and (j, i) not in edges:
                    solver.add(Not(And(c[d][i], c[d][j])))

    # Constraint 4: Consecutive days must share at least one city
    for d in range(n_days - 1):
        solver.add(Or([And(c[d][i], c[d+1][i]) for i in range(n_cities)]))

    # Constraint 5: Event constraints
    # Bucharest must be visited on days 1-4
    for d in [0, 1, 2, 3]:  # Days 1,2,3,4 (0-indexed: days 0 to 3)
        solver.add(c[d][0])
    # Munich: at least one day between days 4 and 8 (inclusive)
    solver.add(Or([c[d][4] for d in range(4, 8)]))  # Days 5 to 9 (0-indexed: 4 to 7)
    # Seville: at least one day between days 8 and 12 (inclusive)
    solver.add(Or([c[d][2] for d in range(8, 12)]))  # Days 9 to 13 (0-indexed: 8 to 11)

    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(n_days):
            actual_day = d + 1
            places = []
            for i in range(n_cities):
                if model.evaluate(c[d][i]) == True:
                    places.append(city_names[i])
            itinerary.append({"day": actual_day, "place": places})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()