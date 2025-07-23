from z3 import *
import json

def main():
    city_names = ["Bucharest", "Tallinn", "Seville", "Stockholm", "Munich", "Milan"]
    n_days = 18
    n_cities = len(city_names)
    
    # Create Z3 variables: c[d][i] is True if in city i on day d (0-indexed)
    c = [[Bool(f"c_{d}_{i}") for i in range(n_cities)] for d in range(n_days)]
    
    # Define the direct flight edges (undirected, stored with i < j)
    edges = set()
    edges.add((0, 4))  # Bucharest-Munich
    edges.add((1, 3))  # Tallinn-Stockholm
    edges.add((1, 4))  # Tallinn-Munich
    edges.add((2, 4))  # Seville-Munich
    edges.add((2, 5))  # Seville-Milan
    edges.add((3, 4))  # Stockholm-Munich
    edges.add((3, 5))  # Stockholm-Milan
    edges.add((4, 5))  # Munich-Milan
    
    solver = Solver()
    
    # Constraint 1: Each day, traveler is in at least one and at most two cities
    for d in range(n_days):
        in_cities = [c[d][i] for i in range(n_cities)]
        total = Sum([If(in_cities[i], 1, 0) for i in range(n_cities)])
        solver.add(total >= 1, total <= 2)
    
    # Constraint 2: Total days per city
    req_days = [4, 2, 5, 5, 5, 2]  # Bucharest, Tallinn, Seville, Stockholm, Munich, Milan
    for i in range(n_cities):
        total = Sum([If(c[d][i], 1, 0) for d in range(n_days)])
        solver.add(total == req_days[i])
    
    # Constraint 3: If two cities on the same day, they must have a direct flight
    for d in range(n_days):
        for i in range(n_cities):
            for j in range(i+1, n_cities):
                if (i, j) not in edges and (j, i) not in edges:
                    # If not connected, cannot be both true on the same day
                    solver.add(Not(And(c[d][i], c[d][j])))
    
    # Constraint 4: Consecutive days must share at least one city
    for d in range(n_days - 1):
        solver.add(Or([And(c[d][i], c[d+1][i]) for i in range(n_cities)]))
    
    # Constraint 5: Event constraints
    # Bucharest must be on all days 0 to 3 (actual days 1-4)
    for d in range(4):  # days 0,1,2,3 (indexed) -> actual days 1,2,3,4
        solver.add(c[d][0])
    # Munich: at least one day in [3,7] (actual days 4-8)
    solver.add(Or([c[d][4] for d in range(3, 8)]))  # indices 3,4,5,6,7 -> actual days 4,5,6,7,8
    # Seville: at least one day in [7,11] (actual days 8-12)
    solver.add(Or([c[d][2] for d in range(7, 12)]))  # indices 7,8,9,10,11 -> actual days 8,9,10,11,12
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(n_days):
            actual_day = d + 1
            places = []
            for i in range(n_cities):
                if model.evaluate(c[d][i]):
                    places.append(city_names[i])
            itinerary.append({"day": actual_day, "place": places})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()