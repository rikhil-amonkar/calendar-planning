from z3 import *
import json

def main():
    # City names and their durations
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    durations = [4, 3, 4, 5, 5, 2, 5, 4]
    # Indices for fixed cities
    idx_edinburgh = 2
    idx_split = 6
    
    # Direct flight edges (undirected)
    edges = [
        (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
        (1, 6), (1, 7),
        (2, 4), (2, 7),
        (3, 4), (3, 7),
        (4, 5), (4, 6),
        (5, 6), (5, 7),
        (6, 7)
    ]
    
    # Create Z3 solver and variables
    solver = Solver()
    order = [Int('order_%d' % i) for i in range(8)]
    s = [Int('s_%d' % i) for i in range(8)]
    
    # Constraints for order: each is between 0 and 7, and distinct
    solver.add(Distinct(order))
    for i in range(8):
        solver.add(order[i] >= 0, order[i] < 8)
    
    # Fixed start for Edinburgh
    solver.add(s[idx_edinburgh] == 5)
    
    # Split start between 15 and 21
    solver.add(s[idx_split] >= 15, s[idx_split] <= 21)
    
    # Chain constraints
    # First city starts at day 1
    solver.add(s[order[0]] == 1)
    # Last city ends at day 25
    solver.add(s[order[7]] + durations[order[7]] - 1 == 25)
    # Middle cities: start of next = end of current
    for i in range(1, 8):
        solver.add(s[order[i]] == s[order[i-1]] + durations[order[i-1]] - 1)
    
    # Graph constraints: consecutive cities must have a direct flight
    for i in range(7):
        a = order[i]
        b = order[i+1]
        edge_conds = []
        for (x, y) in edges:
            edge_conds.append(And(a == x, b == y))
            edge_conds.append(And(a == y, b == x))
        solver.add(Or(edge_conds))
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        # Extract start days for each city
        start_days = [model.evaluate(s[i]).as_long() for i in range(8)]
        # Generate itinerary
        itinerary = []
        for i in range(8):
            city = cities[i]
            start = start_days[i]
            end = start + durations[i] - 1
            for day in range(start, end + 1):
                itinerary.append({"day": day, "place": city})
        # Sort itinerary by day
        itinerary.sort(key=lambda x: x["day"])
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()