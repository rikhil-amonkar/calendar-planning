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
                    solver.add(Not(And(c[d][i], c[d][j])))
    
    # Constraint 4: Consecutive days must share at least one city
    for d in range(n_days - 1):
        solver.add(Or([And(c[d][i], c[d+1][i]) for i in range(n_cities)]))
    
    # Constraint 5: Event constraints
    # Bucharest must be on all days 0 to 3 (actual days 1-4)
    for d in range(4):
        solver.add(c[d][0])
    # Munich: at least one day in [3,7] (actual days 4-8)
    solver.add(Or([c[d][4] for d in range(3, 8)]))
    # Seville: at least one day in [7,11] (actual days 8-12)
    solver.add(Or([c[d][2] for d in range(7, 12)]))
    
    # Constraint 6: Each city must be visited in one contiguous block
    for i in range(n_cities):
        for d1 in range(n_days):
            for d2 in range(d1+2, n_days):
                # If city i is on d1 and d2, must also be on all days between
                solver.add(Implies(And(c[d1][i], c[d2][i]), And([c[d][i] for d in range(d1+1, d2)])))
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        city_blocks = []
        for i in range(n_cities):
            present_days = []
            for d in range(n_days):
                if model.evaluate(c[d][i]):
                    present_days.append(d)
            if not present_days:
                continue
            start_day = min(present_days)
            end_day = max(present_days)
            day_range = f"Day {start_day+1}-{end_day+1}"
            city_blocks.append({'start': start_day, 'day_range': day_range, 'place': city_names[i]})
        
        # Sort blocks by start day
        city_blocks.sort(key=lambda x: x['start'])
        itinerary = [{'day_range': block['day_range'], 'place': block['place']} for block in city_blocks]
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()