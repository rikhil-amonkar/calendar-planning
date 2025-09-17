import json
from z3 import *

def main():
    # City indices
    cities = {
        0: "Reykjavik",
        1: "Riga",
        2: "Oslo",
        3: "Lyon",
        4: "Dubrovnik",
        5: "Madrid",
        6: "Warsaw",
        7: "London"
    }
    
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]
    
    # Direct flights graph (undirected)
    graph = {
        0: [2, 5, 6, 7],  # Reykjavik
        1: [2, 6],         # Riga
        2: [0, 1, 3, 4, 5, 6, 7],  # Oslo
        3: [2, 5, 7],      # Lyon
        4: [2, 5],         # Dubrovnik
        5: [0, 2, 3, 4, 6, 7],  # Madrid
        6: [0, 1, 2, 5, 7],  # Warsaw
        7: [0, 2, 3, 5, 6]   # London
    }
    
    allowed_edges = []
    for u, neighbors in graph.items():
        for v in neighbors:
            allowed_edges.append((u, v))
            allowed_edges.append((v, u))
    
    s = Solver()
    
    # Start and end days for each city
    start = [Int(f'start_{i}') for i in range(8)]
    end = [Int(f'end_{i}') for i in range(8)]
    
    # Order of visit (permutation)
    order = [Int(f'order_{i}') for i in range(8)]
    
    # Constraints for order: distinct and within 0-7
    s.add(Distinct(order))
    for i in range(8):
        s.add(And(order[i] >= 0, order[i] <= 7))
    
    # Constraints for start and end days
    for i in range(8):
        s.add(start[i] >= 1)
        s.add(end[i] <= 18)
        s.add(start[i] <= end[i])
        s.add(end[i] - start[i] + 1 == required_days[i])
    
    # First city starts at day 1, last city ends at day 18 using element constraints
    first_city = order[0]
    last_city = order[7]
    for i in range(8):
        s.add(If(first_city == i, start[i] == 1, True))
        s.add(If(last_city == i, end[i] == 18, True))
    
    # Consecutive cities share travel day using element constraints
    for seq in range(7):
        current_city = order[seq]
        next_city = order[seq+1]
        for i in range(8):
            for j in range(8):
                s.add(If(And(current_city == i, next_city == j), end[i] == start[j], True))
    
    # Flight connections between consecutive cities
    for seq in range(7):
        current_city = order[seq]
        next_city = order[seq+1]
        edge_constraints = []
        for (u, v) in allowed_edges:
            edge_constraints.append(And(current_city == u, next_city == v))
        s.add(Or(edge_constraints))
    
    # Additional constraints
    # Riga must include day 4 or 5
    s.add(Or(And(start[1] <= 4, end[1] >= 4), And(start[1] <= 5, end[1] >= 5)))
    # Dubrovnik must include day 7 or 8
    s.add(Or(And(start[4] <= 7, end[4] >= 7), And(start[4] <= 8, end[4] >= 8)))
    
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(8)]
        start_val = [model.evaluate(start[i]).as_long() for i in range(8)]
        end_val = [model.evaluate(end[i]).as_long() for i in range(8)]
        
        # Sort cities by visit order
        visit_sequence = sorted(range(8), key=lambda i: order_val.index(i))
        
        itinerary = []
        for idx in visit_sequence:
            city_name = cities[idx]
            day_start = start_val[idx]
            day_end = end_val[idx]
            if day_start == day_end:
                day_range = f"Day {day_start}"
            else:
                day_range = f"Day {day_start}-{day_end}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()