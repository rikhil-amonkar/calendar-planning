import json
from z3 import *

def main():
    # City indices
    cities = {
        'Reykjavik': 0,
        'Istanbul': 1,
        'Edinburgh': 2,
        'Oslo': 3,
        'Stuttgart': 4,
        'Bucharest': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    required_days = [5, 4, 5, 2, 3, 5]
    
    # Fixed constraints for Istanbul and Oslo
    istanbul_index = cities['Istanbul']
    oslo_index = cities['Oslo']
    fixed_s_istanbul = 5
    fixed_e_istanbul = 8
    fixed_s_oslo = 8
    fixed_e_oslo = 9
    
    # Direct flights (undirected)
    edges = [
        (0, 4), (4, 0),
        (1, 3), (3, 1),
        (5, 3), (3, 5),
        (1, 5), (5, 1),
        (4, 2), (2, 4),
        (1, 2), (2, 1),
        (3, 0), (0, 3),
        (1, 4), (4, 1),
        (3, 2), (2, 3)
    ]
    
    s = IntVector('s', 6)
    e = IntVector('e', 6)
    order = IntVector('order', 6)
    
    solver = Solver()
    
    # City order is a permutation of 0 to 5
    solver.add(Distinct(order))
    for i in range(6):
        solver.add(And(order[i] >= 0, order[i] <= 5))
    
    # Required days for each city
    for i in range(6):
        solver.add(e[i] - s[i] + 1 == required_days[i])
        solver.add(s[i] >= 1)
        solver.add(e[i] <= 19)
    
    # Fixed constraints for Istanbul and Oslo
    solver.add(s[istanbul_index] == fixed_s_istanbul)
    solver.add(e[istanbul_index] == fixed_e_istanbul)
    solver.add(s[oslo_index] == fixed_s_oslo)
    solver.add(e[oslo_index] == fixed_e_oslo)
    
    # Istanbul must be immediately followed by Oslo in the order
    consecutive_constraints = []
    for i in range(5):
        consecutive_constraints.append(And(order[i] == istanbul_index, order[i+1] == oslo_index))
    solver.add(Or(consecutive_constraints))
    
    # Sequence constraints
    solver.add(s[order[0]] == 1)
    solver.add(e[order[5]] == 19)
    for i in range(5):
        solver.add(e[order[i]] == s[order[i+1]])
        # Direct flight constraint
        edge_constraint = Or([And(order[i] == a, order[i+1] == b) for (a, b) in edges])
        solver.add(edge_constraint)
    
    if solver.check() == sat:
        model = solver.model()
        order_val = [model[order[i]].as_long() for i in range(6)]
        s_val = [model[s[i]].as_long() for i in range(6)]
        e_val = [model[e[i]].as_long() for i in range(6)]
        
        itinerary = []
        for city_index in order_val:
            start = s_val[city_index]
            end = e_val[city_index]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range,
                "place": city_names[city_index]
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()