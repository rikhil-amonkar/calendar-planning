import json
from z3 import *

def main():
    # Cities and their required stay durations
    city_names = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    L = [4, 3, 4, 5, 5, 2, 5, 4]  # days for each city in the order of city_names

    # Build the set of allowed flight connections (as unordered pairs of indices)
    edges_by_index = [
        (3,4), (4,6), (4,0), (7,5), (2,7), (5,6), (7,0), (0,5), (7,6), (0,1), (4,2), (6,1), (4,5), (7,1), (3,0), (7,3), (0,6)
    ]
    allowed_edges_set = set()
    for (u, v) in edges_by_index:
        a, b = min(u, v), max(u, v)
        allowed_edges_set.add((a, b))

    # Create Z3 solver and variables
    s = Solver()
    order = [Int(f'o_{i}') for i in range(8)]
    start = [Int(f'start_{i}') for i in range(8)]
    end = [Int(f'end_{i}') for i in range(8)]

    # Constraints: each order variable is between 0 and 7 and all are distinct
    s.add([And(order[i] >= 0, order[i] < 8) for i in range(8)])
    s.add(Distinct(order))

    # Start and end day constraints
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + L[order[0]] - 1)
    for i in range(1, 8):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + L[order[i]] - 1)
    s.add(end[7] == 25)  # total days must be 25

    # Fixed events: Edinburgh (index 2) must be from day 5 to 8, Split (index 6) from day 19 to 23
    s.add(Or([And(order[i] == 2, start[i] == 5, end[i] == 8) for i in range(8)]))
    s.add(Or([And(order[i] == 6, start[i] == 19, end[i] == 23) for i in range(8)]))

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        u = order[i]
        v = order[i+1]
        a = If(u < v, u, v)
        b = If(u < v, v, u)
        # Create disjunction over all allowed edges
        edge_constraints = []
        for edge in allowed_edges_set:
            edge_constraints.append(And(a == edge[0], b == edge[1]))
        s.add(Or(edge_constraints))

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(8)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(8)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(8)]
        
        # Helper function to format day ranges
        def format_day_range(s, e):
            if s == e:
                return f"Day {s}"
            else:
                return f"Day {s}-{e}"
        
        # Build itinerary
        itinerary_list = []
        for i in range(8):
            s_i = start_val[i]
            e_i = end_val[i]
            city = city_names[order_val[i]]
            itinerary_list.append({"day_range": format_day_range(s_i, e_i), "place": city})
            if i < 7:
                # Travel day: same day for departure and arrival
                next_city = city_names[order_val[i+1]]
                itinerary_list.append({"day_range": f"Day {e_i}", "place": city})
                itinerary_list.append({"day_range": f"Day {e_i}", "place": next_city})
        
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()