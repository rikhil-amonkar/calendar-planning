import json
from z3 import *

def main():
    cities = ["Reykjavik", "Stockholm", "Tallinn", "Oslo", "Split", "Geneva", "Porto", "Stuttgart"]
    durations = [2, 3, 5, 5, 3, 2, 3, 5]

    # Define direct flights (bidirectional connections)
    graph_edges = [
        (0, 1), (0, 2), (0, 3), (0, 7),
        (1, 0), (1, 3), (1, 4), (1, 5), (1, 7),
        (2, 0), (2, 3),
        (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6),
        (4, 1), (4, 3), (4, 5), (4, 7),
        (5, 1), (5, 3), (5, 4), (5, 6),
        (6, 3), (6, 5), (6, 7),
        (7, 0), (7, 1), (7, 4), (7, 6)
    ]
    allowed_edges = set(graph_edges)

    s = Solver()

    # City order variables
    order = [Int('order_%d' % i) for i in range(8)]
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    # Fixed start and end cities
    s.add(order[0] == 0)  # Start with Reykjavik
    s.add(order[7] == 6)  # End with Porto

    # Flight connection constraints
    for i in range(7):
        cons = []
        for u, v in allowed_edges:
            cons.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(cons))

    # Improved duration function using loop
    def get_duration(city_var):
        d = durations[7]  # Base case (Porto)
        # Check cities in reverse order (6 down to 0)
        for i in range(6, -1, -1):
            d = If(city_var == i, durations[i], d)
        return d

    # Timeline variables
    s_arr = [Int('s_arr_%d' % i) for i in range(8)]
    e_arr = [Int('e_arr_%d' % i) for i in range(8)]
    
    # First city (Reykjavik) constraints
    s.add(s_arr[0] == 1)
    s.add(e_arr[0] == s_arr[0] + get_duration(order[0]) - 1)
    
    # Subsequent cities start where previous ended
    for i in range(1, 8):
        s.add(s_arr[i] == e_arr[i-1])
        s.add(e_arr[i] == s_arr[i] + get_duration(order[i]) - 1)
    
    # Global constraints
    s.add(e_arr[7] == 21)  # Trip ends day 21
    s.add(s_arr[7] == 19)  # Porto starts day 19
    
    # Stockholm meeting must overlap days 2-4
    stockholm_constraints = []
    for i in range(8):
        # Stay must cover at least one day between 2-4
        stockholm_constraints.append(And(
            order[i] == 1, 
            s_arr[i] <= 4, 
            e_arr[i] >= 2
        ))
    s.add(Or(stockholm_constraints))

    # Solve and output itinerary
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(8)]
        s_vals = [model.evaluate(s_arr[i]).as_long() for i in range(8)]
        e_vals = [model.evaluate(e_arr[i]).as_long() for i in range(8)]
        
        itinerary = []
        for day in range(1, 22):
            cities_today = []
            for pos in range(8):
                if s_vals[pos] <= day <= e_vals[pos]:
                    cities_today.append((pos, cities[order_vals[pos]]))
            # Sort by visit order
            cities_today.sort(key=lambda x: x[0])
            place_str = ", ".join(city for (_, city) in cities_today)
            itinerary.append({"day": day, "place": place_str})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()