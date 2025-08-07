from z3 import *
import json

def main():
    cities = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
    durations = [4, 5, 2, 2, 3, 2, 5, 2]
    
    bidirectional_pairs = [
        (0, 6),  # Mykonos-Madrid
        (5, 1),  # Oslo-Krakow
        (5, 7),  # Oslo-Paris
        (7, 6),  # Paris-Madrid
        (3, 2),  # Helsinki-Vilnius
        (5, 6),  # Oslo-Madrid
        (5, 3),  # Oslo-Helsinki
        (3, 1),  # Helsinki-Krakow
        (4, 3),  # Dubrovnik-Helsinki
        (4, 6),  # Dubrovnik-Madrid
        (5, 4),  # Oslo-Dubrovnik
        (1, 7),  # Krakow-Paris
        (5, 2),  # Oslo-Vilnius
        (3, 7),  # Helsinki-Paris
        (2, 7),  # Vilnius-Paris
        (3, 6)   # Helsinki-Madrid
    ]
    allowed_edges = set()
    for (u, v) in bidirectional_pairs:
        allowed_edges.add((u, v))
        allowed_edges.add((v, u))
    
    s = Solver()
    order = [Int(f'order_{i}') for i in range(8)]
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    # Create a Z3 array for durations
    durations_arr = Array('durations_arr', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(durations_arr[i] == d)
    
    starts = [Int(f'starts_{i}') for i in range(8)]
    s.add(starts[0] == 1)
    for i in range(1, 8):
        prev_city = order[i-1]
        s.add(starts[i] == starts[i-1] + Select(durations_arr, prev_city) - 1)
    
    # Fixed start day constraints using Z3 conditions
    for i in range(8):
        s.add(If(order[i] == 5, starts[i] == 1, True))  # Oslo starts on day 1
    for i in range(8):
        s.add(If(order[i] == 4, starts[i] == 2, True))  # Dubrovnik starts on day 2
    for i in range(8):
        s.add(If(order[i] == 0, starts[i] == 15, True))  # Mykonos starts on day 15
    
    # Flight constraints between consecutive cities
    for i in range(7):
        u = order[i]
        v = order[i+1]
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(And(u == edge[0], v == edge[1]))
        s.add(Or(edge_constraints))
    
    # Total trip ends on day 18
    s.add(starts[7] + Select(durations_arr, order[7]) - 1 == 18)
    
    if s.check() == sat:
        model = s.model()
        order_sol = [model.evaluate(order[i]).as_long() for i in range(8)]
        starts_sol = [model.evaluate(starts[i]).as_long() for i in range(8)]
        
        itinerary_list = []
        for i in range(8):
            city_index = order_sol[i]
            city_name = cities[city_index]
            start_day = starts_sol[i]
            duration = durations[city_index]
            for day in range(start_day, start_day + duration):
                itinerary_list.append({"day": day, "city": city_name})
        
        sorted_itinerary = sorted(itinerary_list, key=lambda x: x['day'])
        result = {'itinerary': sorted_itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()