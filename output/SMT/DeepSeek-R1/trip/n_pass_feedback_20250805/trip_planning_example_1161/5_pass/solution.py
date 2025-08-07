from z3 import *
import json

def main():
    cities = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
    durations = [4, 5, 2, 2, 3, 2, 5, 2]
    
    bidirectional_pairs = [
        (0, 6), (5, 1), (5, 7), (7, 6), (3, 2), (5, 6), (5, 3), (3, 1),
        (4, 3), (4, 6), (5, 4), (1, 7), (5, 2), (3, 7), (2, 7), (3, 6)
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
    
    durations_arr = Array('durations_arr', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(durations_arr[i] == d)
    
    starts = [Int(f'starts_{i}') for i in range(8)]
    s.add(starts[0] == 1)
    for i in range(1, 8):
        prev_city = order[i-1]
        s.add(starts[i] == starts[i-1] + Select(durations_arr, prev_city) - 1)
    
    s.add(Or([order[0] == idx for idx in [5]]))
    s.add(Or([order[1] == idx for idx in [4]]))
    s.add(Or([order[7] == idx for idx in [0]]))
    s.add(Or([starts[0] == 1, True]))
    s.add(Or([starts[1] == 2, True]))
    s.add(Or([starts[7] == 15, True]))
    s.add(Or([starts[0] == 1, True]))
    s.add(Or([starts[1] == 2, True]))
    s.add(Or([starts[7] == 15, True]))
    
    for i in range(7):
        u = order[i]
        v = order[i+1]
        edge_constraints = []
        for edge in allowed_edges:
            edge_constraints.append(And(u == edge[0], v == edge[1]))
        s.add(Or(edge_constraints))
    
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