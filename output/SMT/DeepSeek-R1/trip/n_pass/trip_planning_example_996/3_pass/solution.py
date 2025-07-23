from z3 import *
import json

def main():
    cities = ["Mykonos", "Prague", "Valencia", "Riga", "Zurich", "Bucharest", "Nice"]
    durations = [3, 3, 5, 5, 5, 5, 2]
    
    flight_list_str = [
        ("Mykonos", "Nice"),
        ("Mykonos", "Zurich"),
        ("Prague", "Bucharest"),
        ("Valencia", "Bucharest"),
        ("Zurich", "Prague"),
        ("Riga", "Nice"),
        ("Zurich", "Riga"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Valencia"),
        ("Bucharest", "Riga"),
        ("Prague", "Riga"),
        ("Prague", "Valencia"),
        ("Zurich", "Nice")
    ]
    
    flight_pairs_set = set()
    for flight in flight_list_str:
        city1, city2 = flight
        idx1 = cities.index(city1)
        idx2 = cities.index(city2)
        flight_pairs_set.add((idx1, idx2))
        flight_pairs_set.add((idx2, idx1))
    
    slot_city = [Int(f'slot_city_{i}') for i in range(7)]
    start = [Int(f'start_{i}') for i in range(7)]
    end = [Int(f'end_{i}') for i in range(7)]
    
    s = Solver()
    
    for i in range(7):
        s.add(slot_city[i] >= 0, slot_city[i] < 7)
    s.add(Distinct(slot_city))
    
    s.add(start[0] == 1)
    s.add(end[6] == 22)
    
    for i in range(1, 7):
        s.add(start[i] == end[i-1])
    
    mykonos_idx = cities.index("Mykonos")
    prague_idx = cities.index("Prague")
    
    # Create a Z3 array to map city indices to durations
    dur_arr = Array('durations', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        s.add(dur_arr[idx] == d)
    
    for i in range(7):
        # Look up duration using Z3 array
        dur = dur_arr[slot_city[i]]
        s.add(end[i] == start[i] + dur - 1)
    
    for i in range(7):
        s.add(If(slot_city[i] == mykonos_idx, And(start[i] == 1, end[i] == 3), True))
        s.add(If(slot_city[i] == prague_idx, And(start[i] == 7, end[i] == 9), True))
    
    for i in range(6):
        c1 = slot_city[i]
        c2 = slot_city[i+1]
        constraints = []
        for pair in flight_pairs_set:
            constraints.append(And(c1 == pair[0], c2 == pair[1]))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        slot_city_vals = [m.evaluate(slot_city[i]).as_long() for i in range(7)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(7)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(7)]
        
        itinerary_list = []
        for d in range(1, 23):
            for i in range(7):
                s_val = start_vals[i]
                e_val = end_vals[i]
                if s_val <= d <= e_val:
                    city_name = cities[slot_city_vals[i]]
                    itinerary_list.append({"day": d, "place": city_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()