from z3 import *
import json

def main():
    cities = ["Mykonos", "Prague", "Valencia", "Riga", "Zurich", "Bucharest", "Nice"]
    city_index = {c: i for i, c in enumerate(cities)}
    days_list = [3, 3, 5, 5, 5, 5, 2]  # Corresponding to cities order

    flights_list = [
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
    
    flight_pairs = []
    for (c1, c2) in flights_list:
        i1 = city_index[c1]
        i2 = city_index[c2]
        flight_pairs.append((i1, i2))
        flight_pairs.append((i2, i1))
    
    slot_city = [Int(f'slot_city_{i}') for i in range(7)]
    start = [Int(f'start_{i}') for i in range(7)]
    end = [Int(f'end_{i}') for i in range(7)]
    
    s = Solver()
    
    for i in range(7):
        s.add(slot_city[i] >= 0)
        s.add(slot_city[i] < 7)
    
    s.add(Distinct(slot_city))
    
    s.add(start[0] == 1)
    s.add(end[6] == 22)
    
    for i in range(7):
        dur_expr = Int(f'dur_{i}')
        cond = (dur_expr == days_list[0])
        for idx in range(1, 7):
            cond = Or(cond, And(slot_city[i] == idx, dur_expr == days_list[idx]))
        s.add(cond)
        s.add(end[i] == start[i] + dur_expr - 1)
    
    for i in range(1, 7):
        s.add(start[i] == end[i-1])
    
    for i in range(6):
        constraints = []
        for (a, b) in flight_pairs:
            constraints.append(And(slot_city[i] == a, slot_city[i+1] == b))
        s.add(Or(constraints))
    
    mykonos_idx = city_index["Mykonos"]
    prague_idx = city_index["Prague"]
    
    for i in range(7):
        s.add(If(slot_city[i] == mykonos_idx, start[i] <= 3, True))
        s.add(If(slot_city[i] == prague_idx, And(start[i] <= 9, end[i] >= 7), True))
    
    if s.check() == sat:
        m = s.model()
        slot_city_vals = [m.evaluate(slot_city[i]).as_long() for i in range(7)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(7)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(7)]
        
        itinerary_list = []
        for d in range(1, 23):
            for i in range(7):
                s_i = start_vals[i]
                e_i = end_vals[i]
                if s_i <= d <= e_i:
                    city_name = cities[slot_city_vals[i]]
                    itinerary_list.append({"day": d, "place": city_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()