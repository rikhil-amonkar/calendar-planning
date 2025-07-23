from z3 import *
import json

def main():
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    durations = [4, 3, 4, 5, 5, 2, 5, 4]
    edges = [
        (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
        (1, 6), (1, 7),
        (2, 4), (2, 7),
        (3, 4), (3, 7),
        (4, 5), (4, 6),
        (5, 6),
        (6, 7)
    ]
    
    s = Solver()
    order = [Int(f'o{i}') for i in range(8)]
    start_days = [Int(f'sd{i}') for i in range(8)]
    
    # Create Z3 array for durations
    durations_arr = Array('durations_arr', IntSort(), IntSort())
    for i in range(8):
        durations_arr = Store(durations_arr, i, durations[i])
    
    # Each order position contains a unique city index (0-7)
    s.add([And(o >= 0, o < 8) for o in order])
    s.add(Distinct(order))
    
    # Chain constraint: next city starts when previous ends
    s.add(start_days[0] == 1)
    for i in range(7):
        current_city = order[i]
        current_dur = Select(durations_arr, current_city)
        next_start = start_days[i] + current_dur - 1
        s.add(start_days[i+1] == next_start)
    
    last_city = order[7]
    last_dur = Select(durations_arr, last_city)
    s.add(start_days[7] + last_dur - 1 == 25)
    
    # Edinburgh must be from day 5 to 8
    edinburgh_idx = 2
    for i in range(8):
        dur_edinburgh = Select(durations_arr, edinburgh_idx)
        s.add(If(order[i] == edinburgh_idx, 
                 And(start_days[i] == 5, 
                     start_days[i] + dur_edinburgh - 1 == 8), 
                 True))
    
    # Split must include at least one day between 19-23
    split_idx = 6
    split_dur = Select(durations_arr, split_idx)
    s.add(Or([And(order[i] == split_idx, 
              start_days[i] <= 23, 
              start_days[i] + split_dur - 1 >= 19) 
            for i in range(8)]))
    
    # Flight connections between consecutive cities
    for i in range(7):
        city1 = order[i]
        city2 = order[i+1]
        valid_flight = Or([And(city1 == a, city2 == b) for a, b in edges] + 
                         [And(city1 == b, city2 == a) for a, b in edges])
        s.add(valid_flight)
    
    if s.check() == sat:
        m = s.model()
        city_starts = [0] * 8
        city_order = [0] * 8
        for i in range(8):
            city_order[i] = m.evaluate(order[i]).as_long()
            city_starts[i] = m.evaluate(start_days[i]).as_long()
        
        itinerary = []
        for day in range(1, 26):
            current_cities = []
            for pos in range(8):
                city_idx = city_order[pos]
                start = city_starts[pos]
                dur = durations[city_idx]
                end = start + dur - 1
                if start <= day <= end:
                    current_cities.append(cities[city_idx])
            for city in sorted(current_cities):
                itinerary.append({"day": day, "place": city})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()