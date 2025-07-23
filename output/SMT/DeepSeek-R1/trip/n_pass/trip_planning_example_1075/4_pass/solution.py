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
    
    # Each order position contains a unique city index (0-7)
    s.add([And(o >= 0, o < 8) for o in order])
    s.add(Distinct(order))
    
    # Chain constraint: next city starts when previous ends
    s.add(start_days[0] == 1)
    for i in range(7):
        current_city = order[i]
        next_start = start_days[i] + durations[current_city] - 1
        s.add(start_days[i+1] == next_start)
    s.add(start_days[7] + durations[order[7]] - 1 == 25)
    
    # Edinburgh must be from day 5 to 8
    edinburgh_idx = 2
    for i in range(8):
        s.add(If(order[i] == edinburgh_idx, 
                 And(start_days[i] == 5, 
                     start_days[i] + durations[edinburgh_idx] - 1 == 8), 
                 True))
    
    # Split must include at least one day between 19-23
    split_idx = 6
    s.add(Or([And(order[i] == split_idx, 
                 start_days[i] <= 19, 
                 start_days[i] + durations[split_idx] - 1 >= 23) 
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
        itinerary = []
        # Track start days for each city
        city_starts = [m.evaluate(sd).as_long() for sd in start_days]
        city_order = [m.evaluate(o).as_long() for o in order]
        
        # Build day-by-day itinerary
        for day in range(1, 26):
            current_cities = []
            for pos in range(8):
                city_idx = city_order[pos]
                start = city_starts[pos]
                end = start + durations[city_idx] - 1
                if start <= day <= end:
                    current_cities.append(cities[city_idx])
            # Sort alphabetically for consistent output
            for city in sorted(current_cities):
                itinerary.append({"day": day, "place": city})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()