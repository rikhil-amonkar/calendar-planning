from z3 import *
import json

def main():
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    required_days = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Barcelona': 2,
        'Porto': 4
    }
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    flights_str = [
        "Venice and Nice",
        "Naples and Amsterdam",
        "Barcelona and Nice",
        "Amsterdam and Nice",
        "Stuttgart and Valencia",
        "Stuttgart and Porto",
        "Split and Stuttgart",
        "Split and Naples",
        "Valencia and Amsterdam",
        "Barcelona and Porto",
        "Valencia and Naples",
        "Venice and Amsterdam",
        "Barcelona and Naples",
        "Barcelona and Valencia",
        "Split and Amsterdam",
        "Barcelona and Venice",
        "Stuttgart and Amsterdam",
        "Naples and Nice",
        "Venice and Stuttgart",
        "Split and Barcelona",
        "Porto and Nice",
        "Barcelona and Stuttgart",
        "Venice and Naples",
        "Porto and Amsterdam",
        "Porto and Valencia",
        "Stuttgart and Naples",
        "Barcelona and Amsterdam"
    ]
    
    flight_edges_set = set()
    for flight in flights_str:
        parts = flight.split(' and ')
        city1 = parts[0].strip()
        city2 = parts[1].strip()
        idx1 = city_to_index[city1]
        idx2 = city_to_index[city2]
        flight_edges_set.add((min(idx1, idx2), max(idx1, idx2)))
    
    directed_flight_edges_set = set()
    for (u, v) in flight_edges_set:
        directed_flight_edges_set.add((u, v))
        directed_flight_edges_set.add((v, u))
    
    s = Solver()
    
    start = [Int(f'start_{i}') for i in range(9)]
    end = [Int(f'end_{i}') for i in range(9)]
    position = [Int(f'position_{i}') for i in range(9)]
    
    for i in range(9):
        s.add(start[i] >= 1)
        s.add(end[i] <= 24)
        s.add(end[i] == start[i] + required_days[cities[i]] - 1)
        s.add(position[i] >= 0, position[i] < 9)
    
    s.add(Distinct(position))
    
    # First city starts on day 1
    for i in range(9):
        s.add(Implies(position[i] == 0, start[i] == 1))
    
    # Last city ends on day 24
    for i in range(9):
        s.add(Implies(position[i] == 8, end[i] == 24))
    
    # Consecutive cities: next starts the day after previous ends
    for i in range(9):
        for j in range(9):
            if i != j:
                s.add(Implies(position[j] == position[i] + 1, start[j] == end[i] + 1))
    
    # Flight connections
    for i in range(9):
        for j in range(9):
            if i != j and (i, j) not in directed_flight_edges_set:
                s.add(Not(And(position[j] == position[i] + 1)))
    
    # Meeting constraints
    naples_idx = city_to_index['Naples']
    s.add(start[naples_idx] <= 18)
    s.add(end[naples_idx] >= 20)
    
    venice_idx = city_to_index['Venice']
    s.add(start[venice_idx] <= 6)
    s.add(end[venice_idx] >= 10)
    
    barcelona_idx = city_to_index['Barcelona']
    s.add(start[barcelona_idx] <= 5)
    s.add(end[barcelona_idx] >= 6)
    
    nice_idx = city_to_index['Nice']
    s.add(start[nice_idx] <= 23)
    s.add(end[nice_idx] >= 24)
    
    # Attempt to find solution
    result = s.check()
    if result == sat:
        m = s.model()
        start_val = [m.evaluate(start[i]).as_long() for i in range(9)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(9)]
        pos_val = [m.evaluate(position[i]).as_long() for i in range(9)]
        
        # Build itinerary in order
        itinerary = []
        for pos in range(9):
            for i in range(9):
                if pos_val[i] == pos:
                    s_day = start_val[i]
                    e_day = end_val[i]
                    if s_day == e_day:
                        day_range = f"Day {s_day}"
                    else:
                        day_range = f"Day {s_day}-{e_day}"
                    itinerary.append({'day_range': day_range, 'place': cities[i]})
                    break
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()