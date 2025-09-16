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
    
    for i in range(9):
        s.add(Or(position[i] != 0, start[i] == 1))
        s.add(Or(position[i] != 8, end[i] == 24))
    
    for i in range(9):
        for j in range(9):
            if i != j:
                s.add(Implies(position[j] == position[i] + 1, end[i] == start[j]))
    
    for i in range(9):
        for j in range(9):
            if i != j and (i, j) not in directed_flight_edges_set:
                s.add(position[j] != position[i] + 1)
    
    naples_idx = city_to_index['Naples']
    s.add(start[naples_idx] <= 20)
    s.add(end[naples_idx] >= 18)
    
    venice_idx = city_to_index['Venice']
    s.add(start[venice_idx] <= 10)
    s.add(end[venice_idx] >= 6)
    
    barcelona_idx = city_to_index['Barcelona']
    s.add(start[barcelona_idx] <= 6)
    s.add(end[barcelona_idx] >= 5)
    
    nice_idx = city_to_index['Nice']
    s.add(start[nice_idx] <= 24)
    s.add(end[nice_idx] >= 23)
    
    if s.check() == sat:
        m = s.model()
        start_val = [m.evaluate(start[i]).as_long() for i in range(9)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(9)]
        pos_val = [m.evaluate(position[i]).as_long() for i in range(9)]
        
        order = [0] * 9
        for i in range(9):
            order[pos_val[i]] = i
        
        itinerary_list = []
        for day in range(1, 25):
            for idx in order:
                if start_val[idx] <= day <= end_val[idx]:
                    itinerary_list.append({"day": day, "place": cities[idx]})
                    break
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()