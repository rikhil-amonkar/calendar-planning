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
    
    s = Solver()
    
    start = [Int(f'start_{i}') for i in range(9)]
    end = [Int(f'end_{i}') for i in range(9)]
    city_order = [Int(f'city_order_{k}') for k in range(9)]
    
    for i in range(9):
        s.add(start[i] >= 1, start[i] <= 24)
        s.add(end[i] >= 1, end[i] <= 24)
        s.add(end[i] == start[i] + required_days[cities[i]] - 1)
    
    for k in range(9):
        s.add(city_order[k] >= 0, city_order[k] < 9)
    s.add(Distinct(city_order))
    
    s.add(Sum([If(city_order[0] == i, start[i], 0) for i in range(9)]) == 1)
    s.add(Sum([If(city_order[8] == i, end[i], 0) for i in range(9)]) == 24)
    
    for k in range(8):
        left = Sum([If(city_order[k] == i, end[i], 0) for i in range(9)])
        right = Sum([If(city_order[k+1] == j, start[j], 0) for j in range(9)])
        s.add(left == right)
    
    for k in range(8):
        conds = []
        for edge in flight_edges_set:
            u, v = edge
            conds.append(And(city_order[k] == u, city_order[k+1] == v))
            conds.append(And(city_order[k] == v, city_order[k+1] == u))
        s.add(Or(conds))
    
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
        
        itinerary_list = []
        for day in range(1, 25):
            for i in range(9):
                if start_val[i] <= day <= end_val[i]:
                    itinerary_list.append({"day": day, "place": cities[i]})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()