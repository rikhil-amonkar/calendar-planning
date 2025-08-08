from z3 import *
import json

def main():
    cities = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 5,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 3,
        'Split': 3,
        'Copenhagen': 2
    }
    cities_list = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_to_index = {city: idx for idx, city in enumerate(cities_list)}
    durations = [cities[city] for city in cities_list]
    
    flights = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(8)]
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    starts = [Int(f'starts_{i}') for i in range(8)]
    ends = [Int(f'ends_{i}') for i in range(8)]
    
    dur_arr = Array('durations', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        dur_arr = Store(dur_arr, idx, d)
    
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + Select(dur_arr, order[0]) - 1)
    
    for i in range(1, 8):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + Select(dur_arr, order[i]) - 1)
    
    s.add(ends[7] == 17)
    
    city_start = [Int(f'city_start_{city}') for city in cities_list]
    city_end = [Int(f'city_end_{city}') for city in cities_list]
    
    for c_idx in range(8):
        for pos in range(8):
            s.add(Implies(order[pos] == c_idx, 
                          And(city_start[c_idx] == starts[pos], 
                              city_end[c_idx] == ends[pos])))
    
    for c_idx in range(8):
        s.add(city_end[c_idx] - city_start[c_idx] + 1 == durations[c_idx])
    
    idxR = city_to_index['Reykjavik']
    s.add(city_start[idxR] <= 4)
    s.add(city_end[idxR] >= 3)
    
    idxS = city_to_index['Stockholm']
    s.add(city_start[idxS] <= 5)
    s.add(city_end[idxS] >= 4)
    
    idxP = city_to_index['Porto']
    s.add(city_end[idxP] >= 13)
    
    idxV = city_to_index['Vienna']
    s.add(city_start[idxV] <= 13)
    s.add(city_end[idxV] >= 11)
    
    flight_edges = {}
    for A, B in flights:
        idxA = city_to_index[A]
        idxB = city_to_index[B]
        flight_edges[(idxA, idxB)] = True
        flight_edges[(idxB, idxA)] = True
    
    for i in range(7):
        curr_city = order[i]
        next_city = order[i+1]
        s.add(flight_edges.get((curr_city, next_city), False)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 18):
            locations = []
            for city in cities_list:
                c_idx = city_to_index[city]
                start_val = m[city_start[c_idx]].as_long()
                end_val = m[city_end[c_idx]].as_long()
                if start_val <= day <= end_val:
                    locations.append(city)
            locations.sort()
            itinerary.append({'day': day, 'location': ','.join(locations)})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()