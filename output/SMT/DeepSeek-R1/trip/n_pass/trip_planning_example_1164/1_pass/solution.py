from z3 import *
import json

def main():
    # Define cities and their stay durations
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
    
    # List of cities for indexing
    cities_list = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_to_index = {city: idx for idx, city in enumerate(cities_list)}
    index_to_city = {idx: city for idx, city in enumerate(cities_list)}
    
    # Define direct flights
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
    
    # Initialize Z3 solver
    s = Solver()
    
    # Order of cities: 8 integers representing the sequence
    order = [Int(f'order_{i}') for i in range(8)]
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    # Start and end days for each position in the order
    starts = [Int(f'starts_{i}') for i in range(8)]
    ends = [Int(f'ends_{i}') for i in range(8)]
    
    # First city starts on day 1
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + cities[index_to_city[order[0]]] - 1)
    
    # Subsequent cities start where the previous ended
    for i in range(1, 8):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + cities[index_to_city[order[i]]] - 1)
    
    # Entire trip ends on day 17
    s.add(ends[7] == 17)
    
    # City-specific start and end variables
    city_start = [Int(f'city_start_{city}') for city in cities_list]
    city_end = [Int(f'city_end_{city}') for city in cities_list]
    
    # Link city_start and city_end to the order positions
    for c_idx in range(8):
        for pos in range(8):
            s.add(Implies(order[pos] == c_idx, 
                          And(city_start[c_idx] == starts[pos], 
                              city_end[c_idx] == ends[pos])))
    
    # Event constraints
    # Reykjavik: must overlap day 3 or 4
    idxR = city_to_index['Reykjavik']
    s.add(city_start[idxR] <= 4)
    s.add(city_end[idxR] >= 3)
    
    # Stockholm: must overlap day 4 or 5
    idxS = city_to_index['Stockholm']
    s.add(city_start[idxS] <= 5)
    s.add(city_end[idxS] >= 4)
    
    # Porto: must include at least one day between 13 and 17
    idxP = city_to_index['Porto']
    s.add(city_end[idxP] >= 13)
    
    # Vienna: must overlap day 11 to 13
    idxV = city_to_index['Vienna']
    s.add(city_start[idxV] <= 13)
    s.add(city_end[idxV] >= 11)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        conds = []
        for A, B in flights:
            idxA = city_to_index[A]
            idxB = city_to_index[B]
            conds.append(And(order[i] == idxA, order[i+1] == idxB))
            conds.append(And(order[i] == idxB, order[i+1] == idxA))
        s.add(Or(conds))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Determine the order of cities
        order_list = []
        for i in range(8):
            idx_val = m.evaluate(order[i]).as_long()
            order_list.append(index_to_city[idx_val])
        
        # Compute start and end days for each city in the order
        starts_vals = [0] * 8
        ends_vals = [0] * 8
        starts_vals[0] = 1
        ends_vals[0] = starts_vals[0] + cities[order_list[0]] - 1
        for i in range(1, 8):
            starts_vals[i] = ends_vals[i-1]
            ends_vals[i] = starts_vals[i] + cities[order_list[i]] - 1
        
        # Build itinerary
        itinerary = []
        for day in range(1, 18):
            locations = []
            for i in range(8):
                if starts_vals[i] <= day <= ends_vals[i]:
                    locations.append(order_list[i])
            locations.sort()
            itinerary.append({'day': day, 'location': ','.join(locations)})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()