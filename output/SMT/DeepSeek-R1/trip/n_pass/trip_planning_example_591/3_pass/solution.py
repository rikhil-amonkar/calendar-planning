from z3 import *
import json

def main():
    cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    durations = [2, 2, 4, 6, 7]  # durations in the same order as cities
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    allowed_edges = set()
    edges = [
        ('Geneva', 'Munich'), 
        ('Munich', 'Valencia'), 
        ('Bucharest', 'Valencia'), 
        ('Munich', 'Bucharest'), 
        ('Valencia', 'Stuttgart'), 
        ('Geneva', 'Valencia')
    ]
    for u, v in edges:
        u_idx = city_to_idx[u]
        v_idx = city_to_idx[v]
        allowed_edges.add((u_idx, v_idx))
        allowed_edges.add((v_idx, u_idx))
    
    # We have 5 positions in the travel sequence
    pos = [Int(f'pos_{i}') for i in range(5)]  # which city is at position i
    start = [Int(f'start_{i}') for i in range(5)]  # start day for the city at position i
    city_start = [Int(f'city_start_{i}') for i in range(5)]  # start day for each city (by city index)
    
    s = Solver()
    
    # Each position has a city index between 0 and 4
    for p in pos:
        s.add(p >= 0, p < 5)
    
    # All cities are visited exactly once (permutation)
    s.add(Distinct(pos))
    
    # Helper to get duration of a city (by its index)
    def duration(city_idx):
        return durations[city_idx]
    
    # The start day for the first city is 1
    s.add(start[0] == 1)
    
    # For each subsequent position, the start day is: current start = previous start + previous duration - 1
    for i in range(4):
        prev_city = pos[i]
        s.add(start[i+1] == start[i] + duration(prev_city) - 1)
    
    # The last city must end by day 17
    last_city = pos[4]
    s.add(start[4] + duration(last_city) - 1 == 17)
    
    # Link the city_start for each city: if city j is at position i, then city_start[j] = start[i]
    for j in range(5):
        s.add(Or([And(pos[i] == j, city_start[j] == start[i]) for i in range(5)]))
    
    # Flight constraints: consecutive cities in the sequence must have a direct flight
    for i in range(4):
        city_i = pos[i]
        city_j = pos[i+1]
        s.add(Or([And(city_i == u, city_j == v) for (u, v) in allowed_edges]))
    
    # Constraints for Geneva and Munich: 
    geneva_idx = city_to_idx['Geneva']
    munich_idx = city_to_idx['Munich']
    s.add(city_start[geneva_idx] <= 4)  # Geneva starts by day 4
    s.add(city_start[munich_idx] <= 10) # Munich starts by day 10
    
    if s.check() == sat:
        model = s.model()
        
        # Get the actual start day for each city
        city_start_vals = {}
        for j in range(5):
            city_start_vals[j] = model.evaluate(city_start[j]).as_long()
        
        # Calculate end day for each city: start + duration - 1
        city_end_vals = {}
        for j in range(5):
            city_end_vals[j] = city_start_vals[j] + durations[j] - 1
        
        # Build the itinerary: for each day 1 to 17, list all cities we are in
        itinerary = []
        for day in range(1, 18):
            cities_today = []
            for j in range(5):
                if city_start_vals[j] <= day <= city_end_vals[j]:
                    cities_today.append(idx_to_city[j])
            # Sort alphabetically for consistent output
            cities_today.sort()
            itinerary.append({'day': day, 'place': ", ".join(cities_today)})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()