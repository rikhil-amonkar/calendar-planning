import z3
import json

def main():
    # Cities encoding
    cities = ['London', 'Copenhagen', 'Tallinn', 'Oslo', 'Mykonos', 'Nice']
    city_dict = {c: i for i, c in enumerate(cities)}
    
    # Direct flights (undirected)
    connections = [
        (city_dict['London'], city_dict['Copenhagen']),
        (city_dict['Copenhagen'], city_dict['Tallinn']),
        (city_dict['Tallinn'], city_dict['Oslo']),
        (city_dict['Mykonos'], city_dict['London']),
        (city_dict['Oslo'], city_dict['Nice']),
        (city_dict['London'], city_dict['Nice']),
        (city_dict['Mykonos'], city_dict['Nice']),
        (city_dict['London'], city_dict['Oslo']),
        (city_dict['Copenhagen'], city_dict['Nice']),
        (city_dict['Copenhagen'], city_dict['Oslo'])
    ]
    
    # Required days per city
    req_days = [2, 3, 4, 5, 4, 3]  # London, Copenhagen, Tallinn, Oslo, Mykonos, Nice
    
    # Initialize solver
    s = z3.Solver()
    
    # Variables for each day: city1 (morning) and city2 (evening)
    city1 = [z3.Int(f'city1_{i}') for i in range(1, 17)]
    city2 = [z3.Int(f'city2_{i}') for i in range(1, 17)]
    
    # Domain constraints
    for i in range(16):
        s.add(z3.And(city1[i] >= 0, city1[i] <= 5))
        s.add(z3.And(city2[i] >= 0, city2[i] <= 5))
    
    # Continuity between days
    for i in range(15):
        s.add(city2[i] == city1[i+1])
    
    # Flight connections constraint
    for i in range(16):
        cond = z3.Or([z3.And(city1[i] == a, city2[i] == b) for a, b in connections] +
                     [z3.And(city1[i] == b, city2[i] == a) for a, b in connections])
        s.add(z3.Implies(city1[i] != city2[i], cond))
    
    # Presence matrix: present[c][i] indicates if city c is visited on day i
    present = [[z3.Int(f'present_{c}_{i}') for i in range(1, 17)] for c in range(6)]
    for c in range(6):
        for i in range(16):
            s.add(present[c][i] == z3.If(z3.Or(city1[i] == c, city2[i] == c), 1, 0))
    
    # Total days per city
    total_days = [z3.Int(f'total_{c}') for c in cities]
    for c in range(6):
        s.add(total_days[c] == sum(present[c][i] for i in range(16)))
        s.add(total_days[c] == req_days[c])
    
    # Specific constraints
    # Nice on day 14 and 16
    s.add(present[5][13] == 1)  # Day 14 (index 13)
    s.add(present[5][15] == 1)  # Day 16 (index 15)
    # Oslo between day 10 and 14
    s.add(z3.Or([present[3][i] == 1 for i in range(9, 14)]))  # Days 10-14 (indices 9 to 13)
    
    # Exactly 5 travel days
    travel_days = [z3.If(city1[i] != city2[i], 1, 0) for i in range(16)]
    s.add(sum(travel_days) == 5)
    
    # Solve
    if s.check() == z3.sat:
        m = s.model()
        city1_vals = [m.evaluate(city1[i]).as_long() for i in range(16)]
        city2_vals = [m.evaluate(city2[i]).as_long() for i in range(16)]
        
        # Generate segments
        segments = []
        current_city = city1_vals[0]
        start_day = 1
        for i in range(16):
            if i == 15 or city1_vals[i] != city2_vals[i]:
                segments.append((start_day, i+1, current_city))
                if i < 15:
                    current_city = city2_vals[i]
                start_day = i+1
        
        # Format output
        itinerary = []
        for seg in segments:
            start, end, city_idx = seg
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": cities[city_idx]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()