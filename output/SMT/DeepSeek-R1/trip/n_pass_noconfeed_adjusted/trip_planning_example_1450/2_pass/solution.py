import json
from z3 import *

def main():
    # City mapping
    cities = {
        'Stockholm': 0,
        'Hamburg': 1,
        'Florence': 2,
        'Istanbul': 3,
        'Oslo': 4,
        'Vilnius': 5,
        'Santorini': 6,
        'Munich': 7,
        'Frankfurt': 8,
        'Krakow': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    n_days = 32
    # Adjusted required days to sum to 32
    req_days = [3, 3, 2, 5, 3, 3, 2, 3, 3, 5]  # Ordered by city index
    
    # Direct flights (as symmetric pairs)
    direct_flights = [
        (0,4), (0,7), (0,1), (0,3), (0,8), (0,9), (0,6),
        (1,7), (1,3), (1,8), (1,4),
        (2,8), (2,7),
        (3,4), (3,5), (3,8), (3,7), (3,9), (3,1), (3,0),
        (4,5), (4,8), (4,7), (4,1), (4,9), (4,6), (4,0),
        (5,9), (5,3), (5,4), (5,8), (5,7),
        (6,4), (6,0),
        (7,8), (7,1), (7,3), (7,4), (7,9), (7,2), (7,5),
        (8,9), (8,3), (8,4), (8,1), (8,0), (8,7), (8,5), (8,2),
        (9,3), (9,4), (9,0), (9,7), (9,5)
    ]
    direct_set = set()
    for a, b in direct_flights:
        direct_set.add((a, b))
        direct_set.add((b, a))
    
    # Create solver
    s = Solver()
    
    # Create variables: morning_city and evening_city for each day
    morning_city = [Int(f'morning_{i}') for i in range(1, n_days+1)]
    evening_city = [Int(f'evening_{i}') for i in range(1, n_days+1)]
    
    # Constraint: cities must be valid
    for i in range(n_days):
        s.add(And(morning_city[i] >= 0, morning_city[i] <= 9))
        s.add(And(evening_city[i] >= 0, evening_city[i] <= 9))
    
    # Fixed events: Krakow days 5-9 and Istanbul days 25-29 (no travel)
    for i in range(5, 10):  # days 5 to 9 (1-indexed)
        s.add(morning_city[i-1] == cities['Krakow'])
        s.add(evening_city[i-1] == cities['Krakow'])
    for i in range(25, 30):  # days 25 to 29
        s.add(morning_city[i-1] == cities['Istanbul'])
        s.add(evening_city[i-1] == cities['Istanbul'])
    
    # Constraint: No other days in Krakow or Istanbul outside event periods
    for i in range(1, n_days+1):
        if i < 5 or i > 9:
            s.add(morning_city[i-1] != cities['Krakow'])
            s.add(evening_city[i-1] != cities['Krakow'])
        if i < 25 or i > 29:
            s.add(morning_city[i-1] != cities['Istanbul'])
            s.add(evening_city[i-1] != cities['Istanbul'])
    
    # Start in Stockholm on morning of day 1
    s.add(morning_city[0] == cities['Stockholm'])
    
    # Continuity constraint
    for i in range(1, n_days):
        s.add(evening_city[i-1] == morning_city[i])
    
    # Travel constraint: if morning != evening, then direct flight must exist
    for i in range(n_days):
        cond = (morning_city[i] != evening_city[i])
        s.add(Implies(cond, Or([And(morning_city[i] == a, evening_city[i] == b) for (a, b) in direct_set])))
    
    # Count days per city (only evening cities)
    for c in range(10):
        total = Sum([If(evening_city[i] == c, 1, 0) for i in range(n_days)])
        s.add(total == req_days[c])
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        morn_vals = [m.evaluate(morning_city[i]).as_long() for i in range(n_days)]
        # Form segments
        segments = []
        current_city = morn_vals[0]
        start_day = 1
        for day in range(1, n_days):
            if morn_vals[day] != current_city:
                segments.append((start_day, day, current_city))
                current_city = morn_vals[day]
                start_day = day+1  # +1 because days are 1-indexed
        segments.append((start_day, n_days, current_city))
        
        # Convert to JSON output
        itinerary = []
        for seg in segments:
            start, end, city_idx = seg
            place = city_names[city_idx]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": place})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()