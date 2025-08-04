from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Total days
    days = 25
    
    # Create Z3 variables: for each day, which city are we in?
    # day_city[d][c] is true if we are in city c on day d (1-based)
    day_city = [[Bool(f"day_{day+1}_city_{city}") for city in cities] for day in range(days)]
    
    s = Solver()
    
    # Constraints for each day: exactly one city is true (we are in exactly one city each day)
    for day in range(days):
        # At least one city is true
        s.add(Or(day_city[day]))
        # At most one city is true (no two cities on the same day)
        for c1 in range(len(cities)):
            for c2 in range(c1 + 1, len(cities)):
                s.add(Or(Not(day_city[day][c1]), Not(day_city[day][c2])))
    
    # Flight connections: transitions between cities must be via direct flights
    direct_flights = [
        ('Geneva', 'Istanbul'),
        ('Reykjavik', 'Munich'),
        ('Stuttgart', 'Valencia'),
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Istanbul'),
        ('Munich', 'Geneva'),
        ('Istanbul', 'Vilnius'),
        ('Valencia', 'Seville'),
        ('Valencia', 'Istanbul'),
        ('Vilnius', 'Munich'),
        ('Seville', 'Munich'),
        ('Munich', 'Istanbul'),
        ('Valencia', 'Geneva'),
        ('Valencia', 'Munich')
    ]
    # Make flights bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    # Allow staying in the same city or moving to a directly connected city
    for day in range(days - 1):
        current_day = day
        next_day = day + 1
        # For each possible current city and next city, if they are different, must be connected by a direct flight
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 != c2:
                    city1 = cities[c1]
                    city2 = cities[c2]
                    if (city1, city2) not in direct_flights:
                        # If we are in city1 on current_day and city2 on next_day, it's not allowed
                        s.add(Or(Not(day_city[current_day][c1]), Not(day_city[next_day][c2])))
    
    # Specific constraints
    # Reykjavik: workshop between day 1-4 (must be in Reykjavik at least one of these days)
    reykjavik_idx = city_to_idx['Reykjavik']
    s.add(Or([day_city[d][reykjavik_idx] for d in range(4)]))
    
    # Stuttgart: conference on day 4 and day 7 (1-based days 4 and 7; 0-based 3 and 6)
    stuttgart_idx = city_to_idx['Stuttgart']
    s.add(day_city[3][stuttgart_idx])  # day 4
    s.add(day_city[6][stuttgart_idx])  # day 7
    
    # Istanbul: relatives between day 19-22 (1-based days 19-22; 0-based 18-21)
    istanbul_idx = city_to_idx['Istanbul']
    s.add(Or([day_city[d][istanbul_idx] for d in range(18, 22)]))
    
    # Munich: annual show day 13-15 (1-based days 13-15; 0-based 12-14)
    munich_idx = city_to_idx['Munich']
    s.add(Or([day_city[d][munich_idx] for d in range(12, 15)]))
    
    # Total days per city
    city_days_required = {
        'Stuttgart': 4,
        'Istanbul': 4,
        'Vilnius': 4,
        'Seville': 3,
        'Geneva': 5,
        'Valencia': 5,
        'Munich': 3,
        'Reykjavik': 4
    }
    
    for city in cities:
        required = city_days_required[city]
        idx = city_to_idx[city]
        total_days = Sum([If(day_city[d][idx], 1, 0) for d in range(days)])
        s.add(total_days == required)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(days):
            for c in range(len(cities)):
                if is_true(model.eval(day_city[day][c])):
                    itinerary.append({"day": day + 1, "place": cities[c]})
                    break
        return itinerary
    else:
        return None

itinerary = solve_itinerary()
if itinerary is not None:
    print('{\n  "itinerary": [')
    for i, entry in enumerate(itinerary):
        comma = "," if i < len(itinerary) - 1 else ""
        print(f'    {{"day": {entry["day"]}, "place": "{entry["place"]}"}}{comma}')
    print('  ]\n}')
else:
    print("No valid itinerary found.")