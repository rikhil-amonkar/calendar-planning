from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Days are 1..8
    days = 8
    # For each day, which city are we in?
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day's assignment is one of the cities
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Flight connections (direct flights)
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Prague': ['Florence', 'Split', 'Krakow'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Transition constraints: if day i and i+1 are different, there must be a direct flight
    for i in range(days - 1):
        current_day = day_city[i]
        next_day = day_city[i + 1]
        # If different cities, then must have a direct flight
        s.add(Implies(current_day != next_day, 
                      Or([And(current_day == city_ids[c1], next_day == city_ids[c2]) 
                          for c1 in direct_flights 
                          for c2 in direct_flights.get(c1, [])])))
    
    # Duration constraints
    # Count days per city
    for city in cities:
        count = Sum([If(day == city_ids[city], 1, 0) for day in day_city])
        if city == 'Prague':
            s.add(count == 4)
        elif city == 'Stuttgart':
            s.add(count == 2)
        elif city == 'Split':
            s.add(count == 2)
        elif city == 'Krakow':
            s.add(count == 2)
        elif city == 'Florence':
            s.add(count == 2)
    
    # Event constraints
    # Wedding in Stuttgart between day 2 and 3: so day 2 or day 3 must be Stuttgart
    s.add(Or(day_city[1] == city_ids['Stuttgart'], day_city[2] == city_ids['Stuttgart']))
    
    # Meet friends in Split between day 3 and 4: so day 3 or day 4 must be Split
    s.add(Or(day_city[2] == city_ids['Split'], day_city[3] == city_ids['Split']))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_id = m.evaluate(day_city[i]).as_long()
            city_name = id_to_city[city_id]
            itinerary.append({'day': day_num, 'place': city_name})
        
        # Verify the solution meets all constraints
        # Check durations
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        assert city_days['Prague'] == 4
        assert city_days['Stuttgart'] == 2
        assert city_days['Split'] == 2
        assert city_days['Krakow'] == 2
        assert city_days['Florence'] == 2
        
        # Check transitions
        for i in range(days - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                assert next_city in direct_flights.get(current_city, [])
        
        # Check events
        stuttgart_days = [entry['day'] for entry in itinerary if entry['place'] == 'Stuttgart']
        assert any(day in [2, 3] for day in stuttgart_days)
        
        split_days = [entry['day'] for entry in itinerary if entry['place'] == 'Split']
        assert any(day in [3, 4] for day in split_days)
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")