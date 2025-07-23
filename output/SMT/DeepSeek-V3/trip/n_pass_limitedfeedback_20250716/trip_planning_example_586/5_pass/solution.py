from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ['Prague', 'Frankfurt', 'Naples', 'Helsinki', 'Lyon']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    flights = [
        ('Prague', 'Lyon'),
        ('Prague', 'Frankfurt'),
        ('Frankfurt', 'Lyon'),
        ('Helsinki', 'Naples'),
        ('Helsinki', 'Frankfurt'),
        ('Naples', 'Frankfurt'),
        ('Prague', 'Helsinki')
    ]
    
    # Create flight pairs (both directions)
    flight_pairs = set()
    for a, b in flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    total_days = 12
    
    # Create variables for each day's city
    day_city = [Int(f'day_{day}') for day in range(total_days)]
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in range(total_days):
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Flight transitions between consecutive days
    for day in range(total_days - 1):
        current = day_city[day]
        next_day = day_city[day + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            *[And(current == city_idx[a], next_day == city_idx[b])
              for a, b in flight_pairs
            ]
        ))
    
    # Count days in each city (including flight days)
    city_days = [Sum([If(day_city[day] == i, 1, 0) 
                     for day in range(total_days)])
                for i in range(len(cities))]
    
    # Required days per city
    s.add(city_days[city_idx['Frankfurt']] == 3)
    s.add(city_days[city_idx['Naples']] == 4)
    s.add(city_days[city_idx['Helsinki']] == 4)
    s.add(city_days[city_idx['Lyon']] == 3)
    s.add(city_days[city_idx['Prague']] == 2)
    
    # Helsinki must be visited from day 2 to day 5 (1-based)
    for day in [1, 2, 3, 4]:  # 0-based days 1-4
        s.add(day_city[day] == city_idx['Helsinki'])
    
    # Workshop in Prague on day 1 (0-based day 0)
    s.add(day_city[0] == city_idx['Prague'])
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(total_days):
            city = cities[m.evaluate(day_city[day]).as_long()]
            itinerary.append({'day': day + 1, 'place': city})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Frankfurt'] == 3
        assert counts['Naples'] == 4
        assert counts['Helsinki'] == 4
        assert counts['Lyon'] == 3
        assert counts['Prague'] == 2
        
        for day in [1, 2, 3, 4]:
            assert itinerary[day]['place'] == 'Helsinki'
        
        assert itinerary[0]['place'] == 'Prague'
        
        for day in range(total_days - 1):
            current = itinerary[day]['place']
            next_p = itinerary[day + 1]['place']
            if current != next_p:
                assert (current, next_p) in flight_pairs
        
        return {'itinerary': itinerary}
    else:
        # If no solution found, relax some constraints
        s.reset()
        # Try allowing 1 less day in one city
        for i in range(len(cities)):
            s.push()
            temp = city_days[i]
            s.add(temp == city_days[i] - 1)
            if s.check() == sat:
                m = s.model()
                itinerary = []
                for day in range(total_days):
                    city = cities[m.evaluate(day_city[day]).as_long()]
                    itinerary.append({'day': day + 1, 'place': city})
                return {'itinerary': itinerary, 'note': f'Relaxed constraint for {cities[i]} by 1 day'}
            s.pop()
        return {"error": "No valid itinerary found even after relaxing constraints"}

# Run the solver
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))