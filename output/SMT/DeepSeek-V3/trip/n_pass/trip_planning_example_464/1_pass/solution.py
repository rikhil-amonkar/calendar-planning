from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    
    # Direct flight connections
    direct_flights = {
        ('Dubrovnik', 'Oslo'), ('Frankfurt', 'Krakow'), ('Frankfurt', 'Oslo'),
        ('Dubrovnik', 'Frankfurt'), ('Krakow', 'Oslo'), ('Naples', 'Oslo'),
        ('Naples', 'Dubrovnik'), ('Naples', 'Frankfurt')
    }
    # Ensure bidirectional
    all_flights = set()
    for (a, b) in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    direct_flights = all_flights
    
    # Total days
    total_days = 18
    
    # Create solver
    s = Solver()
    
    # Variables: day[i] is the city on day i (1-based)
    day = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    
    # Map cities to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Constraints: each day must be one of the cities
    for d in day:
        s.add(Or([d == city_to_int[city] for city in cities]))
    
    # Constraints for total days in each city
    s.add(Sum([If(d == city_to_int['Krakow'], 1, 0) for d in day]) == 5)
    s.add(Sum([If(d == city_to_int['Frankfurt'], 1, 0) for d in day]) == 4)
    s.add(Sum([If(d == city_to_int['Oslo'], 1, 0) for d in day]) == 3)
    s.add(Sum([If(d == city_to_int['Dubrovnik'], 1, 0) for d in day]) == 5)
    s.add(Sum([If(d == city_to_int['Naples'], 1, 0) for d in day]) == 5)
    
    # Oslo must be between day 16-18 (inclusive)
    s.add(Or(day[15] == city_to_int['Oslo'], day[16] == city_to_int['Oslo'], day[17] == city_to_int['Oslo']))
    
    # Dubrovnik must have some days between day 5-9 (inclusive)
    s.add(Or([day[i] == city_to_int['Dubrovnik'] for i in range(4, 9)]))  # days 5-9 (1-based)
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(1, total_days):
        current_city = day[i-1]
        next_city = day[i]
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) for (a, b) in direct_flights]
        ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        day_assignments = []
        for i in range(1, total_days + 1):
            city_idx = model.evaluate(day[i-1]).as_long()
            day_assignments.append(int_to_city[city_idx])
        
        itinerary = []
        current_place = day_assignments[0]
        start_day = 1
        
        for i in range(1, total_days):
            if day_assignments[i] == current_place:
                continue
            else:
                # Add the stay up to the day before the flight
                if start_day <= i:
                    itinerary.append({
                        'day_range': f'Day {start_day}-{i}',
                        'place': current_place
                    })
                # Add the flight day for departure and arrival
                itinerary.append({
                    'day_range': f'Day {i+1}',
                    'place': current_place
                })
                itinerary.append({
                    'day_range': f'Day {i+1}',
                    'place': day_assignments[i]
                })
                current_place = day_assignments[i]
                start_day = i + 1
        # Add the last stay
        if start_day <= total_days:
            itinerary.append({
                'day_range': f'Day {start_day}-{total_days}',
                'place': current_place
            })
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No solution found'}

result = solve_itinerary()
print(json.dumps(result, indent=2))