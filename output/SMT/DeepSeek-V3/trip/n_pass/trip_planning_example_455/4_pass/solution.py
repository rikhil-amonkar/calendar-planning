from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ('Istanbul', 'Krakow'),
        ('Warsaw', 'Reykjavik'),
        ('Istanbul', 'Warsaw'),
        ('Riga', 'Istanbul'),
        ('Krakow', 'Warsaw'),
        ('Riga', 'Warsaw')
    ]
    
    # Make the flights bidirectional
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights
    
    num_days = 21
    days = range(1, num_days + 1)
    
    # Create Z3 variables: assign each day to a city
    city_vars = [Int(f'day_{day}') for day in days]
    
    # Create a mapping from city names to integers
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day must be assigned to a valid city ID
    for day_var in city_vars:
        s.add(day_var >= 0, day_var < len(cities))
    
    # Transition constraints: consecutive days must be the same city or connected by a direct flight
    for i in range(len(days) - 1):
        current_city = city_vars[i]
        next_city = city_vars[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[a], next_city == city_ids[b]) for a, b in direct_flights]
        ))
    
    # Total days per city constraints
    for city, total_days in cities.items():
        city_id = city_ids[city]
        s.add(Sum([If(city_var == city_id, 1, 0) for city_var in city_vars]) == total_days)
    
    # Riga must include day 1 or day 2 (meeting friend between day 1 and 2)
    riga_id = city_ids['Riga']
    s.add(Or(city_vars[0] == riga_id, city_vars[1] == riga_id))
    
    # Istanbul must include at least one day between day 2 and 7 (wedding between day 2 and 7)
    istanbul_id = city_ids['Istanbul']
    s.add(Or([city_vars[i] == istanbul_id for i in range(1, 7)]))  # days 2-7 (indices 1-6)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in days:
            city_id = model.evaluate(city_vars[day - 1]).as_long()
            city = id_to_city[city_id]
            itinerary.append({'day': day, 'place': city})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

# Output the solution
print(solve_itinerary())