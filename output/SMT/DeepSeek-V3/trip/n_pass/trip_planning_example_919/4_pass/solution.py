from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Riga', 'Oslo'), ('Rome', 'Oslo'), ('Vienna', 'Milan'), ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'), ('Riga', 'Milan'), ('Lisbon', 'Oslo'), ('Rome', 'Riga'),
        ('Rome', 'Lisbon'), ('Vienna', 'Riga'), ('Vienna', 'Rome'), ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'), ('Vilnius', 'Oslo'), ('Riga', 'Vilnius'), ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'), ('Milan', 'Lisbon')
    ]
    # Make flights bidirectional
    bidirectional_flights = []
    for (a, b) in direct_flights:
        bidirectional_flights.append((a, b))
        bidirectional_flights.append((b, a))
    # Also, a city has a flight to itself (staying)
    for city in cities:
        bidirectional_flights.append((city, city))
    
    flight_pairs = set((city_to_int[a], city_to_int[b]) for (a, b) in bidirectional_flights)
    
    # Create solver
    s = Solver()
    
    # Variables: day 1 to 15, each is a city (represented as an integer)
    days = [Int(f'day_{i}') for i in range(1, 16)]
    
    # Each day's value must be between 0 and 6 (representing the cities)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints:
    # Day 1 and 4 must be Vienna
    s.add(days[0] == city_to_int['Vienna'])
    s.add(days[3] == city_to_int['Vienna'])
    
    # Lisbon between day 11 and 13: at least one day in 11-13 is Lisbon
    s.add(Or([days[i] == city_to_int['Lisbon'] for i in range(10, 13)]))
    
    # Oslo between day 13 and 15: at least one day in 13-15 is Oslo
    s.add(Or([days[i] == city_to_int['Oslo'] for i in range(12, 15)]))
    
    # Flight constraints: consecutive days must have a direct flight.
    for i in range(14):  # days 1-15: pairs (0,1), (1,2), ..., (13,14)
        s.add(Or([And(days[i] == a, days[i+1] == b) for (a, b) in flight_pairs]))
    
    # Duration constraints:
    # Vienna: 4 days (including days 1 and 4)
    # Milan: 2 days
    # Rome: 3 days
    # Riga: 2 days
    # Lisbon: 3 days
    # Vilnius: 4 days
    # Oslo: 3 days
    
    # Count occurrences of each city.
    duration_constraints = [
        (city_to_int['Vienna'], 4),
        (city_to_int['Milan'], 2),
        (city_to_int['Rome'], 3),
        (city_to_int['Riga'], 2),
        (city_to_int['Lisbon'], 3),
        (city_to_int['Vilnius'], 4),
        (city_to_int['Oslo'], 3)
    ]
    
    for city_idx, required_days in duration_constraints:
        s.add(Sum([If(days[i] == city_idx, 1, 0) for i in range(15)]) == required_days)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(15):
            day = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day, 'place': city})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        # Verify the constraints
        assert counts['Vienna'] == 4
        assert counts['Milan'] == 2
        assert counts['Rome'] == 3
        assert counts['Riga'] == 2
        assert counts['Lisbon'] == 3
        assert counts['Vilnius'] == 4
        assert counts['Oslo'] == 3
        assert itinerary[0]['place'] == 'Vienna'  # Day 1
        assert itinerary[3]['place'] == 'Vienna'  # Day 4
        # Check Lisbon between day 11-13 (at least one)
        lisbon_days = [entry['day'] for entry in itinerary if entry['place'] == 'Lisbon']
        assert any(11 <= day <= 13 for day in lisbon_days)
        # Check Oslo between day 13-15 (at least one)
        oslo_days = [entry['day'] for entry in itinerary if entry['place'] == 'Oslo']
        assert any(13 <= day <= 15 for day in oslo_days)
        
        # Verify consecutive flights
        for i in range(14):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            assert (current_city == next_city) or ((current_city, next_city) in bidirectional_flights)
        
        # Convert itinerary to the required JSON format
        result = {
            'itinerary': [
                {'day': entry['day'], 'place': entry['place']} for entry in itinerary
            ]
        }
        return result
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))