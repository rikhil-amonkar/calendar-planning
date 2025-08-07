from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    # Direct flights as a list of tuples (assuming bidirectional unless specified)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),  # Assuming 'Madrid' is a typo and should be 'Madrid'
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),  # Assuming 'Madrid'
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')  # One-way from Reykjavik to Madrid
    ]
    
    # Correcting city name typos in direct_flights
    corrected_flights = []
    for flight in direct_flights:
        city1, city2 = flight
        if city1 == 'Madrid' or city1 == 'Madrid':
            city1 = 'Madrid'
        if city2 == 'Madrid' or city2 == 'Madrid':
            city2 = 'Madrid'
        corrected_flights.append((city1, city2))
    
    # Create flight_pairs: bidirectional for all except one-way flights
    flight_pairs = set()
    for flight in corrected_flights:
        A, B = flight
        flight_pairs.add((A, B))
        if (A, B) != ('Reykjavik', 'Madrid'):
            flight_pairs.add((B, A))
    
    # Create Z3 variables for each day (1..14), each is one of the cities
    days = 14
    city_names = list(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day variable must be between 0 and len(city_names) - 1
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(city_names))
    
    # Constraint 1: Helsinki on day 1 and day 2
    s.add(day_vars[0] == city_to_int['Helsinki'])
    s.add(day_vars[1] == city_to_int['Helsinki'])
    
    # Constraint 2: Reykjavik between day 8 and day 9 (so day 8 or day 9 must be Reykjavik)
    s.add(Or(
        day_vars[7] == city_to_int['Reykjavik'],  # day 8
        day_vars[8] == city_to_int['Reykjavik']   # day 9
    ))
    
    # Constraint 3: Warsaw between day 9 and day 11 (so at least one of day 9, 10, or 11 must be Warsaw)
    s.add(Or(
        day_vars[8] == city_to_int['Warsaw'],   # day 9
        day_vars[9] == city_to_int['Warsaw'],   # day 10
        day_vars[10] == city_to_int['Warsaw']   # day 11
    ))
    
    # Flight constraints: For each consecutive day, either the city remains the same or there's a direct flight
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        same_city = current_day == next_day
        possible_flights = []
        for city1, city2 in flight_pairs:
            c1 = city_to_int[city1]
            c2 = city_to_int[city2]
            possible_flights.append(And(current_day == c1, next_day == c2))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Total days constraints for each city
    for city, required_days in cities.items():
        city_int = city_to_int[city]
        total_days = Sum([If(day_var == city_int, 1, 0) for day_var in day_vars])
        s.add(total_days == required_days)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_int = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_int]
            itinerary.append({'day': day_num, 'place': city})
        
        result = {'itinerary': itinerary}
        return result
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")