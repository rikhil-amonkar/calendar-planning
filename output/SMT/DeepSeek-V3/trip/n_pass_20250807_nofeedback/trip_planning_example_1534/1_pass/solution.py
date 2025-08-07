import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Paris', 'Venice', 'Warsaw', 'Vilnius', 'Salzburg', 'Amsterdam', 'Barcelona', 'Hamburg', 'Florence', 'Tallinn']
    
    # Direct flights as a set of tuples
    direct_flights = {
        ('Paris', 'Venice'), ('Barcelona', 'Amsterdam'), ('Amsterdam', 'Warsaw'), 
        ('Amsterdam', 'Vilnius'), ('Barcelona', 'Warsaw'), ('Warsaw', 'Venice'), 
        ('Amsterdam', 'Hamburg'), ('Barcelona', 'Hamburg'), ('Barcelona', 'Florence'), 
        ('Barcelona', 'Venice'), ('Paris', 'Hamburg'), ('Paris', 'Vilnius'), 
        ('Paris', 'Amsterdam'), ('Paris', 'Florence'), ('Florence', 'Amsterdam'), 
        ('Vilnius', 'Warsaw'), ('Barcelona', 'Tallinn'), ('Paris', 'Warsaw'), 
        ('Tallinn', 'Warsaw'), ('Tallinn', 'Vilnius'), ('Amsterdam', 'Tallinn'), 
        ('Paris', 'Tallinn'), ('Paris', 'Barcelona'), ('Venice', 'Hamburg'), 
        ('Warsaw', 'Hamburg'), ('Hamburg', 'Salzburg'), ('Amsterdam', 'Venice')
    }
    # Make flights bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights

    # Create Z3 variables for each day's city
    s = Solver()
    day_city = [Int(f'day_{i}_city') for i in range(1, 26)]  # days 1 to 25
    
    # Map each city to an integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Each day's city must be one of the 10 cities
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Duration constraints
    # Total days in each city must match the specified durations
    # Warsaw: 4 days
    s.add(Sum([If(day_city[i] == city_to_int['Warsaw'], 1, 0) for i in range(25)]) == 4)
    # Venice: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Venice'], 1, 0) for i in range(25)]) == 3)
    # Vilnius: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Vilnius'], 1, 0) for i in range(25)]) == 3)
    # Salzburg: 4 days, must include days 22-25
    s.add(Sum([If(day_city[i] == city_to_int['Salzburg'], 1, 0) for i in range(25)]) == 4)
    for i in range(21, 25):  # days 22-25 (0-based: 21-24)
        s.add(day_city[i] == city_to_int['Salzburg'])
    # Amsterdam: 2 days
    s.add(Sum([If(day_city[i] == city_to_int['Amsterdam'], 1, 0) for i in range(25)]) == 2)
    # Barcelona: 5 days, must include days 2-6 (1-5 in 0-based)
    s.add(Sum([If(day_city[i] == city_to_int['Barcelona'], 1, 0) for i in range(25)]) == 5)
    for i in range(1, 6):  # days 2-6 (0-based: 1-5)
        s.add(day_city[i] == city_to_int['Barcelona'])
    # Paris: 2 days, must include days 1-2 (0-1 in 0-based)
    s.add(Sum([If(day_city[i] == city_to_int['Paris'], 1, 0) for i in range(25)]) == 2)
    s.add(day_city[0] == city_to_int['Paris'])  # day 1
    s.add(day_city[1] == city_to_int['Paris'])  # day 2
    # Hamburg: 4 days, must include days 19-22 (18-21 in 0-based)
    s.add(Sum([If(day_city[i] == city_to_int['Hamburg'], 1, 0) for i in range(25)]) == 4)
    for i in range(18, 22):  # days 19-22 (0-based: 18-21)
        s.add(day_city[i] == city_to_int['Hamburg'])
    # Florence: 5 days
    s.add(Sum([If(day_city[i] == city_to_int['Florence'], 1, 0) for i in range(25)]) == 5)
    # Tallinn: 2 days, must include days 11-12 (10-11 in 0-based)
    s.add(Sum([If(day_city[i] == city_to_int['Tallinn'], 1, 0) for i in range(25)]) == 2)
    s.add(day_city[10] == city_to_int['Tallinn'])  # day 11
    s.add(day_city[11] == city_to_int['Tallinn'])  # day 12
    
    # Flight constraints: consecutive days must be either same city or have a direct flight
    for i in range(24):  # days 1-24 to check transition to next day
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) for (a, b) in direct_flights]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(25):
            day = i + 1
            city_idx = model.evaluate(day_city[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day, "place": city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result as JSON
result = solve_itinerary()
print(json.dumps(result, indent=2))