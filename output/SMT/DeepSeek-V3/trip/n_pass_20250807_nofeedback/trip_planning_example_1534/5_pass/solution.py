import json
from z3 import *

def solve_itinerary():
    # Cities with correct spellings
    cities = ['Paris', 'Venice', 'Warsaw', 'Vilnius', 'Salzburg', 
              'Amsterdam', 'Barcelona', 'Hamburg', 'Florence', 'Tallinn']
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Paris', 'Venice'), ('Barcelona', 'Amsterdam'), ('Amsterdam', 'Warsaw'),
        ('Amsterdam', 'Vilnius'), ('Barcelona', 'Warsaw'), ('Warsaw', 'Venice'),
        ('Amsterdam', 'Hamburg'), ('Barcelona', 'Hamburg'), ('Barcelona', 'Florence'),
        ('Barcelona', 'Venice'), ('Paris', 'Hamburg'), ('Paris', 'Vilnius'),
        ('Paris', 'Amsterdam'), ('Paris', 'Florence'), ('Florence', 'Amsterdam'),
        ('Vilnius', 'Warsaw'), ('Barcelona', 'Tallinn'), ('Paris', 'Warsaw'),
        ('Tallinn', 'Warsaw'), ('Tallinn', 'Vilnius'), ('Amsterdam', 'Tallinn'),
        ('Paris', 'Tallinn'), ('Paris', 'Barcelona'), ('Venice', 'Hamburg'),
        ('Warsaw', 'Hamburg'), ('Hamburg', 'Salzburg'), ('Amsterdam', 'Venice')
    ]
    
    # Create bidirectional flight connections
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))

    # Create solver
    s = Solver()

    # Create variables for each day's city
    day_city = [Int(f'day_{i}') for i in range(25)]  # Days 1-25 (0-based index)

    # City to integer mapping
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}

    # Each day must be assigned to a valid city
    for day in day_city:
        s.add(day >= 0, day < len(cities))

    # Duration constraints
    # Warsaw: 4 days
    s.add(Sum([If(day_city[i] == city_to_int['Warsaw'], 1, 0) for i in range(25)]) == 4)
    # Venice: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Venice'], 1, 0) for i in range(25)]) == 3)
    # Vilnius: 3 days
    s.add(Sum([If(day_city[i] == city_to_int['Vilnius'], 1, 0) for i in range(25)]) == 3)
    # Salzburg: 4 days (days 22-25 inclusive)
    s.add(Sum([If(day_city[i] == city_to_int['Salzburg'], 1, 0) for i in range(25)]) == 4)
    for i in range(21, 25):  # Days 22-25 (0-based 21-24)
        s.add(day_city[i] == city_to_int['Salzburg'])
    # Amsterdam: 2 days
    s.add(Sum([If(day_city[i] == city_to_int['Amsterdam'], 1, 0) for i in range(25)]) == 2)
    # Barcelona: 5 days (days 2-6 inclusive)
    s.add(Sum([If(day_city[i] == city_to_int['Barcelona'], 1, 0) for i in range(25)]) == 5)
    for i in range(1, 6):  # Days 2-6 (0-based 1-5)
        s.add(day_city[i] == city_to_int['Barcelona'])
    # Paris: 2 days (days 1-2 inclusive)
    s.add(Sum([If(day_city[i] == city_to_int['Paris'], 1, 0) for i in range(25)]) == 2)
    s.add(day_city[0] == city_to_int['Paris'])  # Day 1
    s.add(day_city[1] == city_to_int['Paris'])  # Day 2
    # Hamburg: 4 days (days 19-22 inclusive)
    s.add(Sum([If(day_city[i] == city_to_int['Hamburg'], 1, 0) for i in range(25)]) == 4)
    for i in range(18, 22):  # Days 19-22 (0-based 18-21)
        s.add(day_city[i] == city_to_int['Hamburg'])
    # Florence: 5 days
    s.add(Sum([If(day_city[i] == city_to_int['Florence'], 1, 0) for i in range(25)]) == 5)
    # Tallinn: 2 days (days 11-12 inclusive)
    s.add(Sum([If(day_city[i] == city_to_int['Tallinn'], 1, 0) for i in range(25)]) == 2)
    s.add(day_city[10] == city_to_int['Tallinn'])  # Day 11
    s.add(day_city[11] == city_to_int['Tallinn'])  # Day 12

    # Flight constraints between consecutive days
    for i in range(24):  # Check transitions between days 1-24 and 2-25
        current = day_city[i]
        next_day = day_city[i+1]
        
        # Create OR condition for all possible flight connections
        flight_options = []
        for city_a, city_b in flight_connections:
            flight_options.append(And(
                current == city_to_int[city_a],
                next_day == city_to_int[city_b]
            ))
        
        # Can either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,  # Stay in same city
            *flight_options       # Or take a direct flight
        ))

    # Check if solution exists
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

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))