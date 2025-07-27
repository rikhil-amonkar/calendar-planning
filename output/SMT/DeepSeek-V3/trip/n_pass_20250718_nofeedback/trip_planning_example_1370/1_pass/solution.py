from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Paris', 'Krakow'), ('Paris', 'Amsterdam'), ('Paris', 'Split'),
        ('Vilnius', 'Munich'), ('Paris', 'Geneva'), ('Amsterdam', 'Geneva'),
        ('Munich', 'Split'), ('Split', 'Krakow'), ('Munich', 'Amsterdam'),
        ('Budapest', 'Amsterdam'), ('Split', 'Geneva'), ('Vilnius', 'Split'),
        ('Munich', 'Geneva'), ('Munich', 'Krakow'), ('Krakow', 'Vilnius'),
        ('Vilnius', 'Amsterdam'), ('Budapest', 'Paris'), ('Krakow', 'Amsterdam'),
        ('Vilnius', 'Paris'), ('Budapest', 'Geneva'), ('Split', 'Amsterdam'),
        ('Santorini', 'Geneva'), ('Amsterdam', 'Santorini'), ('Munich', 'Budapest'),
        ('Munich', 'Paris')
    ]
    
    # Create a set of bidirectional flight connections
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))
    
    # Number of days
    days = 30
    
    # Create Z3 variables: day[i] is the city visited on day i+1 (0-based)
    day = [Int(f'day_{i}') for i in range(days)]
    
    s = Solver()
    
    # Each day must be one of the cities (0 to 8)
    for d in day:
        s.add(And(d >= 0, d < len(cities)))
    
    # Flight transitions: consecutive days must be connected by a flight or same city
    for i in range(days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_map[a], next_city == city_map[b])
                for a, b in flight_connections
            ]
        ))
    
    # Duration constraints
    # Santorini: 5 days
    s.add(Sum([If(day[i] == city_map['Santorini'], 1, 0) for i in range(days)]) == 5)
    # Santorini between day 25-29 (1-based, so 24-28 in 0-based)
    s.add(Or(*[day[i] == city_map['Santorini'] for i in range(24, 29)]))
    
    # Krakow: 5 days
    s.add(Sum([If(day[i] == city_map['Krakow'], 1, 0) for i in range(days)]) == 5)
    # Krakow wedding between day 18-22 (17-21 in 0-based)
    s.add(Or(*[day[i] == city_map['Krakow'] for i in range(17, 22)]))
    
    # Paris: 5 days
    s.add(Sum([If(day[i] == city_map['Paris'], 1, 0) for i in range(days)]) == 5)
    # Paris friend between day 11-15 (10-14 in 0-based)
    s.add(Or(*[day[i] == city_map['Paris'] for i in range(10, 15)]))
    
    # Vilnius: 3 days
    s.add(Sum([If(day[i] == city_map['Vilnius'], 1, 0) for i in range(days)]) == 3)
    
    # Munich: 5 days
    s.add(Sum([If(day[i] == city_map['Munich'], 1, 0) for i in range(days)]) == 5)
    
    # Geneva: 2 days
    s.add(Sum([If(day[i] == city_map['Geneva'], 1, 0) for i in range(days)]) == 2)
    
    # Amsterdam: 4 days
    s.add(Sum([If(day[i] == city_map['Amsterdam'], 1, 0) for i in range(days)]) == 4)
    
    # Budapest: 5 days
    s.add(Sum([If(day[i] == city_map['Budapest'], 1, 0) for i in range(days)]) == 5)
    
    # Split: 4 days
    s.add(Sum([If(day[i] == city_map['Split'], 1, 0) for i in range(days)]) == 4)
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day[i]).as_long()
            itinerary.append({'day': i+1, 'place': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return None

# Generate and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(itinerary)
else:
    print("No valid itinerary found.")