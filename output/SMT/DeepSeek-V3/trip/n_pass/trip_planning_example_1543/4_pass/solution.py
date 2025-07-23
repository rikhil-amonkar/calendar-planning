from z3 import *

def solve_itinerary():
    # Cities with their required visit durations
    cities = [
        ('Prague', 3),
        ('Warsaw', 4),
        ('Dublin', 3),
        ('Athens', 3),
        ('Vilnius', 4),
        ('Porto', 5),
        ('London', 3),
        ('Seville', 2),
        ('Lisbon', 5),
        ('Dubrovnik', 3)
    ]
    city_names = [city[0] for city in cities]
    city_to_idx = {name: idx for idx, name in enumerate(city_names)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Warsaw', 'Vilnius'),
        ('Prague', 'Athens'),
        ('London', 'Lisbon'),
        ('Lisbon', 'Porto'),
        ('Prague', 'Lisbon'),
        ('London', 'Dublin'),
        ('Athens', 'Vilnius'),
        ('Athens', 'Dublin'),
        ('Prague', 'London'),
        ('London', 'Warsaw'),
        ('Dublin', 'Seville'),
        ('Seville', 'Porto'),
        ('Lisbon', 'Athens'),
        ('Dublin', 'Porto'),
        ('Athens', 'Warsaw'),
        ('Lisbon', 'Warsaw'),
        ('Porto', 'Warsaw'),
        ('Prague', 'Warsaw'),
        ('Prague', 'Dublin'),
        ('Athens', 'Dubrovnik'),
        ('Lisbon', 'Dublin'),
        ('Dubrovnik', 'Dublin'),
        ('Lisbon', 'Seville'),
        ('London', 'Athens')
    ]
    
    # Create allowed transitions (both directions)
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_to_idx[a], city_to_idx[b]))
        allowed_transitions.add((city_to_idx[b], city_to_idx[a]))
    
    # Create solver with timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 second timeout
    
    # Day variables: day[i] is the city on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(26)]
    
    # Each day's value is an index into the cities list (0 to 9)
    for d in days:
        s.add(d >= 0, d < len(cities))
    
    # Fixed intervals:
    # Prague: days 1-3 (workshop)
    for i in range(3):
        s.add(days[i] == city_to_idx['Prague'])
    
    # London: days 3-5 (wedding)
    for i in range(2, 5):
        s.add(days[i] == city_to_idx['London'])
    
    # Lisbon: days 5-9 (relatives)
    for i in range(4, 9):
        s.add(days[i] == city_to_idx['Lisbon'])
    
    # Porto: days 16-20 (conference)
    for i in range(15, 20):
        s.add(days[i] == city_to_idx['Porto'])
    
    # Warsaw: days 20-23 (friends)
    for i in range(19, 23):
        s.add(days[i] == city_to_idx['Warsaw'])
    
    # Duration constraints for other cities
    for city, duration in cities:
        if city in ['Prague', 'London', 'Lisbon', 'Porto', 'Warsaw']:
            continue  # already handled
        s.add(Sum([If(days[i] == city_to_idx[city], 1, 0) for i in range(26)]) == duration)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(25):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == a, next_day == b) for a, b in allowed_transitions]
        ))
    
    # Additional constraints to help the solver:
    # 1. No immediate returns (stay at least 1 day in a city)
    for i in range(24):
        s.add(Implies(days[i] != days[i+1], days[i+1] != days[i+2]))
    
    # 2. Prefer longer stays when possible
    for i in range(23):
        s.add(Implies(
            And(days[i] != days[i+1], days[i+1] != days[i+2]),
            days[i+2] == days[i+3]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(26):
            day = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = city_names[city_idx]
            itinerary.append({"day": day, "place": city})
        
        # Verify counts
        counts = {city: 0 for city in city_names}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        print("City visit counts:")
        for city, count in counts.items():
            print(f"{city}: {count} days")
        
        return {'itinerary': itinerary}
    else:
        print("Failed to find a valid itinerary")
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(itinerary)