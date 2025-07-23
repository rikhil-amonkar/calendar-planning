from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
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
    
    # Create a set of allowed transitions (both directions)
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_to_idx[a], city_to_idx[b]))
        allowed_transitions.add((city_to_idx[b], city_to_idx[a]))
    
    # Create solver
    s = Solver()
    
    # Day variables: day[i] is the city on day i+1 (since days are 1-based)
    days = [Int('day_%d' % i) for i in range(26)]
    
    # Each day's value is an index into the cities list (0 to 9)
    for d in days:
        s.add(And(d >= 0, d < len(cities)))
    
    # Fixed intervals:
    # Prague: 3 days, including workshop between day 1 and 3 (must be days 1-3)
    s.add(days[0] == city_to_idx['Prague'])
    s.add(days[1] == city_to_idx['Prague'])
    s.add(days[2] == city_to_idx['Prague'])
    
    # London: wedding between day 3 and 5 (days 3-5)
    s.add(days[2] == city_to_idx['London'])
    s.add(days[3] == city_to_idx['London'])
    s.add(days[4] == city_to_idx['London'])
    
    # Lisbon: relatives between day 5 and 9 (5 days)
    for i in range(4, 9):
        s.add(days[i] == city_to_idx['Lisbon'])
    
    # Porto: conference between day 16 and 20 (5 days)
    for i in range(15, 20):
        s.add(days[i] == city_to_idx['Porto'])
    
    # Warsaw: meet friends between day 20 and 23 (4 days)
    for i in range(19, 23):
        s.add(days[i] == city_to_idx['Warsaw'])
    
    # Other durations:
    # Dublin: 3 days total
    s.add(Sum([If(days[i] == city_to_idx['Dublin'], 1, 0) for i in range(26)]) == 3)
    # Athens: 3 days
    s.add(Sum([If(days[i] == city_to_idx['Athens'], 1, 0) for i in range(26)]) == 3)
    # Vilnius: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Vilnius'], 1, 0) for i in range(26)]) == 4)
    # Dubrovnik: 3 days
    s.add(Sum([If(days[i] == city_to_idx['Dubrovnik'], 1, 0) for i in range(26)]) == 3)
    # Seville: 2 days
    s.add(Sum([If(days[i] == city_to_idx['Seville'], 1, 0) for i in range(26)]) == 2)
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(25):
        current_city = days[i]
        next_city = days[i+1]
        # Constraint: (current_city == next_city) OR (current_city, next_city) in allowed_transitions
        s.add(Or(
            current_city == next_city,
            *[And(current_city == a, next_city == b) for (a, b) in allowed_transitions]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(26):
            day = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day, "place": city})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        print("City counts:")
        for city in counts:
            print(f"{city}: {counts[city]}")
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)