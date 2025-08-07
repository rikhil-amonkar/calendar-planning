import json
from z3 import *

# Define cities and their codes
cities = {
    'Stuttgart': 0,
    'Edinburgh': 1,
    'Athens': 2,
    'Split': 3,
    'Krakow': 4,
    'Venice': 5,
    'Mykonos': 6
}
city_names = {v: k for k, v in cities.items()}

# Flight connections (bidirectional)
flight_pairs = [
    (0,1), (0,2), (0,3), (0,4), (0,5),  # Stuttgart
    (1,4), (1,5),                       # Edinburgh
    (2,3), (2,5), (2,6),                # Athens
    (3,4),                               # Split
    (4,0),                               # Krakow
    (5,6),                               # Venice
    (6,2)                                # Mykonos
]

# Make flights bidirectional
all_flights = flight_pairs + [(b,a) for (a,b) in flight_pairs]

# Create solver
s = Solver()

# Day variables (1-20)
days = [Int(f'day_{i}') for i in range(20)]

# City must be valid (0-6)
for d in days:
    s.add(And(d >= 0, d <= 6))

# Flight constraints
for i in range(19):
    current = days[i]
    next_day = days[i+1]
    # Can stay or take a direct flight
    options = [current == next_day]
    for (a,b) in all_flights:
        options.append(And(current == a, next_day == b))
    s.add(Or(options))

# Total days per city
city_days = {
    0: 3,  # Stuttgart
    1: 4,  # Edinburgh
    2: 4,  # Athens
    3: 2,  # Split
    4: 4,  # Krakow
    5: 5,  # Venice
    6: 4   # Mykonos
}

for city, total in city_days.items():
    s.add(Sum([If(d == city, 1, 0) for d in days]) == total)

# Workshop in Stuttgart (days 11-13)
s.add(Or(days[10] == 0, days[11] == 0, days[12] == 0))

# Meet in Split (days 13-14)
s.add(Or(days[12] == 3, days[13] == 3))

# Meet in Krakow (days 8-11)
s.add(Or([days[i] == 4 for i in range(7,11)]))

# Try to find solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(20):
        city_code = model.eval(days[i]).as_long()
        itinerary.append({"day": i+1, "place": city_names[city_code]})
    
    # Verify constraints
    print("Verifying constraints...")
    city_counts = {name:0 for name in cities}
    for entry in itinerary:
        city_counts[entry['place']] += 1
    
    print("City day counts:")
    for city, count in city_counts.items():
        print(f"{city}: {count} days (target: {city_days[cities[city]]})")
    
    print("\nWorkshop in Stuttgart (days 11-13):", 
          any(11 <= entry['day'] <= 13 and entry['place'] == 'Stuttgart' for entry in itinerary))
    print("Meet in Split (days 13-14):",
          any(13 <= entry['day'] <= 14 and entry['place'] == 'Split' for entry in itinerary))
    print("Meet in Krakow (days 8-11):",
          any(8 <= entry['day'] <= 11 and entry['place'] == 'Krakow' for entry in itinerary))
    
    output = {'itinerary': itinerary}
    print("\nFinal itinerary:")
    print(json.dumps(output, indent=2))
else:
    print("No solution found - trying alternative approach...")
    # If no solution, try relaxing some constraints
    s.reset()
    # Re-add basic constraints
    for d in days:
        s.add(And(d >= 0, d <= 6))
    for i in range(19):
        current = days[i]
        next_day = days[i+1]
        options = [current == next_day]
        for (a,b) in all_flights:
            options.append(And(current == a, next_day == b))
        s.add(Or(options))
    
    # Keep mandatory events but be flexible with day counts
    s.add(Or(days[10] == 0, days[11] == 0, days[12] == 0))
    s.add(Or(days[12] == 3, days[13] == 3))
    s.add(Or([days[i] == 4 for i in range(7,11)]))
    
    # Make day counts soft constraints
    for city, total in city_days.items():
        s.add_soft(Sum([If(d == city, 1, 0) for d in days]) == total)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_code = model.eval(days[i]).as_long()
            itinerary.append({"day": i+1, "place": city_names[city_code]})
        output = {'itinerary': itinerary}
        print("\nAlternative solution (some constraints relaxed):")
        print(json.dumps(output, indent=2))
    else:
        print("Still no solution found - problem may be over-constrained")