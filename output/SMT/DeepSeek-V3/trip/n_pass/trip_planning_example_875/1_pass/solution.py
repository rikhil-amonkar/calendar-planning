import json
from z3 import *

# Define the cities and their codes for easier reference
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

# Direct flights: adjacency list
direct_flights = {
    0: [3, 4, 1, 2, 5],  # Stuttgart: Split, Krakow, Edinburgh, Athens, Venice
    1: [4, 0, 2, 5],     # Edinburgh: Krakow, Stuttgart, Athens, Venice
    2: [3, 0, 1, 5, 6],  # Athens: Split, Stuttgart, Edinburgh, Venice, Mykonos
    3: [4, 2, 0],        # Split: Krakow, Athens, Stuttgart
    4: [3, 1, 0],        # Krakow: Split, Edinburgh, Stuttgart
    5: [0, 1, 2],        # Venice: Stuttgart, Edinburgh, Athens
    6: [2]               # Mykonos: Athens
}

# Create a Z3 solver
s = Solver()

# Variables: day[i] is the city visited on day i+1 (since days are 1-based)
days = [Int(f'day_{i}') for i in range(20)]

# Constraint: each day must be a valid city (0 to 6)
for d in days:
    s.add(And(d >= 0, d <= 6))

# Constraint: flights are only between connected cities
for i in range(19):
    current_city = days[i]
    next_city = days[i+1]
    # Allow staying in the same city or moving to a connected city
    s.add(Or(
        current_city == next_city,
        Or([next_city == j for j in direct_flights[current_city]])
    ))

# Total days per city constraints
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

# Workshop in Stuttgart between day 11 and 13 (1-based, days 10-12 in 0-based)
s.add(Or(
    days[10] == 0,
    days[11] == 0,
    days[12] == 0
))

# Meet friends in Split between day 13 and 14 (0-based: 12 and 13)
s.add(Or(
    days[12] == 3,
    days[13] == 3
))

# Meet friend in Krakow between day 8 and 11 (0-based: 7-10)
s.add(Or([days[i] == 4 for i in range(7, 11)]))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(20):
        city_code = model.eval(days[i]).as_long()
        itinerary.append({"day": i+1, "place": city_names[city_code]})
    
    # Verify constraints are met (debugging)
    # Convert itinerary to day-place dictionary for verification
    day_place = {entry['day']: entry['place'] for entry in itinerary}
    
    # Check Stuttgart workshop days (11-13)
    stuttgart_days = [day for day, place in day_place.items() if place == 'Stuttgart']
    workshop_ok = any(11 <= day <= 13 for day in stuttgart_days)
    
    # Check Split meeting days (13-14)
    split_days = [day for day, place in day_place.items() if place == 'Split']
    split_meeting_ok = any(13 <= day <= 14 for day in split_days)
    
    # Check Krakow meeting days (8-11)
    krakow_days = [day for day, place in day_place.items() if place == 'Krakow']
    krakow_meeting_ok = any(8 <= day <= 11 for day in krakow_days)
    
    # Check total days per city
    city_counts = {}
    for city in city_names.values():
        city_counts[city] = sum(1 for place in day_place.values() if place == city)
    
    # Print verification (optional)
    print("Verification:")
    print(f"Stuttgart days: {stuttgart_days}, Workshop between 11-13: {workshop_ok}")
    print(f"Split days: {split_days}, Meeting between 13-14: {split_meeting_ok}")
    print(f"Krakow days: {krakow_days}, Meeting between 8-11: {krakow_meeting_ok}")
    print("City day counts:", city_counts)
    
    # Prepare the output
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")