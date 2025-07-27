import json
from z3 import *

# Define the cities and their codes for easier reference
cities = {
    'Bucharest': 0,
    'Venice': 1,
    'Prague': 2,
    'Frankfurt': 3,
    'Zurich': 4,
    'Florence': 5,
    'Tallinn': 6
}

# Inverse mapping for output
city_names = {v: k for k, v in cities.items()}

# Direct flights: adjacency list
direct_flights = {
    0: [3, 2, 4],  # Bucharest: Frankfurt, Prague, Zurich
    1: [3, 4],      # Venice: Frankfurt, Zurich
    2: [6, 4, 5, 3, 0],  # Prague: Tallinn, Zurich, Florence, Frankfurt, Bucharest
    3: [0, 1, 6, 4, 5, 2],  # Frankfurt: Bucharest, Venice, Tallinn, Zurich, Florence, Prague
    4: [2, 0, 1, 5, 3, 6],   # Zurich: Prague, Bucharest, Venice, Florence, Frankfurt, Tallinn
    5: [2, 3, 4],   # Florence: Prague, Frankfurt, Zurich
    6: [2, 3, 4]    # Tallinn: Prague, Frankfurt, Zurich
}

# Total days
total_days = 26

# Create a Z3 solver instance
solver = Solver()

# Create variables: day_1 to day_26, each can be 0-6 representing the city
days = [Int(f'day_{i}') for i in range(1, total_days + 1)]

# Constraint: each day variable must be between 0 and 6
for day in days:
    solver.add(day >= 0, day <= 6)

# Fixed constraints:
# Venice must be days 22-26
for day in range(22, 27):
    solver.add(days[day - 1] == cities['Venice'])

# Frankfurt must be days 12-16
for day in range(12, 17):
    solver.add(days[day - 1] == cities['Frankfurt'])

# Tallinn must be days 8-12
for day in range(8, 13):
    solver.add(days[day - 1] == cities['Tallinn'])

# Ensure transitions are via direct flights
for i in range(total_days - 1):
    current_city = days[i]
    next_city = days[i + 1]
    # Create a condition that next_city is either the same as current_city or a direct flight exists
    solver.add(Or(
        current_city == next_city,
        And(
            current_city != next_city,
            Or([And(current_city == city_code, Or([next_city == neighbor for neighbor in direct_flights[city_code]])) for city_code in direct_flights])
        )
    ))

# Count days per city
city_days = {city: 0 for city in cities}
for city in cities:
    count = 0
    for day in days:
        count += If(day == cities[city], 1, 0)
    solver.add(count == {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }[city])

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(total_days):
        city_code = model.evaluate(days[i]).as_long()
        city_name = city_names[city_code]
        itinerary.append({"day": i + 1, "place": city_name})
    
    # Output the itinerary in JSON format
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")