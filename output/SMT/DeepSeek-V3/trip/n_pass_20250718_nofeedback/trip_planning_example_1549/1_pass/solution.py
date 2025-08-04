import json
from z3 import *

# Define the cities and their required days
cities = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

# Flight connections as a dictionary: each city maps to a list of directly connected cities
flight_connections = {
    "Riga": ["Prague", "Milan", "Tallinn", "Warsaw", "Stockholm", "Lisbon"],
    "Stockholm": ["Milan", "Lisbon", "Warsaw", "Riga", "Santorini", "Prague", "Tallinn"],
    "Milan": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Lisbon", "Santorini", "Warsaw"],
    "Lisbon": ["Stockholm", "Warsaw", "Naples", "Riga", "Porto", "Prague", "Milan"],
    "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
    "Warsaw": ["Naples", "Lisbon", "Stockholm", "Riga", "Porto", "Tallinn", "Milan", "Prague"],
    "Porto": ["Lisbon", "Milan", "Warsaw"],
    "Prague": ["Riga", "Tallinn", "Stockholm", "Lisbon", "Milan", "Warsaw"],
    "Tallinn": ["Riga", "Prague", "Stockholm", "Warsaw"],
    "Santorini": ["Stockholm", "Milan", "Naples"]
}

# Create a Z3 solver instance
s = Solver()

# Create a list of city names for easier reference
city_names = list(cities.keys())

# Create a dictionary to map city names to their indices
city_index = {city: idx for idx, city in enumerate(city_names)}

# Create variables for each day: day[i] is the city visited on day i+1 (since days are 1-based)
days = [Int(f"day_{i+1}") for i in range(28)]

# Constraint: each day's value must be a valid city index (0 to 9)
for day in days:
    s.add(day >= 0, day < len(city_names))

# Constraint: total days per city must match the requirements
for city, count in cities.items():
    idx = city_index[city]
    s.add(Sum([If(day == idx, 1, 0) for day in days]) == count)

# Specific constraints:
# 1. Spend 5 days in Prague.
# 2. Tallinn for 3 days, between day 18 and day 20 (inclusive) for relatives.
#   So at least one of days 18, 19, 20 must be Tallinn.
#   But since the total is 3 days, likely more.
s.add(Or([days[17] == city_index["Tallinn"], days[18] == city_index["Tallinn"], days[19] == city_index["Tallinn"]]))

# 3. Warsaw for 2 days.
# 4. Porto for 3 days.
# 5. Naples for 5 days.
# 6. Milan for 3 days, with a friend between day 24-26 (days 23, 24, 25 in 0-based).
s.add(Or([days[23] == city_index["Milan"], days[24] == city_index["Milan"], days[25] == city_index["Milan"]]))

# 7. Lisbon for 5 days.
# 8. Santorini for 5 days.
# 9. Riga for 4 days, with annual show from day 5 to day 8 (days 4 to 7 in 0-based).
for i in range(4, 8):
    s.add(days[i] == city_index["Riga"])

# 10. Stockholm for 2 days.

# Flight constraints: consecutive days must be same city or have a direct flight.
for i in range(27):
    current_city = days[i]
    next_city = days[i+1]
    # Either stay in the same city or move to a connected city
    s.add(Or(
        current_city == next_city,
        # Check if there's a flight from current_city to next_city
        *[And(current_city == city_index[a], next_city == city_index[b]) 
          for a in flight_connections for b in flight_connections[a]
          if a in flight_connections and b in flight_connections[a]
        )
    )

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(28):
        day = i + 1
        city_idx = model.evaluate(days[i]).as_long()
        city = city_names[city_idx]
        itinerary.append({"day": day, "place": city})
    
    # Convert to the required JSON format
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")