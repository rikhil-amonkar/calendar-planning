import json
from z3 import *

# Define the cities and their required days
cities = {
    "Lyon": 3,
    "Paris": 5,
    "Riga": 2,
    "Berlin": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

# Direct flights as a set of tuples (correcting any typos in city names)
direct_flights_input = {
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),  # Typo: "Naples"
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),  # Typo: "Lyon"
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),  # Typo: "Zurich"
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples"),
    ("Berlin", "Nice")
}

# Correct any typos in the flight data
corrected_flights = set()
for (a, b) in direct_flights_input:
    a_corrected = a.replace("Milan", "Milan").replace("Zurich", "Zurich").replace("Naples", "Naples").replace("Lyon", "Lyon")
    b_corrected = b.replace("Milan", "Milan").replace("Zurich", "Zurich").replace("Naples", "Naples").replace("Lyon", "Lyon")
    corrected_flights.add((a_corrected, b_corrected))

# Ensure flights are bidirectional
expanded_flights = set()
for (a, b) in corrected_flights:
    expanded_flights.add((a, b))
    expanded_flights.add((b, a))
direct_flights = expanded_flights

# Create a list of city names for Z3
city_names = sorted(cities.keys())
n_days = 23

# Initialize Z3 solver
s = Solver()

# Create variables: day_1 to day_23, each can be one of the cities
day_vars = [Int(f"day_{i}") for i in range(1, n_days + 1)]

# Each day variable must be between 0 and len(city_names) - 1 (representing city_names[index])
for day in day_vars:
    s.add(day >= 0, day < len(city_names))

# Function to get city name from index
def city_index(city):
    return city_names.index(city)

# Add constraints for each city's total days
for city, days in cities.items():
    idx = city_index(city)
    s.add(Sum([If(day_vars[i] == idx, 1, 0) for i in range(n_days)]) == days)

# Flight constraints: consecutive days must be either same city or connected by a direct flight
for i in range(n_days - 1):
    current_day = day_vars[i]
    next_day = day_vars[i + 1]
    # The constraint is that either cities are the same, or (city_names[current_day], city_names[next_day]) is in direct_flights
    same_city = (current_day == next_day)
    flight_possible = Or([And(current_day == city_index(a), next_day == city_index(b)) for (a, b) in direct_flights])
    s.add(Or(same_city, flight_possible))

# Add event constraints
# Wedding in Berlin between day 1 and day 2: so day 1 and day 2 are Berlin
s.add(day_vars[0] == city_index("Berlin"))
s.add(day_vars[1] == city_index("Berlin"))

# Workshop in Nice between day 12 and day 13: one of these days is Nice
s.add(Or(day_vars[11] == city_index("Nice"), day_vars[12] == city_index("Nice")))

# Annual show in Stockholm from day 20 to day 22 (inclusive)
s.add(day_vars[19] == city_index("Stockholm"))
s.add(day_vars[20] == city_index("Stockholm"))
s.add(day_vars[21] == city_index("Stockholm"))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(n_days):
        city_idx = model.evaluate(day_vars[i]).as_long()
        itinerary.append({"day": i + 1, "place": city_names[city_idx]})
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")