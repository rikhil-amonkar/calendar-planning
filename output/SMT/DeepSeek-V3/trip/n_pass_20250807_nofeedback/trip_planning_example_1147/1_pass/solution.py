import json
from z3 import *

# Define the cities and their required days
cities = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,
    "Milan": 4,
    "Vilnius": 5,
    "Frankfurt": 3
}

# Direct flights as per the problem statement, adjusted to match city names in 'cities'
direct_flights = [
    ("Milan", "Frankfurt"),
    ("Split", "Frankfurt"),
    ("Milan", "Split"),
    ("Brussels", "Vilnius"),
    ("Brussels", "Helsinki"),
    ("Istanbul", "Brussels"),
    ("Milan", "Vilnius"),
    ("Brussels", "Milan"),
    ("Istanbul", "Helsinki"),
    ("Helsinki", "Vilnius"),
    ("Helsinki", "Dubrovnik"),
    ("Split", "Vilnius"),
    ("Dubrovnik", "Istanbul"),
    ("Istanbul", "Milan"),
    ("Helsinki", "Frankfurt"),
    ("Istanbul", "Vilnius"),
    ("Split", "Helsinki"),
    ("Milan", "Helsinki"),
    ("Istanbul", "Frankfurt"),
    ("Brussels", "Frankfurt"),
    ("Dubrovnik", "Frankfurt"),
    ("Frankfurt", "Vilnius")
]

# Correct any typos in the flight list to match 'cities' keys
corrected_flights = set()
for city1, city2 in direct_flights:
    # Standardize city names
    c1 = city1.replace("Brussels", "Brussels").replace("Helsinki", "Helsinki")
    c2 = city2.replace("Brussels", "Brussels").replace("Helsinki", "Helsinki")
    if c1 in cities and c2 in cities:
        corrected_flights.add((c1, c2))
    else:
        # Handle cases like "Brussels" -> "Brussels" or others
        pass  # assuming no other typos

direct_flights = corrected_flights

# Create a Z3 solver instance
s = Solver()

# Create variables for each day: day_1 to day_22, each can be one of the possible cities
possible_cities = list(cities.keys())
city_indices = {city: idx for idx, city in enumerate(possible_cities)}
days = [Int(f"day_{i}") for i in range(1, 23)]  # days 1 to 22

# Add constraints that each day variable is within the possible cities (represented by their indices)
for day in days:
    s.add(Or([day == city_indices[city] for city in possible_cities]))

# Add constraints for the required days in each city
for city in possible_cities:
    required_days = cities[city]
    s.add(Sum([If(day == city_indices[city], 1, 0) for day in days]) == required_days)

# Add constraints for specific events:
# Istanbul from day 1 to 5
for day in days[:5]:
    s.add(day == city_indices["Istanbul"])

# Vilnius between day 18 and 22 (inclusive). The total days must be 5, so likely all these days.
# But the workshop is between day 18-22, so at least one day in this range must be Vilnius.
s.add(Or([days[i] == city_indices["Vilnius"] for i in range(17, 22)]))

# Wedding in Frankfurt between day 16 and 18: at least one of days 16, 17, or 18 is Frankfurt.
s.add(Or([days[i] == city_indices["Frankfurt"] for i in range(15, 18)]))

# Flight connectivity: for each consecutive day, either stay in the same city or move to a directly connected city.
for i in range(len(days) - 1):
    current_day = days[i]
    next_day = days[i+1]
    # Either stay in the same city or move to a connected city
    same_city = current_day == next_day
    connected = Or([
        And(current_day == city_indices[city1], next_day == city_indices[city2])
        for city1, city2 in direct_flights
    ] + [
        And(current_day == city_indices[city2], next_day == city_indices[city1])
        for city1, city2 in direct_flights
    ])
    s.add(Or(same_city, connected))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(1, 23):
        day_var = days[i-1]
        city_index = model.evaluate(day_var).as_long()
        city = possible_cities[city_index]
        itinerary.append({"day": i, "place": city})
    
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")