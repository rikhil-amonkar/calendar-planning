import json
from z3 import *

# Define the cities
cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]

# Direct flights as a set of tuples
direct_flights = {
    ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"), ("Reykjavik", "Oslo"),
    ("Bucharest", "Munich"), ("Oslo", "Frankfurt"), ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"),
    ("Reykjavik", "Frankfurt"), ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
    ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"), ("Split", "Stockholm"),
    ("Barcelona", "Oslo"), ("Stockholm", "Munich"), ("Stockholm", "Oslo"), ("Split", "Frankfurt"),
    ("Barcelona", "Munich"), ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
}

# Make sure flights are bidirectional
bidirectional_flights = set()
for (a, b) in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))
direct_flights = bidirectional_flights

# Create a Z3 solver
s = Solver()

# Variables: day_1 to day_20, each can be one of the cities
days = [Int(f"day_{i}") for i in range(1, 21)]
for day in days:
    s.add(day >= 0, day < len(cities))

# Helper function to get city index
def city_index(city):
    return cities.index(city)

# Constraints for durations
# Oslo: 2 days (including the days 16-17)
s.add(Sum([If(days[i] == city_index("Oslo"), 1, 0) for i in range(20)]) == 2)
# Reykjavik: 5 days
s.add(Sum([If(days[i] == city_index("Reykjavik"), 1, 0) for i in range(20)]) == 5)
# Stockholm: 4 days
s.add(Sum([If(days[i] == city_index("Stockholm"), 1, 0) for i in range(20)]) == 4)
# Munich: 4 days
s.add(Sum([If(days[i] == city_index("Munich"), 1, 0) for i in range(20)]) == 4)
# Frankfurt: 4 days
s.add(Sum([If(days[i] == city_index("Frankfurt"), 1, 0) for i in range(20)]) == 4)
# Barcelona: 3 days
s.add(Sum([If(days[i] == city_index("Barcelona"), 1, 0) for i in range(20)]) == 3)
# Bucharest: 2 days
s.add(Sum([If(days[i] == city_index("Bucharest"), 1, 0) for i in range(20)]) == 2)
# Split: 3 days
s.add(Sum([If(days[i] == city_index("Split"), 1, 0) for i in range(20)]) == 3)

# Specific constraints
# Oslo must be on day 16 and 17 (0-based: days 15 and 16)
s.add(days[15] == city_index("Oslo"))
s.add(days[16] == city_index("Oslo"))

# Reykjavik between day 9 and 13 (1-based: days 9-13 are indices 8-12)
s.add(Or([days[i] == city_index("Reykjavik") for i in range(8, 13)]))

# Munich between day 13 and 16 (indices 12-15)
s.add(Or([days[i] == city_index("Munich") for i in range(12, 16)]))

# Frankfurt between day 17 and 20 (indices 16-19)
s.add(Or([days[i] == city_index("Frankfurt") for i in range(16, 20)]))

# Flight constraints: consecutive days must be either same city or have a direct flight
for i in range(19):
    current_day = days[i]
    next_day = days[i+1]
    # Either stay in the same city or move to a directly connected city
    s.add(Or(
        current_day == next_day,
        Or([And(current_day == city_index(a), next_day == city_index(b)) 
            for (a, b) in direct_flights])
    ))

# Check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(20):
        day_num = i + 1
        city_idx = m.evaluate(days[i]).as_long()
        city = cities[city_idx]
        itinerary.append({"day": day_num, "place": city})
    
    # Prepare the output JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")