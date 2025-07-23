import json
from z3 import *

# Define the cities
cities = [
    "Prague",
    "Brussels",
    "Riga",
    "Munich",
    "Seville",
    "Stockholm",
    "Istanbul",
    "Amsterdam",
    "Vienna",
    "Split"
]

# Direct flights as a dictionary for quick lookup
direct_flights = {
    "Riga": ["Stockholm", "Istanbul", "Vienna", "Amsterdam", "Munich", "Brussels", "Prague"],
    "Stockholm": ["Riga", "Brussels", "Split", "Amsterdam", "Vienna", "Istanbul", "Prague", "Munich"],
    "Brussels": ["Stockholm", "Vienna", "Munich", "Riga", "Prague", "Istanbul", "Seville"],
    "Istanbul": ["Munich", "Riga", "Amsterdam", "Stockholm", "Vienna", "Brussels", "Prague"],
    "Munich": ["Istanbul", "Amsterdam", "Brussels", "Split", "Stockholm", "Riga", "Prague", "Seville", "Vienna"],
    "Amsterdam": ["Munich", "Split", "Stockholm", "Riga", "Seville", "Istanbul", "Vienna", "Prague"],
    "Vienna": ["Brussels", "Riga", "Stockholm", "Istanbul", "Seville", "Split", "Amsterdam", "Munich", "Prague"],
    "Split": ["Prague", "Stockholm", "Munich", "Amsterdam", "Vienna"],
    "Prague": ["Split", "Munich", "Amsterdam", "Brussels", "Istanbul", "Riga", "Stockholm", "Vienna"],
    "Seville": ["Brussels", "Amsterdam", "Vienna", "Munich"]
}

# Create a Z3 solver instance
s = Solver()

# Create variables for each day (1..20), each can be one of the cities
days = [Int(f"day_{i}") for i in range(1, 21)]

# Each day's variable must be between 0 and 9 (indexes of cities)
for day in days:
    s.add(day >= 0, day < len(cities))

# Function to get city index by name
def city_index(name):
    return cities.index(name)

# Constraints for total days in each city
# Prague: 5 days
s.add(Sum([If(day == city_index("Prague"), 1, 0) for day in days]) == 5)
# Brussels: 2 days
s.add(Sum([If(day == city_index("Brussels"), 1, 0) for day in days]) == 2)
# Riga: 2 days
s.add(Sum([If(day == city_index("Riga"), 1, 0) for day in days]) == 2)
# Munich: 2 days
s.add(Sum([If(day == city_index("Munich"), 1, 0) for day in days]) == 2)
# Seville: 3 days
s.add(Sum([If(day == city_index("Seville"), 1, 0) for day in days]) == 3)
# Stockholm: 2 days
s.add(Sum([If(day == city_index("Stockholm"), 1, 0) for day in days]) == 2)
# Istanbul: 2 days
s.add(Sum([If(day == city_index("Istanbul"), 1, 0) for day in days]) == 2)
# Amsterdam: 3 days
s.add(Sum([If(day == city_index("Amsterdam"), 1, 0) for day in days]) == 3)
# Vienna: 5 days
s.add(Sum([If(day == city_index("Vienna"), 1, 0) for day in days]) == 5)
# Split: 3 days
s.add(Sum([If(day == city_index("Split"), 1, 0) for day in days]) == 3)

# Specific date constraints
# Prague: day 5 to day 9 must be Prague (inclusive)
for i in range(5, 10):  # days 5,6,7,8,9
    s.add(days[i-1] == city_index("Prague"))

# Riga: meet friends between day 15 and 16. So either day 15 or 16 is Riga.
s.add(Or(days[14] == city_index("Riga"), days[15] == city_index("Riga")))

# Stockholm: conference during day 16 and 17. So day 16 and 17 must be Stockholm.
s.add(days[15] == city_index("Stockholm"))
s.add(days[16] == city_index("Stockholm"))

# Split: visit relatives between day 11 and 13. So at least one of days 11,12,13 is Split.
s.add(Or(days[10] == city_index("Split"), days[11] == city_index("Split"), days[12] == city_index("Split")))

# Vienna: meet friend between day 1 and 5. So at least one of days 1-5 is Vienna.
s.add(Or([days[i] == city_index("Vienna") for i in range(0, 5)]))

# Flight transitions: for consecutive days, either same city or direct flight.
for i in range(19):
    current_city = days[i]
    next_city = days[i+1]
    # Either same city or connected by direct flight
    same_city = current_city == next_city
    # Check if there's a direct flight between current_city and next_city
    # Create a disjunction over all possible direct flights for current_city
    current_city_name = cities[current_city.as_long()] if is_expr(current_city) else cities[current_city]
    next_city_name = cities[next_city.as_long()] if is_expr(next_city) else cities[next_city]
    # Get the list of connected cities for current_city_name
    connected_cities = direct_flights.get(current_city_name, [])
    # next_city_name must be in connected_cities or same city
    s.add(Or(same_city, next_city_name in connected_cities))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(20):
        day_num = i + 1
        city_index_val = model[days[i]].as_long()
        city = cities[city_index_val]
        itinerary.append({"day": day_num, "city": city})
    
    # Prepare the output as a JSON-formatted dictionary
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")