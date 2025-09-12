from z3 import *
import json

# Define cities and their required durations
cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
durations = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5,
}

# Direct flights between cities
direct_flights = {
    ("Bucharest", "Manchester"), ("Munich", "Venice"), ("Santorini", "Manchester"), ("Vienna", "Reykjavik"), 
    ("Venice", "Santorini"), ("Munich", "Porto"), ("Valencia", "Vienna"), ("Manchester", "Vienna"), ("Porto", "Vienna"), 
    ("Venice", "Manchester"), ("Santorini", "Vienna"), ("Munich", "Manchester"), ("Munich", "Reykjavik"), 
    ("Bucharest", "Valencia"), ("Venice", "Vienna"), ("Bucharest", "Vienna"), ("Porto", "Manchester"), 
    ("Munich", "Vienna"), ("Valencia", "Porto"), ("Munich", "Bucharest"), ("Tallinn", "Munich"), 
    ("Santorini", "Bucharest"), ("Munich", "Valencia")
}

# Create Z3 solver
s = Solver()

# Variables for the order of cities (as indices)
order = [Int(f"order_{i}") for i in range(10)]
# Constraints: each city is visited exactly once
s.add(Distinct(order))
for i in range(10):
    s.add(And(0 <= order[i], order[i] < 10))

# Variables for start days of each city in the order
start_days = [Int(f"start_day_{i}") for i in range(10)]

# The first start day is 1
s.add(start_days[0] == 1)

# Define start_days for subsequent cities based on previous durations
for i in range(1, 10):
    # Get the index of the previous city in the order
    prev_city_index = order[i-1]
    # Get the duration of the previous city
    prev_duration = durations[cities[prev_city_index]]
    # The start day of the current city is the end day of the previous city + 1
    # end day of previous city is start_days[i-1] + prev_duration - 1
    # So start_days[i] = start_days[i-1] + prev_duration
    s.add(start_days[i] == start_days[i-1] + prev_duration)

# Add direct flight constraints between consecutive cities
for i in range(9):
    current_city_index = order[i]
    next_city_index = order[i+1]
    current_city = cities[current_city_index]
    next_city = cities[next_city_index]
    s.add(Or(
        (current_city, next_city) in direct_flights,
        (next_city, current_city) in direct_flights
    ))

# Add constraints for specific cities and days
# Munich must be visited from day 4 to 6
m_index = cities.index("Munich")
m_duration = durations["Munich"]
for i in range(10):
    city_index = order[i]
    is_munich = If(city_index == m_index, 1, 0)
    s.add(If(
        is_munich == 1,
        And(
            start_days[i] <= 4,
            start_days[i] + m_duration - 1 >= 6
        ),
        True
    ))

# Santorini must include days 8-10
sant_index = cities.index("Santorini")
sant_duration = durations["Santorini"]
for i in range(10):
    city_index = order[i]
    is_santorini = If(city_index == sant_index, 1, 0)
    s.add(If(
        is_santorini == 1,
        And(
            start_days[i] <= 8,
            start_days[i] + sant_duration - 1 >= 10
        ),
        True
    ))

# Valencia must include days 14-15
val_index = cities.index("Valencia")
val_duration = durations["Valencia"]
for i in range(10):
    city_index = order[i]
    is_valencia = If(city_index == val_index, 1, 0)
    s.add(If(
        is_valencia == 1,
        And(
            start_days[i] <= 14,
            start_days[i] + val_duration - 1 >= 15
        ),
        True
    ))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    # Extract the order of cities
    order_values = [model.evaluate(order[i]).as_long() for i in range(10)]
    # Extract start days
    start_day_values = [model.evaluate(start_days[i]).as_long() for i in range(10)]
    # Build the itinerary
    itinerary = []
    for i in range(10):
        city_index = order_values[i]
        city = cities[city_index]
        start = start_day_values[i]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))