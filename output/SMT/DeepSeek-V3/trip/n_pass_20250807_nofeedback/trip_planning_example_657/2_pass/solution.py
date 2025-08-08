from z3 import *

# Define the cities
cities = {
    "Frankfurt": 0,
    "Manchester": 1,
    "Valencia": 2,
    "Naples": 3,
    "Oslo": 4,
    "Vilnius": 5
}

# Inverse mapping for city names
city_names = {v: k for k, v in cities.items()}

# Direct flights: list of tuples (city1, city2)
direct_flights = [
    ("Valencia", "Frankfurt"),
    ("Manchester", "Frankfurt"),
    ("Naples", "Manchester"),
    ("Naples", "Frankfurt"),
    ("Naples", "Oslo"),
    ("Oslo", "Frankfurt"),
    ("Vilnius", "Frankfurt"),
    ("Oslo", "Vilnius"),
    ("Manchester", "Oslo"),
    ("Valencia", "Naples")
]

# Convert direct flights to indices
flight_pairs = []
for a, b in direct_flights:
    flight_pairs.append((cities[a], cities[b]))
    flight_pairs.append((cities[b], cities[a]))  # flights are bidirectional

# Create a set of valid transitions
valid_transitions = set(flight_pairs)

# Initialize Z3 solver
s = Solver()

# Create variables for each day (1..16)
days = [Int(f"day_{i}") for i in range(1, 17)]

# Constraint: each day's value must be a valid city (0..5)
for day in days:
    s.add(day >= 0, day <= 5)

# Fixed constraints:
# Days 13-16 must be Frankfurt (0)
for i in range(13, 17):
    s.add(days[i-1] == 0)

# Wedding in Vilnius between day 12 and 13:
# So day 12 is Vilnius (5) or day 13 is Vilnius (but day 13 is Frankfurt, so day 12 must be Vilnius.
s.add(days[11] == 5)  # day 12 is Vilnius

# Constraints for the number of days in each city:
# Frankfurt: 4 days (including days 13-16, which are 4 days, so no additional days)
# Manchester: 4
# Valencia: 4
# Naples: 4
# Oslo: 3
# Vilnius: 2 (wedding day 12 and one more day)

# Count occurrences of each city
city_counts = [0]*6
for city in range(6):
    city_counts[city] = Sum([If(days[i] == city, 1, 0) for i in range(16)])

s.add(city_counts[cities["Frankfurt"]] == 4)
s.add(city_counts[cities["Manchester"]] == 4)
s.add(city_counts[cities["Valencia"]] == 4)
s.add(city_counts[cities["Naples"]] == 4)
s.add(city_counts[cities["Oslo"]] == 3)
s.add(city_counts[cities["Vilnius"]] == 2)

# Transition constraints: consecutive days must be the same city or connected by a direct flight
for i in range(15):
    current_day = days[i]
    next_day = days[i+1]
    # Either same city or a valid flight
    s.add(Or(
        current_day == next_day,
        And(current_day != next_day, (current_day, next_day) in valid_transitions)
    ))

# Check if the model is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(16):
        city_index = model.evaluate(days[i]).as_long()
        itinerary.append({"day": i+1, "place": city_names[city_index]})
    
    # Prepare the output in JSON format
    output = {"itinerary": itinerary}
    print(output)
else:
    print("No valid itinerary found.")