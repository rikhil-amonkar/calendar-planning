import json

# Input parameters and required durations for each city (in days)
# Note: When flying from city A to city B on a given day X,
# the day X counts for both cities.
cities = [
    {"name": "Hamburg", "required": 5},    # 5 days in Hamburg
    {"name": "Frankfurt", "required": 2},   # 2 days in Frankfurt; must cover days 5-6 (annual show)
    {"name": "Naples", "required": 5},      # 5 days in Naples
    {"name": "Mykonos", "required": 3},     # 3 days in Mykonos; meeting friend between day 10 and day 12
    {"name": "Geneva", "required": 3},      # 3 days in Geneva
    {"name": "Porto", "required": 2},       # 2 days in Porto
    {"name": "Manchester", "required": 4}   # 4 days in Manchester; wedding between day 15 and 18
]

# The available direct flights (bidirectional unless noted otherwise)
# Represented as a set of frozensets for unordered pairs except for the one "from Hamburg to Geneva"
# We treat "from Hamburg to Geneva" as also allowing the reverse flight for itinerary feasibility.
direct_flights = {
    frozenset(["Hamburg", "Frankfurt"]),
    frozenset(["Naples", "Mykonos"]),
    frozenset(["Hamburg", "Porto"]),
    frozenset(["Hamburg", "Geneva"]),  # "from Hamburg to Geneva" accepted as flight between Hamburg and Geneva.
    frozenset(["Mykonos", "Geneva"]),
    frozenset(["Frankfurt", "Geneva"]),
    frozenset(["Frankfurt", "Porto"]),
    frozenset(["Geneva", "Porto"]),
    frozenset(["Geneva", "Manchester"]),
    frozenset(["Naples", "Manchester"]),
    frozenset(["Frankfurt", "Naples"]),
    frozenset(["Frankfurt", "Manchester"]),
    frozenset(["Naples", "Geneva"]),
    frozenset(["Porto", "Manchester"]),
    frozenset(["Hamburg", "Manchester"])
}

# Proposed order that satisfies all scheduling constraints:
# 1. Start in Hamburg (5 days)
# 2. Fly from Hamburg to Frankfurt on day 5 (overlap day5) so Frankfurt gets day5-6 to catch the show (days 5,6)
# 3. Fly from Frankfurt to Naples on day6 (overlap day6) to spend 5 days (day6-10)
# 4. Fly from Naples to Mykonos on day10 (overlap day10) to spend 3 days (day10-12); friend meets between day10-12
# 5. Fly from Mykonos to Geneva on day12 (overlap day12) to spend 3 days (day12-14)
# 6. Fly from Geneva to Porto on day14 (overlap day14) to spend 2 days (day14-15)
# 7. Finally, fly from Porto to Manchester on day15 (overlap day15) to spend 4 days (day15-18) for the wedding.
itinerary_order = ["Hamburg", "Frankfurt", "Naples", "Mykonos", "Geneva", "Porto", "Manchester"]

# Check if the sequence is feasible with direct flights
def has_direct_flight(city_a, city_b):
    return frozenset([city_a, city_b]) in direct_flights

feasible = True
for i in range(len(itinerary_order) - 1):
    if not has_direct_flight(itinerary_order[i], itinerary_order[i+1]):
        feasible = False
        break

if not feasible:
    raise Exception("The chosen itinerary order is not feasible with the available direct flights.")

# Compute the itinerary day ranges.
# The rule: The first city starts at day 1.
# Each subsequent city starts on the last day of the previous city (flight day, double counting)
itinerary = []
current_day = 1
city_day_ranges = {}

# Create a dictionary for required durations for fast lookup
duration_map = {city["name"]: city["required"] for city in cities}

for idx, city in enumerate(itinerary_order):
    # The effective stay is from current_day to (current_day + duration - 1)
    start_day = current_day
    end_day = current_day + duration_map[city] - 1
    city_day_ranges[city] = (start_day, end_day)
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city
    })
    # The next city's start day is the current end_day because the flight happens on that same day
    current_day = end_day

# Validate special constraints:
# - Frankfurt must include days 5 and 6.
frankfurt_range = city_day_ranges["Frankfurt"]
if not (frankfurt_range[0] <= 5 <= frankfurt_range[1] and frankfurt_range[0] <= 6 <= frankfurt_range[1]):
    raise Exception("Frankfurt does not cover the annual show days (5-6).")

# - Mykonos must include a day between 10 and 12.
mykonos_range = city_day_ranges["Mykonos"]
if not (mykonos_range[0] <= 10 <= mykonos_range[1] or mykonos_range[0] <= 11 <= mykonos_range[1] or mykonos_range[0] <= 12 <= mykonos_range[1]):
    raise Exception("Mykonos does not cover the friend meeting window (10-12).")

# - Manchester must cover days 15 to 18 for the wedding.
manchester_range = city_day_ranges["Manchester"]
if not (manchester_range[0] <= 15 and manchester_range[1] >= 18):
    raise Exception("Manchester does not cover the wedding days (15-18).")

# - The total itinerary must span exactly 18 days.
if city_day_ranges["Manchester"][1] != 18:
    raise Exception("The total itinerary does not span 18 days.")

# Output the itinerary as a JSON-formatted dictionary (list of day ranges and places)
output = {"itinerary": itinerary}
print(json.dumps(output))