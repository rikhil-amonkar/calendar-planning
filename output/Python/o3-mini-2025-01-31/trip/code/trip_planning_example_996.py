import json

# Trip constraints and parameters
total_days = 22
cities = [
    {"name": "Mykonos", "days": 3},    # Wedding between day 1 and day 3; must cover that window.
    {"name": "Nice", "days": 2},       
    {"name": "Riga", "days": 5},
    {"name": "Prague", "days": 3},      # Relatives must be visited between day 7 and day 9.
    {"name": "Zurich", "days": 5},
    {"name": "Valencia", "days": 5},
    {"name": "Bucharest", "days": 5}
]

# Allowed direct flights (provided as undirected pairs)
allowed_flights = {
    frozenset(["Mykonos", "Nice"]),
    frozenset(["Mykonos", "Zurich"]),
    frozenset(["Prague", "Bucharest"]),
    frozenset(["Valencia", "Bucharest"]),
    frozenset(["Zurich", "Prague"]),
    frozenset(["Riga", "Nice"]),
    frozenset(["Zurich", "Riga"]),
    frozenset(["Zurich", "Bucharest"]),
    frozenset(["Zurich", "Valencia"]),
    frozenset(["Bucharest", "Riga"]),
    frozenset(["Prague", "Riga"]),
    frozenset(["Prague", "Valencia"]),
    frozenset(["Zurich", "Nice"])
}

# Proposed itinerary order:
# 1. Mykonos (3 days, wedding: day1-3)
# 2. Nice (2 days)
# 3. Riga (5 days)
# 4. Prague (3 days, must include a day between 7 and 9; here it gets days 8 and 9)
# 5. Zurich (5 days)
# 6. Valencia (5 days)
# 7. Bucharest (5 days)
#
# Check flights:
# Mykonos -> Nice : allowed.
# Nice -> Riga : allowed.
# Riga -> Prague : allowed.
# Prague -> Zurich : allowed.
# Zurich -> Valencia : allowed.
# Valencia -> Bucharest : allowed.

# We follow the rule: if one flies from A to B on day X,
# then day X is counted in both A and B.
# With this overlap, the overall total day count is:
# Total days = (sum of individual city days) - (number of flights)
#  = (3+2+5+3+5+5+5) - 6 = 28 - 6 = 22 days, as required.

# Compute the itinerary day ranges:
itinerary = []
# x will be the start day for the current city.
current_day = 1
for city in cities:
    start_day = current_day
    # The city must be visited for exactly "city['days']" days.
    # Because the flight day overlaps with the next city's start, the end day is:
    end_day = start_day + city["days"] - 1
    itinerary.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city["name"]
    })
    # Set the start day for the next city to be the same as the current end day.
    current_day = end_day

# Validate that the last day matches the total_days required
if current_day != total_days:
    raise ValueError(f"Computed itinerary ends on day {current_day} but should end on day {total_days}.")

# Additional check: ensure the flight connections are allowed
# (We check consecutive cities in the itinerary order.)
def is_flight_allowed(city_a, city_b):
    return frozenset([city_a, city_b]) in allowed_flights

for i in range(len(cities) - 1):
    if not is_flight_allowed(cities[i]["name"], cities[i+1]["name"]):
        raise ValueError(f"Flight not allowed between {cities[i]['name']} and {cities[i+1]['name']}.")

# Check special constraints:
# Mykonos wedding constraint: must be in Mykonos between day 1 and 3.
mykonos_range = itinerary[0]["day_range"]
start, end = map(int, mykonos_range.split("-"))
if start > 1 or end < 3:
    raise ValueError("Mykonos visit does not cover the wedding window of day 1 to 3.")

# Prague relatives constraint: should have at least one day in Prague between day 7 and 9.
prague_range = itinerary[3]["day_range"]  # Prague is the 4th city in our order.
p_start, p_end = map(int, prague_range.split("-"))
# We require that the Prague range overlaps with the window 7 to 9.
if p_end < 7 or p_start > 9:
    raise ValueError("Prague visit does not cover the relatives' visit window between day 7 and 9.")

# Output the itinerary as a JSON-formatted dictionary (list of dicts)
print(json.dumps(itinerary, indent=2))