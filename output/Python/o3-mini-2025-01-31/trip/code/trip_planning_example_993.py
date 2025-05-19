import json

# Input variables (constraints)
total_days = 15
cities = ["Amsterdam", "London", "Bucharest", "Riga", "Vilnius", "Frankfurt", "Stockholm"]
# Required durations in each city (the sum is 21, but flight days count double in transitions)
durations = {
    "Amsterdam": 2,   # Friend meeting in Amsterdam between day 2 and 3.
    "London": 2,
    "Bucharest": 4,
    "Riga": 2,
    "Vilnius": 5,     # Workshop in Vilnius between day 7 and 11.
    "Frankfurt": 3,
    "Stockholm": 3    # Wedding in Stockholm between day 13 and 15.
}

# The flight legs (only for validation; note that the algorithm below relies on a chosen order 
# that satisfies the constraints and available direct flights)
direct_flights = [
    ("London", "Amsterdam"),
    ("Vilnius", "Frankfurt"),
    ("Riga", "Vilnius"),
    ("Riga", "Stockholm"),
    ("London", "Bucharest"),
    ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Frankfurt"),
    ("Frankfurt", "Stockholm"),
    ("Bucharest", "Riga"),
    ("Amsterdam", "Riga"),
    ("Amsterdam", "Bucharest"),
    ("Riga", "Frankfurt"),
    ("Bucharest", "Frankfurt"),
    ("London", "Frankfurt"),
    ("London", "Stockholm"),
    ("Amsterdam", "Vilnius")
]

# Chosen itinerary order:
#   1. Amsterdam (start; satisfies friend meeting on day 2 since day2 is spent in Amsterdam)
#   2. London     (via direct flight from Amsterdam <-> London)
#   3. Bucharest  (via direct flight from London -> Bucharest)
#   4. Riga       (via direct flight from Bucharest -> Riga)
#   5. Vilnius    (via direct flight from Riga -> Vilnius)
#   6. Frankfurt  (via direct flight from Vilnius -> Frankfurt)
#   7. Stockholm  (via direct flight from Frankfurt -> Stockholm,
#                  satisfies wedding in Stockholm between day 13 and 15)
itinerary_order = ["Amsterdam", "London", "Bucharest", "Riga", "Vilnius", "Frankfurt", "Stockholm"]

# Validate flight connectivity for the chosen order.
def has_direct_flight(city_a, city_b):
    # Since flights are undirected in our context, check both orders.
    return (city_a, city_b) in direct_flights or (city_b, city_a) in direct_flights

valid_route = True
for i in range(len(itinerary_order) - 1):
    if not has_direct_flight(itinerary_order[i], itinerary_order[i+1]):
        valid_route = False
        break

if not valid_route:
    raise ValueError("The chosen itinerary order does not satisfy the direct flight constraints.")

# Compute the day ranges.
# Note: The rule is that if you fly on day X from city A to city B,
# then day X counts for both A and B.
# Thus, the first city gets a full duration starting from day 1.
# Each subsequent city starts on the last day of the previous city.
schedule = []
current_day = 1
for index, city in enumerate(itinerary_order):
    d = durations[city]
    # first city: range from current_day to current_day+d-1
    # subsequent cities: start day = current_day (which is the overlap day from previous flight)
    start_day = current_day
    end_day = start_day + d - 1
    day_range = f"{start_day}-{end_day}"
    schedule.append({"day_range": day_range, "place": city})
    # For next city, the current_day becomes the last day of current city (flight day overlap)
    current_day = end_day

# The computed schedule should cover a total of 15 days (taking into account overlaps)
# Total calculated travel span is the last day of the last city.
if current_day != total_days:
    raise ValueError("The calculated schedule does not sum up to the required total days.")

# Output the schedule as JSON-formatted dictionary (list of dictionaries)
print(json.dumps(schedule))