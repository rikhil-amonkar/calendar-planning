import json
import itertools

# Input parameters: required durations (in days) for each city.
# Note: When flying from one city to the next on day X, that day counts toward both cities.
city_durations = {
    "London": 3,      # Annual show, must be Day 1-3.
    "Milan": 5,       # Must include friend meeting between Day 3 and Day 7.
    "Zurich": 2,      # Conference on Day 7 and Day 8.
    "Bucharest": 2,
    "Hamburg": 5,
    "Barcelona": 4,
    "Reykjavik": 5,   # Visit relatives between Day 9 and Day 13.
    "Stuttgart": 5,
    "Stockholm": 2,
    "Tallinn": 4
}

# Direct flight network (assumed bidirectional)
flight_pairs = [
    ("London", "Hamburg"),
    ("London", "Reykjavik"),
    ("Milan", "Barcelona"),
    ("Reykjavik", "Barcelona"),
    ("Reykjavik", "Stuttgart"),
    ("Stockholm", "Reykjavik"),
    ("London", "Stuttgart"),
    ("Milan", "Zurich"),
    ("London", "Barcelona"),
    ("Stockholm", "Hamburg"),
    ("Zurich", "Barcelona"),
    ("Stockholm", "Stuttgart"),
    ("Milan", "Hamburg"),
    ("Stockholm", "Tallinn"),
    ("Hamburg", "Bucharest"),
    ("London", "Bucharest"),
    ("Milan", "Stockholm"),
    ("Stuttgart", "Hamburg"),
    ("London", "Zurich"),
    ("Milan", "Reykjavik"),
    ("London", "Stockholm"),
    ("Milan", "Stuttgart"),
    ("Stockholm", "Barcelona"),
    ("London", "Milan"),
    ("Zurich", "Hamburg"),
    ("Bucharest", "Barcelona"),
    ("Zurich", "Stockholm"),
    ("Barcelona", "Tallinn"),
    ("Zurich", "Reykjavik"),
    ("Zurich", "Bucharest"),
]

# Build flight graph as a dictionary of sets.
flight_graph = {}
def add_flight(a, b):
    flight_graph.setdefault(a, set()).add(b)
    flight_graph.setdefault(b, set()).add(a)

for a, b in flight_pairs:
    add_flight(a, b)

# Fixed positions due to absolute date constraints:
# - London must be first (and shows Day 1-3 are in London).
# - Milan should be next to enable a friend tour between Day 3 and 7.
# - To have the conference in Zurich on Day 7-8, Zurich must immediately follow Milan.
# - To shift the timeline so that Reykjavik (with 5 days) covers Day 9-13 (for relatives), 
#   we insert a 2-day city between Zurich and Reykjavik.
# Among the 2-day cities available, "Stockholm" connects well with both Zurich and Reykjavik.
fixed_order = ["London", "Milan", "Zurich", "Stockholm", "Reykjavik"]

# The remaining cities (not yet scheduled)
all_cities = set(city_durations.keys())
fixed_set = set(fixed_order)
remaining_cities = list(all_cities - fixed_set)
# remaining_cities should be: ["Bucharest", "Hamburg", "Barcelona", "Stuttgart", "Tallinn"]

# We now need to order the remaining cities (to fill positions 6 to 10)
# such that there is a direct flight from the last fixed city (Reykjavik)
# to the first city of the permutation and each consecutive pair are connected.
def valid_order(order):
    # Check flight from last fixed city to the first in the order.
    if order[0] not in flight_graph.get("Reykjavik", set()):
        return False
    # Check flights between consecutive cities in the order.
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph.get(order[i], set()):
            return False
    return True

valid_perm = None
for perm in itertools.permutations(remaining_cities):
    if valid_order(perm):
        valid_perm = list(perm)
        break

if not valid_perm:
    raise Exception("No valid ordering found for the remaining cities with direct flights")

# Full itinerary order is the fixed_order followed by the valid permutation.
full_order = fixed_order + valid_perm

# Compute the itinerary timeline.
# The rule: For each city with required duration D,
# if you fly on the departure day, that day is shared with both cities.
# Hence, if the current city starts on day S, its last day is S + D - 1,
# and the next city's start day is the same as the current city's last day.
itinerary = []
current_day = 1
for city in full_order:
    duration = city_durations[city]
    end_day = current_day + duration - 1
    day_range_str = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range_str, "place": city})
    # Next city starts on the same day the current city's block ended (flight day overlap)
    current_day = end_day

# The total itinerary should span 28 unique days.
if current_day != 28:
    raise Exception(f"Calculated itinerary spans {current_day} days instead of 28.")

# Prepare output dictionary.
output = {"itinerary": itinerary}

# Output the result as JSON.
print(json.dumps(output, indent=2))