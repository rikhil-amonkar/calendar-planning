import itertools
import json

# Total trip days
TOTAL_DAYS = 16

# Define the cities and the required number of days to spend in each.
durations = {
    "Paris": 2,      # Must attend wedding between Day 1 and Day 2
    "Krakow": 3,
    "Vienna": 4,
    "Riga": 4,
    "Hamburg": 2,    # Conference on Day 10 and Day 11
    "Edinburgh": 4,  # Meet friend between Day 12 and Day 15
    "Barcelona": 2,
    "Stockholm": 2   # Visit relatives between Day 15 and Day 16
}

# List of all cities
cities = list(durations.keys())

# Build the flight graph.
# Most flights are bidirectional except one special flight "from Riga to Hamburg"
graph = {city: set() for city in cities}
# List of direct flight pairs (interpreted as bidirectional)
flight_pairs = [
    ("Hamburg", "Stockholm"),
    ("Vienna", "Stockholm"),
    ("Paris", "Edinburgh"),
    ("Riga", "Barcelona"),
    ("Paris", "Riga"),
    ("Krakow", "Barcelona"),
    ("Edinburgh", "Stockholm"),
    ("Paris", "Krakow"),
    ("Krakow", "Stockholm"),
    ("Riga", "Edinburgh"),
    ("Barcelona", "Stockholm"),
    ("Paris", "Stockholm"),
    ("Krakow", "Edinburgh"),
    ("Vienna", "Hamburg"),
    ("Paris", "Hamburg"),
    ("Riga", "Stockholm"),
    ("Hamburg", "Barcelona"),
    ("Vienna", "Barcelona"),
    ("Krakow", "Vienna"),
    # Special directed flight will be added separately: from Riga to Hamburg
    ("Barcelona", "Edinburgh"),
    ("Paris", "Barcelona"),
    ("Hamburg", "Edinburgh"),
    ("Paris", "Vienna"),
    ("Vienna", "Riga")
]

# Add bidirectional edges for all normal flight pairs.
for a, b in flight_pairs:
    graph[a].add(b)
    graph[b].add(a)

# Add the special directed flight: from Riga to Hamburg.
# This flight is allowed from Riga to Hamburg but not in the reverse direction.
graph["Riga"].add("Hamburg")
if "Riga" in graph["Hamburg"]:
    graph["Hamburg"].remove("Riga")

def can_fly(city_from, city_to):
    """
    Returns True if there is a direct flight from city_from to city_to.
    (Takes into account the one-way nature of the Riga->Hamburg flight.)
    """
    return city_to in graph[city_from]

def compute_schedule(order, durations):
    """
    Given an itinerary order (list of cities) and city durations,
    compute the start and end day for each city.
    Note: When flying on a day, that day counts for both the origin and the destination.
    """
    schedule = []
    current_day = 1
    for city in order:
        d = durations[city]
        # The segment for this city spans from current_day to current_day + d - 1.
        end_day = current_day + d - 1
        schedule.append((city, current_day, end_day))
        # Next city's segment starts on the same day the previous segment ended (overlap flight day).
        current_day = end_day
    return schedule

def schedule_is_valid(schedule):
    """
    Check that the schedule meets:
    - Total trip length is exactly TOTAL_DAYS.
    - Flight connectivity exists for consecutive cities.
    - Special time constraints:
       • Paris (wedding) must be visited on Day 1-2.
       • Hamburg must cover Day 10 and Day 11 exactly.
       • Edinburgh must include at least one day between 12 and 15.
       • Stockholm must include at least one day between 15 and 16.
    """
    # Check that the final day equals TOTAL_DAYS.
    if schedule[-1][2] != TOTAL_DAYS:
        return False

    # Check flight connectivity for consecutive cities.
    for i in range(len(schedule) - 1):
        if not can_fly(schedule[i][0], schedule[i+1][0]):
            return False

    # Check special constraints.
    for city, start, end in schedule:
        if city == "Paris":
            # Wedding in Paris must be between Day 1 and Day 2.
            # Since Paris is best placed at the start, we enforce it be the first city.
            if start > 1 or end < 2:
                return False
        if city == "Hamburg":
            # Hamburg conference: must cover Day 10 and Day 11.
            # With a 2-day duration, Hamburg should start on Day 10 (covering Day 10 and 11).
            if start != 10:
                return False
        if city == "Edinburgh":
            # Friend meeting should occur between Day 12 and Day 15.
            # There must be overlap between Edinburgh's day range and [12, 15].
            if end < 12 or start > 15:
                return False
        if city == "Stockholm":
            # Relatives visit in Stockholm between Day 15 and Day 16.
            if end < 15 or start > 16:
                return False
    return True

# In our search it is optimal to have Paris first (for the wedding) and Stockholm last (for the relatives).
fixed_start = "Paris"
fixed_end = "Stockholm"

# Create the list of cities that remain (excluding fixed start and end).
remaining_cities = [city for city in cities if city not in [fixed_start, fixed_end]]

valid_itinerary = None
valid_schedule_result = None

# Try all possible orders (permutations of the remaining cities).
for perm in itertools.permutations(remaining_cities):
    order = [fixed_start] + list(perm) + [fixed_end]
    sch = compute_schedule(order, durations)
    if schedule_is_valid(sch):
        valid_itinerary = order
        valid_schedule_result = sch
        break

if valid_schedule_result is None:
    result = {"itinerary": []}
else:
    # Build the itinerary output as a list of dictionaries with day_range and place.
    itinerary_output = []
    for city, start, end in valid_schedule_result:
        itinerary_output.append({
            "day_range": "Day {}-{}".format(start, end),
            "place": city
        })
    result = {"itinerary": itinerary_output}

print(json.dumps(result))