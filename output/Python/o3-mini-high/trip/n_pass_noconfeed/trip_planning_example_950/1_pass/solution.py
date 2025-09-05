import json
import itertools

# Input constraints and parameters
total_days = 17

# Cities to be visited with required durations (in days)
# Note: because flight days count for both the departing and arriving city,
# the sum of durations minus (number of transitions) equals the total trip days.
durations = {
    "Rome": 4,        # Must include conference on day 1 and day 4
    "Mykonos": 3,     # Must include a wedding between day 4 and day 6
    "Nice": 3,
    "Riga": 3,
    "Bucharest": 4,
    "Munich": 4,
    "Krakow": 2      # Must include an annual show on day 16-17
}

# Flight network: each key's list contains cities that can be reached directly from the key.
# Most flights are bidirectional, but the ones marked with "from" are directional.
flight_graph = {
    "Rome": ["Nice", "Munich", "Mykonos", "Bucharest", "Riga"],  # "from Rome to Riga" is allowed
    "Mykonos": ["Munich", "Nice", "Rome"],
    "Nice": ["Riga", "Rome", "Munich", "Mykonos"],
    "Riga": ["Nice", "Bucharest", "Munich"],  # "from Riga to Munich" allowed directionally
    "Bucharest": ["Munich", "Riga", "Rome"],
    "Munich": ["Krakow", "Bucharest", "Rome", "Mykonos", "Nice"],
    "Krakow": ["Munich"]
}

# The mandated starting and ending cities
start_city = "Rome"
end_city   = "Krakow"

# The list of all cities required (7 in total)
all_cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]

# The middle cities that must be visited in some order (start and end are fixed)
middle_cities = [city for city in all_cities if city not in [start_city, end_city]]

def compute_segments(route, durations):
    """
    Given a route (list of cities in order) and durations,
    compute the day segments for each city.
    The rule is: first city starts Day 1.
    For city0: segment is [start, start + duration - 1]
    For subsequent cities, the flight day is the same as the previous city's end day.
    """
    segments = {}
    current_day = 1
    for city in route:
        seg_start = current_day
        seg_end = current_day + durations[city] - 1
        segments[city] = (seg_start, seg_end)
        # The next city starts on seg_end (flight day counts in both cities)
        current_day = seg_end
    return segments, current_day

def valid_flight_connection(city_from, city_to):
    # Check if there is a direct flight from city_from to city_to according to flight_graph.
    return city_to in flight_graph.get(city_from, [])

def satisfies_constraints(route, segments):
    # Constraint: The trip must start with Rome and end with Krakow.
    if route[0] != start_city or route[-1] != end_city:
        return False
    # Total days (last segment end day) must equal total_days.
    last_segment = segments[route[-1]]
    if last_segment[1] != total_days:
        return False

    # Conference constraint: Must be in Rome on day 1 and day 4.
    rome_segment = segments["Rome"]
    if not (rome_segment[0] <= 1 <= rome_segment[1] and rome_segment[0] <= 4 <= rome_segment[1]):
        return False

    # Wedding constraint: In Mykonos, at least one of day 4, 5, or 6 must be spent.
    # That is, the Mykonos segment must overlap with the interval [4,6].
    mykonos_segment = segments["Mykonos"]
    # Overlap condition: segment_end >= 4 and segment_start <= 6.
    if not (mykonos_segment[1] >= 4 and mykonos_segment[0] <= 6):
        return False

    # Annual show in Krakow: Must be in Krakow on day 16 and day 17.
    krakow_segment = segments["Krakow"]
    if not (krakow_segment[0] <= 16 <= krakow_segment[1] and krakow_segment[0] <= 17 <= krakow_segment[1]):
        return False

    return True

# Try all permutations of the middle cities.
valid_itinerary = None
for perm in itertools.permutations(middle_cities):
    route = [start_city] + list(perm) + [end_city]
    # Check direct flights for consecutive cities in the route.
    flight_valid = True
    for i in range(len(route) - 1):
        if not valid_flight_connection(route[i], route[i+1]):
            flight_valid = False
            break
    if not flight_valid:
        continue

    # Compute day segments based on durations.
    segments, final_day = compute_segments(route, durations)
    if final_day != total_days:
        continue

    # Check if the day-specific constraints are met.
    if not satisfies_constraints(route, segments):
        continue

    # If this route satisfies all constraints, we choose it.
    valid_itinerary = (route, segments)
    break

if not valid_itinerary:
    output = {"itinerary": "No valid itinerary found with the given constraints."}
else:
    route, segments = valid_itinerary
    # Build the itinerary list according to the output structure.
    itinerary_list = []
    # To keep the order as in our route, we iterate in that order.
    for city in route:
        start_day, end_day = segments[city]
        day_range = f"Day {start_day}-{end_day}"
        itinerary_list.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary_list}

# Output the result as a JSON-formatted dictionary.
print(json.dumps(output, indent=2))