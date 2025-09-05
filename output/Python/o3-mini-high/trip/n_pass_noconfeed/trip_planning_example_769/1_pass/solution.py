import json
import itertools

# Trip parameters
total_days = 16

# Required stay durations for each city
durations = {
    "Porto": 5,
    "Prague": 4,
    "Reykjavik": 4,
    "Santorini": 2,
    "Amsterdam": 2,
    "Munich": 4
}

# Special event constraints:
# Wedding in Reykjavik must happen between day 4 and 7.
# Friend meeting in Munich must occur between day 7 and 10.
# Conference in Amsterdam must occur during day 14 and 15 
# (so Amsterdam's interval must cover both day 14 and day 15).

# Flight connections (bidirectional)
flight_graph = {
    "Porto": {"Amsterdam", "Munich"},
    "Amsterdam": {"Porto", "Munich", "Reykjavik", "Santorini", "Prague"},
    "Munich": {"Amsterdam", "Porto", "Reykjavik", "Prague"},
    "Reykjavik": {"Amsterdam", "Munich", "Prague"},
    "Prague": {"Reykjavik", "Amsterdam", "Munich"},
    "Santorini": {"Amsterdam"}
}

cities = list(durations.keys())

def compute_intervals(order, durations):
    """
    Compute itinerary intervals.
    The first city's stay is from day 1 to day (duration).
    For each subsequent city, the start day is the last day of the previous city (flight day overlap).
    """
    intervals = []
    start = 1
    for city in order:
        end = start + durations[city] - 1
        intervals.append((city, start, end))
        # Next city starts on the same day as the end day (flight day counts for both)
        start = end
    return intervals

def check_connectivity(order, flight_graph):
    """
    For each consecutive pair of cities in the order ensure a direct flight exists.
    """
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph[order[i]]:
            return False
    return True

def check_special_events(intervals):
    wedding_ok = False   # For Reykjavik between day 4 and 7
    friend_ok = False    # For Munich between day 7 and 10
    conference_ok = False  # For Amsterdam covering day 14 and 15

    for city, start, end in intervals:
        if city == "Reykjavik":
            # Must attend wedding between day 4 and 7, so interval must include at least one day in [4,7]
            if end >= 4 and start <= 7:
                wedding_ok = True
        if city == "Munich":
            # Friend meeting between day 7 and 10 must be inside the interval.
            if end >= 7 and start <= 10:
                friend_ok = True
        if city == "Amsterdam":
            # Conference during day 14 and 15; with a 2-day stay, this forces start to be 14 (interval: 14-15)
            if start <= 14 and end >= 15:
                conference_ok = True
    return wedding_ok and friend_ok and conference_ok

# Iterate over all possible orders of visiting the 6 cities.
found_order = None
found_intervals = None

for perm in itertools.permutations(cities):
    # Check flight connectivity between consecutive cities.
    if not check_connectivity(perm, flight_graph):
        continue

    # Compute the day intervals for each city in this permutation.
    intervals = compute_intervals(perm, durations)
    
    # Check if the overall trip lasts exactly total_days.
    if intervals[-1][2] != total_days:
        continue

    # Check if special event constraints are met.
    if not check_special_events(intervals):
        continue

    found_order = perm
    found_intervals = intervals
    break

if found_order is None:
    result = {"itinerary": []}
else:
    # Create the output itinerary list with day_range and place.
    itinerary_list = []
    for city, start, end in found_intervals:
        itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
    result = {"itinerary": itinerary_list}

print(json.dumps(result))