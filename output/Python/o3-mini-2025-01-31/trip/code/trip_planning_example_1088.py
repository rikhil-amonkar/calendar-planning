#!/usr/bin/env python3
import itertools
import json

# Define the cities and their required "stay" durations (in days)
city_stays = {
    "Reykjavik": 2,  # also has conference on day 1 and day 2
    "Stockholm": 3,  # friend meeting in Stockholm between day 2 and day 4
    "Stuttgart": 5,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,     # workshop must be attended in Porto between day 19 and day 21
    "Tallinn": 5,
    "Oslo": 5
}

# Total days must equal 21.
# Because sum(stays) = 2+3+5+3+2+3+5+5 = 28 and we have 7 flights (overlap days),
# so total timeline days = 28 - 7 = 21.

# Flight network as bidirectional edges (using frozensets for undirected connection)
flights = {
    frozenset(("Reykjavik", "Stuttgart")),
    frozenset(("Reykjavik", "Stockholm")),
    frozenset(("Reykjavik", "Tallinn")),
    frozenset(("Reykjavik", "Oslo")),
    frozenset(("Stockholm", "Oslo")),
    frozenset(("Stockholm", "Stuttgart")),
    frozenset(("Stockholm", "Split")),
    frozenset(("Stockholm", "Geneva")),
    frozenset(("Stuttgart", "Porto")),
    frozenset(("Split", "Oslo")),
    frozenset(("Split", "Stuttgart")),
    frozenset(("Oslo", "Geneva")),
    frozenset(("Oslo", "Porto")),
    frozenset(("Geneva", "Porto")),
    frozenset(("Geneva", "Split"))
}

# List of all cities; the itinerary must start with Reykjavik (to allow conference on day 1 and 2)
cities = list(city_stays.keys())
# We fix the first city as "Reykjavik"
fixed_start = "Reykjavik"
remaining_cities = [c for c in cities if c != fixed_start]

def valid_flight_path(order):
    """Check that for each consecutive pair in the order, there is a direct flight."""
    for a, b in zip(order, order[1:]):
        if frozenset((a, b)) not in flights:
            return False
    return True

def compute_day_ranges(order):
    """
    Given an order of cities, compute the day range for each.
    Rule: The first city starts on day 1.
    When flying from city A to city B on day X, that day counts for both A and B.
    So if city A's stay is d_A days and it ends on day D,
    then city B is reached on day D (overlap) and its stay adds (d_B - 1) extra days.
    """
    day_ranges = {}
    day_start = 1
    # For the first city:
    first = order[0]
    d = city_stays[first]
    day_end = day_start + d - 1  # inclusive
    day_ranges[first] = (day_start, day_end)
    current_end = day_end
    # For subsequent cities:
    for city in order[1:]:
        # arrival day is the same as current_end (overlap)
        arrival = current_end
        d = city_stays[city]
        day_end = arrival + d - 1
        day_ranges[city] = (arrival, day_end)
        current_end = day_end
    return day_ranges

def check_events(day_ranges):
    """
    Check the special event constraints:
      - Conference in Reykjavik on day 1 and day 2 => Reykjavik's range must include both 1 and 2.
      - Friend meeting in Stockholm between day 2 and day 4 (at least one day in Stockholm ∈ [2,4]).
      - Workshop in Porto between day 19 and day 21 (at least one day in Porto ∈ [19,21]).
    """
    # Check Reykjavik conference:
    r_start, r_end = day_ranges["Reykjavik"]
    if not (r_start <= 1 <= r_end and r_start <= 2 <= r_end):
        return False
    # Check Stockholm meeting:
    s_start, s_end = day_ranges["Stockholm"]
    # It is enough if the intersection of [s_start, s_end] with [2,4] is not empty.
    if s_end < 2 or s_start > 4:
        return False
    # Check Porto workshop:
    p_start, p_end = day_ranges["Porto"]
    if p_end < 19 or p_start > 21:
        return False
    return True

def main():
    # We iterate over all permutations of the remaining cities,
    # and prepend the fixed starting city "Reykjavik".
    for perm in itertools.permutations(remaining_cities):
        itinerary = [fixed_start] + list(perm)
        # Check if flight connections exist between consecutive cities:
        if not valid_flight_path(itinerary):
            continue
        # Compute day ranges for this itinerary:
        day_ranges = compute_day_ranges(itinerary)
        # Total days must be 21:
        total_days = list(day_ranges.values())[-1][1]  # end day of last city
        if total_days != 21:
            continue
        # Check event constraints:
        if not check_events(day_ranges):
            continue
        # Found a valid itinerary - prepare output list with day_range and place.
        output = []
        for city in itinerary:
            start, end = day_ranges[city]
            day_range_str = f"{start}-{end}"
            output.append({"day_range": day_range_str, "place": city})
        print(json.dumps(output, indent=2))
        return
    # If no valid itinerary is found, output an empty JSON array.
    print(json.dumps([]))

if __name__ == "__main__":
    main()