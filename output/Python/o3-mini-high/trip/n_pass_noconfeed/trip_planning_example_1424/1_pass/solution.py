#!/usr/bin/env python3
import itertools
import json

# Define the durations for each city
durations = {
    "Warsaw": 3,
    "Porto": 5,
    "Naples": 4,
    "Brussels": 3,
    "Split": 3,
    "Reykjavik": 5,
    "Amsterdam": 4,
    "Lyon": 3,
    "Helsinki": 4,
    "Valencia": 2
}

# Define the direct flight connections as undirected edges (represented as frozensets)
flights = {
    frozenset(["Amsterdam", "Warsaw"]),
    frozenset(["Helsinki", "Brussels"]),
    frozenset(["Helsinki", "Warsaw"]),
    frozenset(["Reykjavik", "Brussels"]),
    frozenset(["Amsterdam", "Lyon"]),
    frozenset(["Amsterdam", "Naples"]),
    frozenset(["Amsterdam", "Reykjavik"]),
    frozenset(["Naples", "Valencia"]),
    frozenset(["Porto", "Brussels"]),
    frozenset(["Amsterdam", "Split"]),
    frozenset(["Lyon", "Split"]),
    frozenset(["Warsaw", "Split"]),
    frozenset(["Porto", "Amsterdam"]),
    frozenset(["Helsinki", "Split"]),
    frozenset(["Brussels", "Lyon"]),
    frozenset(["Porto", "Lyon"]),
    frozenset(["Reykjavik", "Warsaw"]),
    frozenset(["Brussels", "Valencia"]),
    frozenset(["Valencia", "Lyon"]),
    frozenset(["Porto", "Warsaw"]),
    frozenset(["Warsaw", "Valencia"]),
    frozenset(["Amsterdam", "Helsinki"]),
    frozenset(["Porto", "Valencia"]),
    frozenset(["Warsaw", "Brussels"]),
    frozenset(["Warsaw", "Naples"]),
    frozenset(["Naples", "Split"]),
    frozenset(["Helsinki", "Naples"]),
    frozenset(["Helsinki", "Reykjavik"]),
    frozenset(["Amsterdam", "Valencia"]),
    frozenset(["Naples", "Brussels"])
}

# Event constraints (if needed, we enforce these by start day in the computed timeline):
# - Porto: workshop between day 1 and 5. (If Porto is first, with duration 5, its range is 1-5.)
# - Amsterdam: visit relatives between day 5 and 8. (If Amsterdam is second with duration 4, range is 5-8.)
# - Helsinki: wedding between day 8 and 11. (If Helsinki is third with duration 4, range is 8-11.)
# - Naples: conference between day 17 and 20 -> We require that the start day for "Naples" equals 17.
# - Brussels: annual show between day 20 and 22 -> We require that the start day for "Brussels" equals 20.
# Also, the overall plan must span 27 unique days.
TOTAL_DAYS = 27

# We will fix the beginning of the itinerary:
fixed_order = ["Porto", "Amsterdam", "Helsinki"]
# The remaining cities to order:
remaining_cities = ["Warsaw", "Naples", "Brussels", "Split", "Reykjavik", "Lyon", "Valencia"]

def compute_start_days(order):
    """
    Given an order (list of city names), compute the start day for each city.
    The rule is: start_day[0] = 1, and for i > 0:
      start_day[i] = start_day[i-1] + (duration(previous) - 1)
    Because if you fly on day X, that day counts in both cities.
    """
    start_days = [1]
    for i in range(1, len(order)):
        prev = order[i-1]
        start_days.append(start_days[i-1] + durations[prev] - 1)
    return start_days

def is_valid_itinerary(order, start_days):
    # Check overall length: final day must equal TOTAL_DAYS.
    final_day = start_days[-1] + durations[order[-1]] - 1
    if final_day != TOTAL_DAYS:
        return False

    # Check event time constraints:
    # For Porto, Amsterdam, Helsinki we assume fixed positions so their ranges are:
    # Porto: day1 to 1+5-1 = 5, Amsterdam: day5 to 5+4-1 = 8, Helsinki: day8 to 8+4-1 = 11.
    # For Naples: require its start day equals 17.
    # For Brussels: require its start day equals 20.
    for city, start in zip(order, start_days):
        if city == "Naples" and start != 17:
            return False
        if city == "Brussels" and start != 20:
            return False

    # Check direct flight connectivity between consecutive cities.
    for a, b in zip(order, order[1:]):
        if frozenset([a, b]) not in flights:
            return False

    return True

# We'll search for an ordering among the remaining cities (after the fixed first three)
# that satisfies the constraint that "Naples" is immediately followed by "Brussels".
found_order = None

# Generate all permutations of the remaining cities
for perm in itertools.permutations(remaining_cities):
    # Ensure that "Naples" is immediately followed by "Brussels"
    # Find the index of "Naples" in perm and check that the next element is "Brussels"
    try:
        idx = perm.index("Naples")
    except ValueError:
        continue
    # "Naples" cannot be the last element if it is to be followed by "Brussels"
    if idx == len(perm) - 1:
        continue
    if perm[idx + 1] != "Brussels":
        continue

    # Form the full itinerary order with the fixed beginning.
    order = fixed_order + list(perm)
    # Compute the start days for the full order.
    start_days = compute_start_days(order)
    # Check validity of the itinerary wrt event constraints and connectivity.
    if is_valid_itinerary(order, start_days):
        found_order = (order, start_days)
        break

# If we found a valid itinerary, build the itinerary JSON structure.
if found_order:
    order, start_days = found_order
    itinerary = []
    for city, start in zip(order, start_days):
        end_day = start + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end_day}", "place": city})
    result = {"itinerary": itinerary}
else:
    result = {"itinerary": []}

# Output the result as a JSON-formatted dictionary
print(json.dumps(result, indent=2))