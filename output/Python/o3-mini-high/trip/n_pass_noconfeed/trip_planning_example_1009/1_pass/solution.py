#!/usr/bin/env python3
import itertools
import json

# Define the cities with their required durations
cities_durations = {
    "Riga": 4,
    "Manchester": 5,
    "Bucharest": 4,
    "Florence": 4,
    "Vienna": 2,
    "Istanbul": 2,
    "Reykjavik": 4,
    "Stuttgart": 5
}

# Define the flight graph (bidirectional edges)
flight_graph = {
    "Bucharest": {"Vienna", "Riga", "Istanbul", "Manchester"},
    "Vienna": {"Bucharest", "Reykjavik", "Manchester", "Riga", "Istanbul", "Florence", "Stuttgart"},
    "Reykjavik": {"Vienna", "Stuttgart"},
    "Manchester": {"Vienna", "Riga", "Istanbul", "Bucharest", "Stuttgart"},
    "Riga": {"Vienna", "Manchester", "Bucharest", "Istanbul"},
    "Istanbul": {"Vienna", "Riga", "Bucharest", "Manchester", "Stuttgart"},
    "Florence": {"Vienna"},
    "Stuttgart": {"Vienna", "Istanbul", "Manchester", "Reykjavik"}
}

# Trip total parameters
TOTAL_DAYS = 23
# Sum of durations must be total + (num_cities - 1)
NUM_CITIES = len(cities_durations)
EXPECTED_TOTAL_DURATION = sum(cities_durations.values()) - (NUM_CITIES - 1)  # 30 - 7 = 23

# Constraint conditions:
# 1. Istanbul: its stay must cover the annual show on day 12-13.
#    That forces the start day for Istanbul to be exactly 12 because its duration is 2 (covers day 12 and 13).
# 2. Bucharest: must host a workshop between day 16 and 19.
#    Given its duration of 4 days, the stay must include at least one day in [16, 19].
#    A sufficient condition is: start_day <= 19 and (start_day + 4 - 1) >= 16, i.e., start_day >= 13.
def compute_start_days(order, durations):
    # Compute the start day for each city in the itinerary.
    # Rule: The first city starts on day 1.
    # If a flight occurs on day X (transition from city A to city B on the same calendar day),
    # then the formula is: s[0] = 1 and for i>=1, s[i] = 1 + (sum_{j=0}^{i-1} duration_j) - i.
    start_days = []
    total = 0
    for i, city in enumerate(order):
        total += durations[city]
        # subtract i because each transition overlaps a day
        s = 1 + total - (i + 1)
        start_days.append(s)
    return start_days

def itinerary_valid(order, start_days):
    # Check if the flight connection is available for every consecutive pair.
    for a, b in zip(order, order[1:]):
        if b not in flight_graph.get(a, set()):
            return False

    # Check the Istanbul constraint (annual show day 12-13)
    # Istanbul must have start day exactly 12 so that with a duration of 2 days,
    # it covers day 12 and day 13.
    for idx, city in enumerate(order):
        if city == "Istanbul":
            if start_days[idx] != 12:
                return False

    # Check the Bucharest workshop constraint:
    # Bucharest (4 days) must include at least one day between 16 and 19.
    # That is, if Bucharest starts on day s, its days are s, s+1, s+2, s+3.
    # We require that there exists a day d in {s, s+1, s+2, s+3} with 16 <= d <= 19.
    for idx, city in enumerate(order):
        if city == "Bucharest":
            s = start_days[idx]
            # The stay covers days s through s+3
            if s > 19 or (s + 3) < 16:
                return False

    # Check overall total days: final city's last day must be TOTAL_DAYS
    last_city = order[-1]
    last_index = len(order) - 1
    final_day = start_days[last_index] + cities_durations[last_city] - 1
    if final_day != TOTAL_DAYS:
        return False

    return True

def build_itinerary(order, start_days):
    # Build a list of itinerary segments with day ranges and place names.
    itinerary = []
    for city, s in zip(order, start_days):
        duration = cities_durations[city]
        end_day = s + duration - 1
        # Format day range as "Day X-Y"
        segment = {
            "day_range": f"Day {s}-{end_day}",
            "place": city
        }
        itinerary.append(segment)
    return itinerary

def main():
    all_cities = list(cities_durations.keys())
    valid_itinerary = None

    # Search through all permutations for one that meets the constraints.
    for order in itertools.permutations(all_cities):
        start_days = compute_start_days(order, cities_durations)
        if itinerary_valid(order, start_days):
            valid_itinerary = build_itinerary(order, start_days)
            break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": valid_itinerary}

    # Output the result as JSON-formatted dictionary.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()