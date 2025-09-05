#!/usr/bin/env python3
import itertools
import json

# Define the cities with their required durations.
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

# Trip parameters.
TOTAL_DAYS = 23
# For 8 cities: (sum of all city durations = 30) – (number of flights = 7) equals 23.
NUM_CITIES = len(cities_durations)

# The itinerary uses a start-day calculation where:
# - The first city starts on day 1.
# - For each subsequent city, start_day = previous city’s start_day + (duration - 1)
def compute_start_days(order, durations):
    start_days = []
    current = 1
    for city in order:
        start_days.append(current)
        current += durations[city] - 1  # flight day "reuses" the last day of the previous city
    return start_days

def itinerary_valid(order, start_days):
    # Check that every consecutive city pair has a valid flight connection.
    for a, b in zip(order, order[1:]):
        if b not in flight_graph.get(a, set()):
            return False

    # Istanbul must start on day 12.
    for idx, city in enumerate(order):
        if city == "Istanbul":
            if start_days[idx] != 12:
                return False

    # Bucharest's four-day stay must cover at least one day between 16 and 19.
    # This is ensured if its start day is not later than 19 and its period covers day 16.
    for idx, city in enumerate(order):
        if city == "Bucharest":
            s = start_days[idx]
            if s > 19 or (s + 3) < 16:
                return False

    # Final city must finish exactly on TOTAL_DAYS.
    last_city = order[-1]
    final_day = start_days[-1] + cities_durations[last_city] - 1
    if final_day != TOTAL_DAYS:
        return False

    return True

def build_itinerary(order, start_days):
    itinerary = []
    for city, s in zip(order, start_days):
        duration = cities_durations[city]
        end_day = s + duration - 1
        itinerary.append({
            "day_range": f"Day {s}-{end_day}",
            "place": city
        })
    return itinerary

def main():
    all_cities = list(cities_durations.keys())
    valid_itinerary = None

    # Search for a permutation of the 8 cities that meets all conditions:
    # - Valid flight connections between consecutive cities.
    # - Istanbul starts exactly on day 12.
    # - Bucharest covers a workshop day between day 16 and 19.
    # - The overall itinerary finishes on day 23.
    for order in itertools.permutations(all_cities):
        start_days = compute_start_days(order, cities_durations)
        if itinerary_valid(order, start_days):
            valid_itinerary = build_itinerary(order, start_days)
            break

    # Prepare the result.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": valid_itinerary}

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()

------------------------------------------------
# Expected Output (one example itinerary):
# {
#   "itinerary": [
#     { "day_range": "Day 1-4",  "place": "Florence" },
#     { "day_range": "Day 4-5",  "place": "Vienna" },
#     { "day_range": "Day 5-8",  "place": "Reykjavik" },
#     { "day_range": "Day 8-12", "place": "Stuttgart" },
#     { "day_range": "Day 12-13", "place": "Istanbul" },
#     { "day_range": "Day 13-16", "place": "Bucharest" },
#     { "day_range": "Day 16-20", "place": "Manchester" },
#     { "day_range": "Day 20-23", "place": "Riga" }
#   ]
# }
  
In this corrected version all stray non‑printable characters have been removed, so the code should execute without syntax errors.