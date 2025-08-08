#!/usr/bin/env python3
import json
import sys

# Define city durations (in days)
durations = {
    "Lyon": 3,
    "Paris": 5,
    "Riga": 2,
    "Berlin": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

# Define direct flight connections (bidirectional)
flights_list = [
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples"),
    ("Berlin", "Nice")
]

# Build a dictionary mapping each city to its set of neighbors.
neighbors = {city: set() for city in durations.keys()}
for (c1, c2) in flights_list:
    neighbors[c1].add(c2)
    neighbors[c2].add(c1)

# Total number of unique days must be 23.
# For an itinerary order [A, B, C, ...] with overlapping flight days,
# total days = durations[A] + sum(durations[X] - 1 for X in B, C, ...)
TOTAL_DAYS = 23

# Event constraints:
# 1. Wedding in Berlin between day 1 and day 2.
#    (We force Berlin as the first city so that its day-range is Day1-2)
# 2. Nice workshop must be attended between day 12 and day 13.
#    For Nice (duration 2) this means its scheduled period must include both day 12 and day 13.
#    We require: start_day(Nice) <= 12 and end_day(Nice) >= 13.
# 3. Stockholm annual show from day 20 to day 22.
#    For Stockholm (duration 3) this means its scheduled period should be exactly Day20-22.
def itinerary_schedule(order):
    # Compute schedule given full order.
    # start_day[0] = 1, and for i>=1: start_day[i] = start_day[i-1] + durations[order[i-1]] - 1.
    start_days = []
    end_days = []
    # First city:
    s = 1
    start_days.append(s)
    end_days.append(s + durations[order[0]] - 1)
    for i in range(1, len(order)):
        s = start_days[i-1] + durations[order[i-1]] - 1  # flight day overlaps
        start_days.append(s)
        end_days.append(s + durations[order[i]] - 1)
    return start_days, end_days

# Check if the full itinerary satisfies overall day count and event constraints.
def valid_itinerary(order, start_days, end_days):
    # Check total unique days
    total_unique = durations[order[0]] + sum(durations[city] - 1 for city in order[1:])
    if total_unique != TOTAL_DAYS:
        return False

    # Berlin wedding: we require Berlin's period includes day 1 or day 2.
    # We forced Berlin as first city so its period is Day1 to Day(1+2-1) = Day1-2.
    if order[0] != "Berlin":
        return False

    # Nice workshop: find Nice in the order and check its scheduled days.
    if "Nice" in order:
        idx = order.index("Nice")
        # Must cover day 12 and 13.
        # That is, start_day <= 12 and end_day >= 13.
        if not (start_days[idx] <= 12 and end_days[idx] >= 13):
            return False
    else:
        return False

    # Stockholm show: find Stockholm in the order.
    if "Stockholm" in order:
        idx = order.index("Stockholm")
        # For duration 3, to cover days 20,21,22 we require start_day == 20 and end_day == 22.
        if not (start_days[idx] == 20 and end_days[idx] == 22):
            return False
    else:
        return False

    return True

# Check if consecutive cities in an order are connected by a direct flight.
def valid_connections(order):
    for i in range(len(order) - 1):
        if order[i+1] not in neighbors[order[i]]:
            return False
    return True

# Backtracking search for a valid itinerary order.
def search_itinerary():
    # We fix Berlin as the first city (to satisfy wedding constraint)
    all_cities = set(durations.keys())
    # Start order with Berlin fixed:
    start_order = ["Berlin"]
    used = {"Berlin"}
    
    results = []
    
    def backtrack(order):
        if len(order) == len(durations):
            # Check flight connections
            if not valid_connections(order):
                return
            # Compute schedule
            s_days, e_days = itinerary_schedule(order)
            # Check overall total days and event constraints
            if valid_itinerary(order, s_days, e_days):
                results.append((order[:], s_days[:], e_days[:]))
            return
        
        # Try to extend the order.
        last = order[-1]
        # For next city, we can try any city not used that is directly reachable
        for city in durations.keys():
            if city in order:
                continue
            # Prune if no direct flight from last to candidate.
            if city not in neighbors[last]:
                continue
            # Add candidate and check partial connection pruning.
            order.append(city)
            backtrack(order)
            order.pop()
    
    backtrack(start_order)
    return results

def main():
    solutions = search_itinerary()
    if not solutions:
        # If no valid itinerary found, output an error message in JSON.
        output = {"itinerary": [], "error": "No valid itinerary found with given constraints."}
        print(json.dumps(output))
        return
    # Take the first valid solution.
    order, start_days, end_days = solutions[0]
    
    # Build list of day-range mappings.
    itinerary_list = []
    for city, s, e in zip(order, start_days, end_days):
        itinerary_list.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()