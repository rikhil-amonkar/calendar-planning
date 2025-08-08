#!/usr/bin/env python3
import json
import itertools

# Input Variables: Cities, required durations, flight connections, and event constraints.
# Required durations for each city (in days)
durations = {
    "Frankfurt": 4,   # Must attend annual show from Day 13-16 in Frankfurt
    "Manchester": 4,
    "Valencia": 4,
    "Naples": 4,
    "Oslo": 3,
    "Vilnius": 2    # Wedding in Vilnius must be attended between Day 12 and Day 13
}

# Direct flight connections (bidirectional)
# Represent each connection as a frozenset so that order doesn't matter.
flights = {
    frozenset(["Valencia", "Frankfurt"]),
    frozenset(["Manchester", "Frankfurt"]),
    frozenset(["Naples", "Manchester"]),
    frozenset(["Naples", "Frankfurt"]),
    frozenset(["Naples", "Oslo"]),
    frozenset(["Oslo", "Frankfurt"]),
    frozenset(["Vilnius", "Frankfurt"]),
    frozenset(["Oslo", "Vilnius"]),
    frozenset(["Manchester", "Oslo"]),
    frozenset(["Valencia", "Naples"])
}

# Total number of days in the itinerary
total_days = 16

# Event constraints:
# - Annual show in Frankfurt: must be in Frankfurt from Day 13 to Day 16.
# - Wedding in Vilnius: must be attended between Day 12 and Day 13.
# Hence, Frankfurt must be the final city and Vilnius should immediately precede Frankfurt.

# We must visit 6 cities:
# The set of 6 cities is: {Frankfurt, Manchester, Valencia, Naples, Oslo, Vilnius}
# We require Frankfurt to be final and Vilnius to be immediately before it.
# That leaves the other 4 cities: {Valencia, Naples, Manchester, Oslo}
# Additionally, to have a direct flight from the 4th city to Vilnius,
# only Oslo works (since only "Oslo and Vilnius" appears in the flight list).
# Therefore, we must have Oslo as the 4th city.
# For the first three positions, we permute the remaining cities {Valencia, Naples, Manchester}.
# Also note: Valencia does not connect directly to Oslo so it cannot be in position 3.
# Let's search for an ordering that satisfies all flight connections.

# Candidates for the first 4 positions must be a permutation of:
first_four_candidates = ["Valencia", "Naples", "Manchester", "Oslo"]

# The ordering must satisfy:
#  - The 4th city (index 3) must be "Oslo" (to be able to fly direct to Vilnius).
#  - For the first three positions, we choose a permutation of the remaining three cities.
# Then the full itinerary order will be: [three cities in order] + ["Oslo", "Vilnius", "Frankfurt"].
def can_fly(city_a, city_b):
    return frozenset([city_a, city_b]) in flights

valid_itinerary_order = None

# Permute the three cities for positions 0-2 from the set {Valencia, Naples, Manchester}
for order_first_three in itertools.permutations(["Valencia", "Naples", "Manchester"], 3):
    # Construct a candidate order: positions 0-2 are the permutation, position 3 must be Oslo.
    candidate = list(order_first_three) + ["Oslo", "Vilnius", "Frankfurt"]
    
    # Check flight connectivity for consecutive cities.
    valid = True
    for i in range(len(candidate) - 1):
        if not can_fly(candidate[i], candidate[i+1]):
            valid = False
            break
    if not valid:
        continue

    # Now, compute the day ranges for each city.
    # The rule: if you fly on day X, then that day counts for both the departure city and the arrival city.
    # We simulate by setting the start day of the first city as 1,
    # and for each subsequent city, its start day is the same as the previous city's end day.
    day_ranges = []
    current_day = 1
    for city in candidate:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        day_ranges.append((city, start_day, end_day))
        # The flight is on the same day as end_day, so next city starts on end_day.
        current_day = end_day

    # Check total itinerary days match the required total_days.
    if current_day != total_days:
        continue

    # Check event constraints:
    # Frankfurt (last city) must have day range Day 13-16 (4 days).
    # Vilnius (the second to last city) must cover the wedding day between Day 12 and Day 13.
    # Since flights overlap, if Vilnius is scheduled with day_range Day 12-13,
    # the wedding can be attended on Day 12 (or Day 13 before departure).
    frankfurt_range = day_ranges[-1]  # Should be (Frankfurt, 13, 16)
    vilnius_range = day_ranges[-2]    # Should be (Vilnius, 12, 13)
    if frankfurt_range[1] == 13 and frankfurt_range[2] == 16 and vilnius_range[1] == 12 and vilnius_range[2] == 13:
        valid_itinerary_order = (candidate, day_ranges)
        break

# If we have found a valid ordering, build the JSON output.
if valid_itinerary_order is not None:
    order, schedule = valid_itinerary_order
    # Build the itinerary list with the required JSON structure.
    itinerary = []
    for city, start, end in schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    # If no valid itinerary is found, output an error message in JSON.
    output = {"error": "No valid itinerary could be found with the given constraints."}
    print(json.dumps(output))