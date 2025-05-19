#!/usr/bin/env python3
import json
import itertools

# Define cities with required durations
cities = {
    "Naples": 3,
    "Valencia": 5,
    "Stuttgart": 2,
    "Split": 5,
    "Venice": 5,
    "Amsterdam": 4,
    "Nice": 2,
    "Barcelona": 2,
    "Porto": 4
}

# Direct flight connections (bidirectional)
raw_flights = [
    ("Venice", "Nice"),
    ("Naples", "Amsterdam"),
    ("Barcelona", "Nice"),
    ("Amsterdam", "Nice"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "Porto"),
    ("Split", "Stuttgart"),
    ("Split", "Naples"),
    ("Valencia", "Amsterdam"),
    ("Barcelona", "Porto"),
    ("Valencia", "Naples"),
    ("Venice", "Amsterdam"),
    ("Barcelona", "Naples"),
    ("Barcelona", "Valencia"),
    ("Split", "Amsterdam"),
    ("Barcelona", "Venice"),
    ("Stuttgart", "Amsterdam"),
    ("Naples", "Nice"),
    ("Venice", "Naples"),
    ("Porto", "Amsterdam"),
    ("Porto", "Valencia"),
    ("Stuttgart", "Naples"),
    ("Barcelona", "Amsterdam")
]
# Create a set of frozensets to check flights irrespective of direction
flights = set(frozenset(pair) for pair in raw_flights)

# Fixed positions based on constraints:
# We have 9 segments in total:
# S1, S2, S3, S4, S5, S6, S7, S8, S9
# S2 is Barcelona (with workshop between day 5 and 6)
# S3 is Venice (with conference on day 6 and day 10)
# S9 is Nice (to meet friends on day 23 to 24)
fixed_segments = {1: None, 2: "Barcelona", 3: "Venice", 9: "Nice"}

# The overall itinerary must span 24 calendar days.
# The rule: if a flight occurs on day X between cities A and B, day X is counted in both.
# So if each segment i has duration d_i, and there are 9 segments and 8 flights (one between each consecutive pair),
# then total calendar days = (sum of durations) - 8.
# We know sum(durations) for all 9 cities is 32.
# So 32 - 8 = 24 calendar days.
# The timeline is computed as follows:
# Let the first segment start on day 1 and end on day = d1.
# For each next segment, we assume the flight occurs on the first day of the segment,
# meaning the segment starts on the previous segment's end day (overlap) and runs for its duration.
# Thus, if a segment has duration d and starts at day X, it covers days X through X+d-1.
#
# Special constraints based on day numbers:
# - S2 (Barcelona, 2 days) must cover days 5 and 6 so that the workshop (between day 5 and 6) occurs.
#   This forces S1's day range to end exactly on day 5, so S1 must have duration 5.
# - S3 (Venice, 5 days) then will cover days 6 through 10, so the Venice conference on day 6 and day 10 is included.
# - S9 (Nice, 2 days) must cover days 23 and 24 (friend meeting in Nice).
# - Naples (3 days) must appear in one segment and its day range must intersect the range [18,20].
#
# We now decide the ordering:
# Our order (index: city, duration):
# S1: must be chosen from remaining cities with duration 5. Among remaining (excluding Barcelona, Venice, Nice) durations of 5:
# Possibilities: Valencia (5) or Split (5).
#
# The remaining positions S4-S8 will be filled with the rest of the cities from:
# {Naples (3), the other of Valencia/Split (if not used in S1), Stuttgart (2), Amsterdam (4), Porto (4)}
#
# We will perform a brute-force search over candidate orders that satisfy:
# 1. Flight connectivity between consecutive segments.
# 2. The timeline computed gives S2 covering day 5-6, S3 covering day 6-10, and overall itinerary ending on day 24.
# 3. The Naples segment (whichever position it appears) must have an interval intersecting [18,20].
#
# The timeline computation for a given itinerary order:
# Let current_day = 1.
# For each segment i in order:
#   segment i gets day_range = [current_day, current_day + duration - 1]
#   Then update current_day = current_day + duration - 1  (since the last day overlaps when flying to the next city)
# At the end, current_day must equal 24.

def compute_timeline(order):
    # order is a list of 9 cities, in positions 1..9.
    timeline = []
    current_day = 1
    for city in order:
        d = cities[city]
        start = current_day
        end = current_day + d - 1
        timeline.append((start, end))
        current_day = end  # next segment starts on the same last day (overlap)
    return timeline

def valid_flights(order):
    # Check consecutive segments have a direct flight (undirected)
    for i in range(len(order)-1):
        if frozenset({order[i], order[i+1]}) not in flights:
            return False
    return True

def meets_naples_constraint(timeline, order):
    # Find the segment for Naples, if exists (it must appear exactly once since cities are unique)
    # Its day range must intersect [18,20]
    for (start, end), city in zip(timeline, order):
        if city == "Naples":
            # Check if the interval [start, end] intersects with [18,20]
            if end < 18 or start > 20:
                return False
    return True

def main():
    # Fixed segments: positions 2,3,9 are fixed.
    # Positions: 1,4,5,6,7,8 are free.
    # Among free positions, S1 must have duration 5.
    free_positions = [1, 4, 5, 6, 7, 8]
    # The cities not fixed: exclude Barcelona, Venice, Nice from the full list.
    available_cities = set(cities.keys()) - {"Barcelona", "Venice", "Nice"}
    available_cities = list(available_cities)
    
    valid_itinerary = None
    
    # Generate all ways to choose an ordering for the 6 free positions from available_cities
    for perm in itertools.permutations(available_cities, 6):
        # Build a candidate order of 9 segments based on positions 1..9
        # Candidate order: index 1 = perm[0], index2 = "Barcelona", index3 = "Venice",
        # then indices 4-8 = perm[1..5], and index9 = "Nice"
        candidate = [None] * 9
        candidate[0] = perm[0]  # S1
        candidate[1] = "Barcelona"
        candidate[2] = "Venice"
        candidate[3] = perm[1]  # S4
        candidate[4] = perm[2]  # S5
        candidate[5] = perm[3]  # S6
        candidate[6] = perm[4]  # S7
        candidate[7] = perm[5]  # S8
        candidate[8] = "Nice"
        
        # Check S1 must have duration 5 so that it ends on day 5 for the workshop constraint in Barcelona.
        if cities[candidate[0]] != 5:
            continue  # skip if S1 duration is not 5
        
        # Compute timeline based on overlapping flight days.
        timeline = compute_timeline(candidate)
        # S2 (Barcelona) must cover days 5-6, which implies S1 must end exactly on day 5.
        # We already ensured S1 has duration 5, so its day range is [1,5].
        # Then S2 timeline becomes [5, 6] and S3 becomes [6, 10].
        if timeline[1] != (5, 6) or timeline[2] != (6, 10):
            continue
        
        # S9 (Nice) must end on day 24 (covering days 23 and 24) 
        # So after computing all segments, the last segment's day range must be (23,24)
        if timeline[-1] != (23, 24):
            continue
        
        # Check flight connectivity
        if not valid_flights(candidate):
            continue
        
        # Check Naples friend meeting constraint:
        if "Naples" in candidate:
            if not meets_naples_constraint(timeline, candidate):
                continue
        else:
            # Naples must be visited.
            continue

        # If we reached here, candidate is valid.
        valid_itinerary = (candidate, timeline)
        break

    if not valid_itinerary:
        print(json.dumps({"error": "No valid itinerary found"}))
        return

    order, timeline = valid_itinerary
    # Prepare the output as a list of dictionaries with "day_range" and "place"
    output = []
    for (start, end), city in zip(timeline, order):
        output.append({
            "day_range": f"{start}-{end}",
            "place": city
        })
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()