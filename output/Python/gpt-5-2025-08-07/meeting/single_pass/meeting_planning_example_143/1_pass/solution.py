import json
from itertools import permutations

# Helper functions for time conversion
def to_minutes(tstr):
    # tstr format: 'H:MM'
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)
start_location = "North Beach"
arrival_time_str = "9:00"  # 24-hour format without leading zero on hour
arrival_time = to_minutes(arrival_time_str)

travel_minutes = {
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Pacific Heights"): 11,
}
# Ensure zero travel time for staying in place
locations = {"North Beach", "Pacific Heights", "Embarcadero"}
for loc in locations:
    travel_minutes[(loc, loc)] = 0

friends = [
    {
        "name": "Karen",
        "location": "Pacific Heights",
        "avail_start": to_minutes("18:45"),
        "avail_end": to_minutes("20:15"),
        "min_meet": 90,
    },
    {
        "name": "Mark",
        "location": "Embarcadero",
        "avail_start": to_minutes("13:00"),
        "avail_end": to_minutes("17:45"),
        "min_meet": 120,
    },
]

# Core search algorithm to maximize number of friends met, then total meeting time
from functools import lru_cache

# Convert friends list to tuple of indices for immutability in cache
friend_indices = tuple(range(len(friends)))

@lru_cache(maxsize=None)
def best_plan(current_time, current_loc, remaining_tuple):
    # remaining_tuple is a tuple of friend indices not yet met
    if not remaining_tuple:
        return (0, 0, [])  # (count, total_minutes, schedule)

    best = (0, 0, [])
    remaining = list(remaining_tuple)

    # Try meeting each remaining friend next
    for idx in remaining:
        f = friends[idx]
        travel_time = travel_minutes[(current_loc, f["location"])]
        earliest_arrival = current_time + travel_time
        start = max(earliest_arrival, f["avail_start"])
        latest_end = f["avail_end"]
        min_end = start + f["min_meet"]

        if min_end > latest_end:
            # Can't meet this friend; skip
            continue

        # Explore possible end times from minimum required up to their availability end
        # Step 1 minute to fully explore options (spaces are small)
        for end in range(min_end, latest_end + 1):
            # Recurse for the rest
            rem_next = tuple(x for x in remaining if x != idx)
            sub_count, sub_minutes, sub_schedule = best_plan(end, f["location"], rem_next)
            total_count = 1 + sub_count
            total_minutes = (end - start) + sub_minutes

            candidate_schedule = [{
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": to_timestr(start),
                "end_time": to_timestr(end),
            }] + sub_schedule

            # Choose best by:
            # 1) max number of friends met
            # 2) max total meeting minutes
            # 3) earliest final end time (tie-breaker)
            current_best_end = best[2][-1]["end_time"] if best[2] else to_timestr(10**9)
            candidate_final_end = candidate_schedule[-1]["end_time"] if candidate_schedule else to_timestr(10**9)

            if (total_count > best[0] or
               (total_count == best[0] and total_minutes > best[1]) or
               (total_count == best[0] and total_minutes == best[1] and
                to_minutes(candidate_final_end) < to_minutes(current_best_end))):
                best = (total_count, total_minutes, candidate_schedule)

    # Also consider the option of meeting no one else from here
    if best[0] == 0:
        return (0, 0, [])
    return best

# Run the search starting from arrival state
count, minutes_total, itinerary = best_plan(arrival_time, start_location, friend_indices)

# Ensure itinerary is sorted chronologically (should already be due to construction)
itinerary_sorted = sorted(itinerary, key=lambda x: to_minutes(x["start_time"]))

output = {
    "itinerary": itinerary_sorted
}

print(json.dumps(output, ensure_ascii=False))