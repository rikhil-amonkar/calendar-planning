# This program computes an optimal meeting schedule given travel times and availability constraints.
# It searches over feasible orders to maximize the number of friends met, and breaks ties by total meeting minutes.

import json
from functools import lru_cache

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def parse_time_str(s):
    # format like '13:30' or '9:00'
    parts = s.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Data
locations = [
    "Bayview",
    "North Beach",
    "Fisherman's Wharf",
    "Haight-Ashbury",
    "Nob Hill",
    "Golden Gate Park",
    "Union Square",
    "Alamo Square",
    "Presidio",
    "Chinatown",
    "Pacific Heights"
]

# Map location names to indices
loc_index = {name: i for i, name in enumerate(locations)}

# Travel times (minutes), directed
travel = {name: {} for name in locations}
def set_t(frm, to, mins):
    travel[frm][to] = mins

# Populate travel times
set_t("Bayview", "North Beach", 22)
set_t("Bayview", "Fisherman's Wharf", 25)
set_t("Bayview", "Haight-Ashbury", 19)
set_t("Bayview", "Nob Hill", 20)
set_t("Bayview", "Golden Gate Park", 22)
set_t("Bayview", "Union Square", 18)
set_t("Bayview", "Alamo Square", 16)
set_t("Bayview", "Presidio", 32)
set_t("Bayview", "Chinatown", 19)
set_t("Bayview", "Pacific Heights", 23)

set_t("North Beach", "Bayview", 25)
set_t("North Beach", "Fisherman's Wharf", 5)
set_t("North Beach", "Haight-Ashbury", 18)
set_t("North Beach", "Nob Hill", 7)
set_t("North Beach", "Golden Gate Park", 22)
set_t("North Beach", "Union Square", 7)
set_t("North Beach", "Alamo Square", 16)
set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Chinatown", 6)
set_t("North Beach", "Pacific Heights", 8)

set_t("Fisherman's Wharf", "Bayview", 26)
set_t("Fisherman's Wharf", "North Beach", 6)
set_t("Fisherman's Wharf", "Haight-Ashbury", 22)
set_t("Fisherman's Wharf", "Nob Hill", 11)
set_t("Fisherman's Wharf", "Golden Gate Park", 25)
set_t("Fisherman's Wharf", "Union Square", 13)
set_t("Fisherman's Wharf", "Alamo Square", 21)
set_t("Fisherman's Wharf", "Presidio", 17)
set_t("Fisherman's Wharf", "Chinatown", 12)
set_t("Fisherman's Wharf", "Pacific Heights", 12)

set_t("Haight-Ashbury", "Bayview", 18)
set_t("Haight-Ashbury", "North Beach", 19)
set_t("Haight-Ashbury", "Fisherman's Wharf", 23)
set_t("Haight-Ashbury", "Nob Hill", 15)
set_t("Haight-Ashbury", "Golden Gate Park", 7)
set_t("Haight-Ashbury", "Union Square", 19)
set_t("Haight-Ashbury", "Alamo Square", 5)
set_t("Haight-Ashbury", "Presidio", 15)
set_t("Haight-Ashbury", "Chinatown", 19)
set_t("Haight-Ashbury", "Pacific Heights", 12)

set_t("Nob Hill", "Bayview", 19)
set_t("Nob Hill", "North Beach", 8)
set_t("Nob Hill", "Fisherman's Wharf", 10)
set_t("Nob Hill", "Haight-Ashbury", 13)
set_t("Nob Hill", "Golden Gate Park", 17)
set_t("Nob Hill", "Union Square", 7)
set_t("Nob Hill", "Alamo Square", 11)
set_t("Nob Hill", "Presidio", 17)
set_t("Nob Hill", "Chinatown", 6)
set_t("Nob Hill", "Pacific Heights", 8)

set_t("Golden Gate Park", "Bayview", 23)
set_t("Golden Gate Park", "North Beach", 23)
set_t("Golden Gate Park", "Fisherman's Wharf", 24)
set_t("Golden Gate Park", "Haight-Ashbury", 7)
set_t("Golden Gate Park", "Nob Hill", 20)
set_t("Golden Gate Park", "Union Square", 22)
set_t("Golden Gate Park", "Alamo Square", 9)
set_t("Golden Gate Park", "Presidio", 11)
set_t("Golden Gate Park", "Chinatown", 23)
set_t("Golden Gate Park", "Pacific Heights", 16)

set_t("Union Square", "Bayview", 15)
set_t("Union Square", "North Beach", 10)
set_t("Union Square", "Fisherman's Wharf", 15)
set_t("Union Square", "Haight-Ashbury", 18)
set_t("Union Square", "Nob Hill", 9)
set_t("Union Square", "Golden Gate Park", 22)
set_t("Union Square", "Alamo Square", 14)
set_t("Union Square", "Presidio", 24)
set_t("Union Square", "Chinatown", 7)
set_t("Union Square", "Pacific Heights", 15)

set_t("Alamo Square", "Bayview", 16)
set_t("Alamo Square", "North Beach", 15)
set_t("Alamo Square", "Fisherman's Wharf", 19)
set_t("Alamo Square", "Haight-Ashbury", 5)
set_t("Alamo Square", "Nob Hill", 11)
set_t("Alamo Square", "Golden Gate Park", 9)
set_t("Alamo Square", "Union Square", 14)
set_t("Alamo Square", "Presidio", 17)
set_t("Alamo Square", "Chinatown", 15)
set_t("Alamo Square", "Pacific Heights", 10)

set_t("Presidio", "Bayview", 31)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Fisherman's Wharf", 19)
set_t("Presidio", "Haight-Ashbury", 15)
set_t("Presidio", "Nob Hill", 18)
set_t("Presidio", "Golden Gate Park", 12)
set_t("Presidio", "Union Square", 22)
set_t("Presidio", "Alamo Square", 19)
set_t("Presidio", "Chinatown", 21)
set_t("Presidio", "Pacific Heights", 11)

set_t("Chinatown", "Bayview", 20)
set_t("Chinatown", "North Beach", 3)
set_t("Chinatown", "Fisherman's Wharf", 8)
set_t("Chinatown", "Haight-Ashbury", 19)
set_t("Chinatown", "Nob Hill", 9)
set_t("Chinatown", "Golden Gate Park", 23)
set_t("Chinatown", "Union Square", 7)
set_t("Chinatown", "Alamo Square", 17)
set_t("Chinatown", "Presidio", 19)
set_t("Chinatown", "Pacific Heights", 10)

set_t("Pacific Heights", "Bayview", 22)
set_t("Pacific Heights", "North Beach", 9)
set_t("Pacific Heights", "Fisherman's Wharf", 13)
set_t("Pacific Heights", "Haight-Ashbury", 11)
set_t("Pacific Heights", "Nob Hill", 8)
set_t("Pacific Heights", "Golden Gate Park", 15)
set_t("Pacific Heights", "Union Square", 12)
set_t("Pacific Heights", "Alamo Square", 10)
set_t("Pacific Heights", "Presidio", 11)
set_t("Pacific Heights", "Chinatown", 11)

# Friends and constraints
friends = [
    {"name": "Brian", "location": "North Beach", "start": parse_time_str("13:00"), "end": parse_time_str("19:00"), "min": 90},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": parse_time_str("11:00"), "end": parse_time_str("12:45"), "min": 60},
    {"name": "Ashley", "location": "Haight-Ashbury", "start": parse_time_str("15:00"), "end": parse_time_str("20:30"), "min": 90},
    {"name": "Elizabeth", "location": "Nob Hill", "start": parse_time_str("11:45"), "end": parse_time_str("18:30"), "min": 75},
    {"name": "Jessica", "location": "Golden Gate Park", "start": parse_time_str("20:00"), "end": parse_time_str("21:45"), "min": 105},
    {"name": "Deborah", "location": "Union Square", "start": parse_time_str("17:30"), "end": parse_time_str("22:00"), "min": 60},
    {"name": "Kimberly", "location": "Alamo Square", "start": parse_time_str("17:30"), "end": parse_time_str("21:15"), "min": 45},
    {"name": "Matthew", "location": "Presidio", "start": parse_time_str("8:15"), "end": parse_time_str("9:00"), "min": 15},
    {"name": "Kenneth", "location": "Chinatown", "start": parse_time_str("13:45"), "end": parse_time_str("19:30"), "min": 105},
    {"name": "Anthony", "location": "Pacific Heights", "start": parse_time_str("14:15"), "end": parse_time_str("16:00"), "min": 30},
]

n = len(friends)

# Precompute friend metadata
for f in friends:
    f["loc_idx"] = loc_index[f["location"]]
    f["latest_start"] = f["end"] - f["min"]

# Start state
start_location = loc_index["Bayview"]
start_time = parse_time_str("9:00")

# Create a list of indices for convenience
indices = list(range(n))

# Order candidates by tighter deadlines to improve pruning
def candidate_order(curr_loc, curr_time, remaining):
    # Sort by latest_start ascending, then by travel time from current location
    return sorted(
        remaining,
        key=lambda i: (friends[i]["latest_start"], travel[locations[curr_loc]].get(friends[i]["location"], 10**6))
    )

# Memoization for search
from functools import lru_cache

@lru_cache(maxsize=None)
def search(curr_loc, curr_time, visited_mask):
    best_count = 0
    best_minutes = 0
    best_schedule = []
    # Remaining friend indices
    remaining = [i for i in indices if not (visited_mask & (1 << i))]
    # Upper bound pruning: even if we could meet all remaining, check if it beats current best (handled implicitly)
    # Try each feasible next meeting
    ordered = candidate_order(curr_loc, curr_time, remaining)
    for i in ordered:
        f = friends[i]
        # Travel time
        if f["location"] not in travel[locations[curr_loc]]:
            continue  # no route
        arrive = curr_time + travel[locations[curr_loc]][f["location"]]
        if arrive > f["latest_start"]:
            continue  # too late to fit minimum
        start_meet = max(arrive, f["start"])
        end_meet = start_meet + f["min"]
        if end_meet > f["end"]:
            continue  # cannot fit within window
        # Recurse
        sub_count, sub_minutes, sub_schedule = search(f["loc_idx"], end_meet, visited_mask | (1 << i))
        # Include current meeting
        total_count = 1 + sub_count
        total_minutes = f["min"] + sub_minutes
        if (total_count > best_count) or (total_count == best_count and total_minutes > best_minutes):
            best_count = total_count
            best_minutes = total_minutes
            this_item = {
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": minutes_to_str(start_meet),
                "end_time": minutes_to_str(end_meet),
            }
            best_schedule = [this_item] + sub_schedule

    return best_count, best_minutes, best_schedule

# Run search
best_count, best_minutes, schedule = search(start_location, start_time, 0)

# Output as JSON
output = {"itinerary": schedule}
print(json.dumps(output, ensure_ascii=False))