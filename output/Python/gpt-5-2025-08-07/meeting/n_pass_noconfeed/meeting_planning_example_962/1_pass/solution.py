import re
import json
from functools import lru_cache

# ----------------------------
# Input data (as variables)
# ----------------------------

arrival_location = "The Castro"
arrival_time_str = "9:00AM"

travel_data_text = """
The Castro to Marina District: 21.
The Castro to Presidio: 20.
The Castro to North Beach: 20.
The Castro to Embarcadero: 22.
The Castro to Haight-Ashbury: 6.
The Castro to Golden Gate Park: 11.
The Castro to Richmond District: 16.
The Castro to Alamo Square: 8.
The Castro to Financial District: 21.
The Castro to Sunset District: 17.
Marina District to The Castro: 22.
Marina District to Presidio: 10.
Marina District to North Beach: 11.
Marina District to Embarcadero: 14.
Marina District to Haight-Ashbury: 16.
Marina District to Golden Gate Park: 18.
Marina District to Richmond District: 11.
Marina District to Alamo Square: 15.
Marina District to Financial District: 17.
Marina District to Sunset District: 19.
Presidio to The Castro: 21.
Presidio to Marina District: 11.
Presidio to North Beach: 18.
Presidio to Embarcadero: 20.
Presidio to Haight-Ashbury: 15.
Presidio to Golden Gate Park: 12.
Presidio to Richmond District: 7.
Presidio to Alamo Square: 19.
Presidio to Financial District: 23.
Presidio to Sunset District: 15.
North Beach to The Castro: 23.
North Beach to Marina District: 9.
North Beach to Presidio: 17.
North Beach to Embarcadero: 6.
North Beach to Haight-Ashbury: 18.
North Beach to Golden Gate Park: 22.
North Beach to Richmond District: 18.
North Beach to Alamo Square: 16.
North Beach to Financial District: 8.
North Beach to Sunset District: 27.
Embarcadero to The Castro: 25.
Embarcadero to Marina District: 12.
Embarcadero to Presidio: 20.
Embarcadero to North Beach: 5.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Richmond District: 21.
Embarcadero to Alamo Square: 19.
Embarcadero to Financial District: 5.
Embarcadero to Sunset District: 30.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Richmond District: 10.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Financial District: 21.
Haight-Ashbury to Sunset District: 15.
Golden Gate Park to The Castro: 13.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Presidio: 11.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Richmond District: 7.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to Financial District: 26.
Golden Gate Park to Sunset District: 10.
Richmond District to The Castro: 16.
Richmond District to Marina District: 9.
Richmond District to Presidio: 7.
Richmond District to North Beach: 17.
Richmond District to Embarcadero: 19.
Richmond District to Haight-Ashbury: 10.
Richmond District to Golden Gate Park: 9.
Richmond District to Alamo Square: 13.
Richmond District to Financial District: 22.
Richmond District to Sunset District: 11.
Alamo Square to The Castro: 8.
Alamo Square to Marina District: 15.
Alamo Square to Presidio: 17.
Alamo Square to North Beach: 15.
Alamo Square to Embarcadero: 16.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Golden Gate Park: 9.
Alamo Square to Richmond District: 11.
Alamo Square to Financial District: 17.
Alamo Square to Sunset District: 16.
Financial District to The Castro: 20.
Financial District to Marina District: 15.
Financial District to Presidio: 22.
Financial District to North Beach: 7.
Financial District to Embarcadero: 4.
Financial District to Haight-Ashbury: 19.
Financial District to Golden Gate Park: 23.
Financial District to Richmond District: 21.
Financial District to Alamo Square: 17.
Financial District to Sunset District: 30.
Sunset District to The Castro: 17.
Sunset District to Marina District: 21.
Sunset District to Presidio: 16.
Sunset District to North Beach: 28.
Sunset District to Embarcadero: 30.
Sunset District to Haight-Ashbury: 15.
Sunset District to Golden Gate Park: 11.
Sunset District to Richmond District: 12.
Sunset District to Alamo Square: 17.
Sunset District to Financial District: 30.
"""

friends_raw = [
    # name, location, start, end, min_minutes
    ("Elizabeth", "Marina District", "7:00PM", "8:45PM", 105),
    ("Joshua", "Presidio", "8:30AM", "1:15PM", 105),
    ("Timothy", "North Beach", "7:45PM", "10:00PM", 90),
    ("David", "Embarcadero", "10:45AM", "12:30PM", 30),
    ("Kimberly", "Haight-Ashbury", "4:45PM", "9:30PM", 75),
    ("Lisa", "Golden Gate Park", "5:30PM", "9:45PM", 45),
    ("Ronald", "Richmond District", "8:00AM", "9:30AM", 90),
    ("Stephanie", "Alamo Square", "3:30PM", "4:30PM", 30),
    ("Helen", "Financial District", "5:30PM", "6:30PM", 45),
    ("Laura", "Sunset District", "5:45PM", "9:15PM", 90),
]

# ----------------------------
# Helpers
# ----------------------------

def parse_travel(text):
    travel = {}
    pattern = re.compile(r"^(.*?) to (.*?): (\d+)\.$")
    for line in text.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        m = pattern.match(line)
        if not m:
            continue
        a, b, t = m.group(1), m.group(2), int(m.group(3))
        travel.setdefault(a, {})[b] = t
    return travel

def parse_time_to_minutes(s):
    s = s.strip().upper()
    m = re.match(r"^(\d{1,2}):(\d{2})(AM|PM)$", s)
    if not m:
        raise ValueError(f"Bad time: {s}")
    h, mi, ap = int(m.group(1)), int(m.group(2)), m.group(3)
    if ap == "AM":
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + mi

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# ----------------------------
# Build data structures
# ----------------------------

travel = parse_travel(travel_data_text)

arrival_time = parse_time_to_minutes(arrival_time_str)

friends = []
for name, location, start_str, end_str, min_min in friends_raw:
    start = parse_time_to_minutes(start_str)
    end = parse_time_to_minutes(end_str)
    friends.append({
        "name": name,
        "location": location,
        "start": start,
        "end": end,
        "min": min_min
    })

# ----------------------------
# Scheduling (search)
# ----------------------------

# Order friends by window end (heuristic)
friends_sorted = sorted(friends, key=lambda f: f["end"])
name_to_friend = {f["name"]: f for f in friends_sorted}
all_names = tuple(f["name"] for f in friends_sorted)

@lru_cache(maxsize=None)
def backtrack(cur_time, cur_loc, remaining_names):
    remaining = [name_to_friend[n] for n in remaining_names]
    # Global best baseline: no more meetings
    best = {
        "count": 0,
        "total_meet_minutes": 0,
        "itinerary": [],
        "end_time": cur_time
    }

    # Upper bound pruning: if even meeting all remaining won't beat best (handled by caller using memoization)
    # We cannot access a global "best so far" due to memoization design; rely on recursion exploration.

    # Try scheduling any of the remaining friends next
    for i, friend in enumerate(remaining):
        loc = friend["location"]
        # If there is no travel defined, skip (shouldn't happen)
        if cur_loc not in travel or loc not in travel[cur_loc]:
            continue
        travel_minutes = travel[cur_loc][loc]
        arrive = cur_time + travel_minutes
        earliest_start = max(arrive, friend["start"])
        latest_start = min(max(arrive, friend["start"]), friend["end"] - friend["min"])
        if latest_start < earliest_start:
            # Can't fit this friend
            continue

        candidate_starts = [earliest_start]
        if latest_start != earliest_start:
            candidate_starts.append(latest_start)

        # Evaluate both earliest and latest feasible starts
        for start_time in candidate_starts:
            end_time = start_time + friend["min"]
            if end_time > friend["end"]:
                continue

            next_remaining = list(remaining_names)
            next_remaining.remove(friend["name"])
            next_remaining = tuple(next_remaining)

            result = backtrack(end_time, loc, next_remaining)

            schedule = [{
                "action": "meet",
                "location": loc,
                "person": friend["name"],
                "start_time": minutes_to_str(start_time),
                "end_time": minutes_to_str(end_time)
            }] + result["itinerary"]

            count = 1 + result["count"]
            total_meet_minutes = friend["min"] + result["total_meet_minutes"]
            final_end_time = result["end_time"]

            # Choose best: maximize count, then maximize total_meet_minutes,
            # then prefer earlier final end_time (frees up evening), then shorter wait before first meeting
            if (count > best["count"] or
                (count == best["count"] and total_meet_minutes > best["total_meet_minutes"]) or
                (count == best["count"] and total_meet_minutes == best["total_meet_minutes"] and final_end_time < best["end_time"])):
                best = {
                    "count": count,
                    "total_meet_minutes": total_meet_minutes,
                    "itinerary": schedule,
                    "end_time": final_end_time
                }

    return best

result = backtrack(arrival_time, arrival_location, all_names)

# Output as required JSON
output = {
    "itinerary": result["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))