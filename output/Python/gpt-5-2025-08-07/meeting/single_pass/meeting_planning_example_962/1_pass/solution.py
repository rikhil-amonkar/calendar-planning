import json
import re
from functools import lru_cache

# ----------------------------
# Helper functions for time
# ----------------------------

def parse_time_12h(tstr):
    # e.g., '7:00PM', '10:45AM'
    tstr = tstr.strip().upper()
    m = re.match(r'^(\d{1,2}):(\d{2})(AM|PM)$', tstr)
    if not m:
        raise ValueError(f"Bad time string: {tstr}")
    h = int(m.group(1))
    minute = int(m.group(2))
    ampm = m.group(3)
    if h == 12:
        h = 0
    if ampm == 'PM':
        h += 12
    return h * 60 + minute

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# ----------------------------
# Parse travel times
# ----------------------------

travel_data = """
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

def build_travel_matrix(data):
    travel = {}
    for raw in data.strip().splitlines():
        line = raw.strip()
        if not line:
            continue
        line = line.rstrip('.')
        if ':' not in line:
            continue
        pair, minutes_str = line.split(':', 1)
        minutes = int(minutes_str.strip())
        if ' to ' not in pair:
            continue
        frm, to = pair.split(' to ')
        frm = frm.strip()
        to = to.strip()
        travel.setdefault(frm, {})[to] = minutes
    # ensure all locations present and self travel zero
    locations = set(travel.keys())
    for frm in list(travel.keys()):
        for to in travel[frm]:
            locations.add(to)
    for a in locations:
        travel.setdefault(a, {})
        travel[a].setdefault(a, 0)
    return travel

TRAVEL = build_travel_matrix(travel_data)

# ----------------------------
# Constraints (Participants)
# ----------------------------

start_location = "The Castro"
start_time_str = "9:00AM"

people_raw = [
    {"name": "Elizabeth", "location": "Marina District", "start": "7:00PM", "end": "8:45PM", "min_minutes": 105},
    {"name": "Joshua", "location": "Presidio", "start": "8:30AM", "end": "1:15PM", "min_minutes": 105},
    {"name": "Timothy", "location": "North Beach", "start": "7:45PM", "end": "10:00PM", "min_minutes": 90},
    {"name": "David", "location": "Embarcadero", "start": "10:45AM", "end": "12:30PM", "min_minutes": 30},
    {"name": "Kimberly", "location": "Haight-Ashbury", "start": "4:45PM", "end": "9:30PM", "min_minutes": 75},
    {"name": "Lisa", "location": "Golden Gate Park", "start": "5:30PM", "end": "9:45PM", "min_minutes": 45},
    {"name": "Ronald", "location": "Richmond District", "start": "8:00AM", "end": "9:30AM", "min_minutes": 90},
    {"name": "Stephanie", "location": "Alamo Square", "start": "3:30PM", "end": "4:30PM", "min_minutes": 30},
    {"name": "Helen", "location": "Financial District", "start": "5:30PM", "end": "6:30PM", "min_minutes": 45},
    {"name": "Laura", "location": "Sunset District", "start": "5:45PM", "end": "9:15PM", "min_minutes": 90},
]

# Convert to structured list with minutes
people = []
for p in people_raw:
    people.append({
        "name": p["name"],
        "location": p["location"],
        "win_start": parse_time_12h(p["start"]),
        "win_end": parse_time_12h(p["end"]),
        "min_minutes": int(p["min_minutes"]),
    })

start_time = parse_time_12h(start_time_str)

# ----------------------------
# Pre-filter impossible people from the start state
# ----------------------------

def earliest_start_from(start_loc, start_t, person):
    travel = TRAVEL[start_loc][person["location"]]
    arrival = start_t + travel
    return max(arrival, person["win_start"])

filtered_people = []
for p in people:
    es = earliest_start_from(start_location, start_time, p)
    if es + p["min_minutes"] <= p["win_end"]:
        filtered_people.append(p)
# ensure travel self times exist for all locations
for loc in list(TRAVEL.keys()):
    TRAVEL[loc].setdefault(loc, 0)

# Sort people by window end time (for better DFS ordering)
filtered_people.sort(key=lambda x: (x["win_end"], x["win_start"]))

# Map indices for bitmasking
index_map = {i: filtered_people[i] for i in range(len(filtered_people))}
name_to_index = {filtered_people[i]["name"]: i for i in range(len(filtered_people))}

# ----------------------------
# DFS with memoization to maximize number of meetings
# ----------------------------

@lru_cache(maxsize=None)
def dfs(cur_loc, cur_time, remaining_mask):
    best = (0, 0, 0, cur_time, [])  # count, meet_minutes, -travel_minutes, finish_time, schedule
    # Iterate candidates in order of earliest window end
    # Build a list of indices from mask
    candidates = []
    m = remaining_mask
    idx = 0
    while m:
        if m & 1:
            candidates.append(idx)
        idx += 1
        m >>= 1
    # Sort candidates by their window end times for better pruning
    candidates.sort(key=lambda i: (index_map[i]["win_end"], index_map[i]["win_start"]))
    for i in candidates:
        p = index_map[i]
        travel_minutes = TRAVEL[cur_loc][p["location"]]
        arrival = cur_time + travel_minutes
        start_mt = max(arrival, p["win_start"])
        end_mt = start_mt + p["min_minutes"]
        if end_mt > p["win_end"]:
            continue  # infeasible
        # Recurse
        next_mask = remaining_mask & ~(1 << i)
        sub_count, sub_meet, sub_neg_travel, sub_finish, sub_sched = dfs(p["location"], end_mt, next_mask)
        cand = (
            1 + sub_count,
            p["min_minutes"] + sub_meet,
            -(travel_minutes) + sub_neg_travel,  # we maximize -travel (i.e., minimize travel)
            sub_finish if sub_sched else end_mt,
            [{"action": "meet",
              "location": p["location"],
              "person": p["name"],
              "start_time": minutes_to_str(start_mt),
              "end_time": minutes_to_str(end_mt)}] + sub_sched
        )
        # Compare candidates:
        # 1) max meetings
        # 2) max total meeting minutes
        # 3) max -travel (i.e., min travel)
        # 4) min finish time
        if (cand[0] > best[0] or
            (cand[0] == best[0] and cand[1] > best[1]) or
            (cand[0] == best[0] and cand[1] == best[1] and cand[2] > best[2]) or
            (cand[0] == best[0] and cand[1] == best[1] and cand[2] == best[2] and cand[3] < best[3])
           ):
            best = cand
    return best

# Build initial remaining mask
remaining_mask = 0
for i in range(len(filtered_people)):
    remaining_mask |= (1 << i)

# Compute best itinerary
count, meet_minutes, neg_travel, finish_time_val, schedule = dfs(start_location, start_time, remaining_mask)

# Sort the schedule by chronological order just in case (should already be ordered)
def time_key(entry):
    h, m = map(int, entry["start_time"].split(':'))
    return h * 60 + m
schedule.sort(key=time_key)

output = {
    "itinerary": schedule
}

print(json.dumps(output, ensure_ascii=False, indent=2))