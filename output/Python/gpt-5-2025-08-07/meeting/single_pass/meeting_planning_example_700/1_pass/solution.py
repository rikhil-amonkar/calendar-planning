import json
from functools import lru_cache

# Time utilities
def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes), directed
dist = {
    "Presidio": {
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18,
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23,
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6,
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11,
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15,
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Nob Hill": 27,
        "North Beach": 28,
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "North Beach": 8,
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7,
    },
}

# Friends constraints
friends = [
    {
        "name": "Kevin",
        "location": "Pacific Heights",
        "start": parse_time("7:15"),
        "end": parse_time("8:45"),
        "min_duration": 90,
    },
    {
        "name": "Michelle",
        "location": "Golden Gate Park",
        "start": parse_time("20:00"),
        "end": parse_time("21:00"),
        "min_duration": 15,
    },
    {
        "name": "Emily",
        "location": "Fisherman's Wharf",
        "start": parse_time("16:15"),
        "end": parse_time("19:00"),
        "min_duration": 30,
    },
    {
        "name": "Mark",
        "location": "Marina District",
        "start": parse_time("18:15"),
        "end": parse_time("19:45"),
        "min_duration": 75,
    },
    {
        "name": "Barbara",
        "location": "Alamo Square",
        "start": parse_time("17:00"),
        "end": parse_time("19:00"),
        "min_duration": 120,
    },
    {
        "name": "Laura",
        "location": "Sunset District",
        "start": parse_time("19:00"),
        "end": parse_time("21:15"),
        "min_duration": 75,
    },
    {
        "name": "Mary",
        "location": "Nob Hill",
        "start": parse_time("17:30"),
        "end": parse_time("19:00"),
        "min_duration": 45,
    },
    {
        "name": "Helen",
        "location": "North Beach",
        "start": parse_time("11:00"),
        "end": parse_time("12:15"),
        "min_duration": 45,
    },
]

# Start state
start_location = "Presidio"
start_time = parse_time("9:00")

# Map friend index by name to keep reference
friend_indices = {f["name"]: i for i, f in enumerate(friends)}

# Helper to compute earliest feasible meeting window starting at/after given arrival
def schedule_meeting(current_loc, current_time, friend):
    travel_time = dist[current_loc][friend["location"]]
    arrival = current_time + travel_time
    start = max(arrival, friend["start"])
    end = start + friend["min_duration"]
    if end <= friend["end"]:
        return start, end
    return None

# Comparison helper for solutions
def better(sol_a, sol_b):
    # sol = (count, total_minutes, -finish_time, itinerary)
    if sol_a[0] != sol_b[0]:
        return sol_a[0] > sol_b[0]
    if sol_a[1] != sol_b[1]:
        return sol_a[1] > sol_b[1]
    return sol_a[2] > sol_b[2]  # since negative finish time, higher is better (earlier finish)

@lru_cache(maxsize=None)
def dfs(current_loc, current_time, visited_mask):
    best = (0, 0, -current_time, tuple())  # no further meetings
    n = len(friends)
    for i in range(n):
        if (visited_mask >> i) & 1:
            continue
        friend = friends[i]
        # Try to meet this friend next
        sch = schedule_meeting(current_loc, current_time, friend)
        if sch is None:
            continue
        start_i, end_i = sch
        next_loc = friend["location"]
        next_time = end_i
        next_mask = visited_mask | (1 << i)
        sub_count, sub_minutes, sub_neg_finish, sub_itin = dfs(next_loc, next_time, next_mask)
        count = 1 + sub_count
        minutes = (end_i - start_i) + sub_minutes
        neg_finish = sub_neg_finish  # finish time determined by remainder
        itinerary = ((i, start_i, end_i),) + sub_itin
        candidate = (count, minutes, neg_finish, itinerary)
        if better(candidate, best):
            best = candidate
    return best

# Run DFS from start
best_count, best_minutes, best_neg_finish, best_itinerary = dfs(start_location, start_time, 0)

# Convert itinerary to list of dicts and then extend meetings to maximize durations within feasibility
def extend_itinerary(itin):
    # itin is tuple of (i, start, end) with minimum durations
    extended = []
    n = len(itin)
    for idx, (fi, s, e) in enumerate(itin):
        friend = friends[fi]
        # Base maximum end within friend's availability
        max_end = friend["end"]
        # Constrain by next meeting's travel and start
        if idx + 1 < n:
            next_fi, next_s, next_e = itin[idx + 1]
            cur_loc = friend["location"]
            next_loc = friends[next_fi]["location"]
            travel_time = dist[cur_loc][next_loc]
            latest_end_to_make_next = next_s - travel_time
            if latest_end_to_make_next < max_end:
                max_end = latest_end_to_make_next
        # Ensure not earlier than current end
        extended_end = max(e, max_end)
        # But don't allow to exceed max_end
        extended_end = min(max_end, max(e, s + friend["min_duration"]))
        # Also ensure extended_end >= e
        extended_end = max(extended_end, e)
        extended.append((fi, s, extended_end))
    return extended

extended_itinerary = extend_itinerary(best_itinerary)

# Build JSON output
output = {"itinerary": []}
for fi, s, e in extended_itinerary:
    f = friends[fi]
    output["itinerary"].append({
        "action": "meet",
        "location": f["location"],
        "person": f["name"],
        "start_time": fmt_time(s),
        "end_time": fmt_time(e),
    })

print(json.dumps(output, ensure_ascii=False))