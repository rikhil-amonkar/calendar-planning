import json
from itertools import permutations

def parse_time(s):
    # s like '10:30AM' or '7:45PM'
    s = s.strip().upper()
    if s.endswith('AM'):
        ampm = 'AM'
    elif s.endswith('PM'):
        ampm = 'PM'
    else:
        raise ValueError(f"Invalid time format: {s}")
    time_part = s[:-2]
    h_str, m_str = time_part.split(':')
    h = int(h_str)
    m = int(m_str)
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (asymmetric)
T = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Union Square": 19,
        "Pacific Heights": 12,
        "Bayview": 18,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Richmond District": 10,
        "Sunset District": 15,
        "Golden Gate Park": 7,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Union Square": 15,
        "Pacific Heights": 16,
        "Bayview": 14,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Richmond District": 20,
        "Sunset District": 24,
        "Golden Gate Park": 17,
    },
    "Union Square": {
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Bayview": 15,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
        "Golden Gate Park": 22,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Union Square": 12,
        "Bayview": 22,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Richmond District": 12,
        "Sunset District": 21,
        "Golden Gate Park": 15,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Union Square": 18,
        "Pacific Heights": 23,
        "Fisherman's Wharf": 25,
        "Marina District": 27,
        "Richmond District": 25,
        "Sunset District": 23,
        "Golden Gate Park": 22,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Union Square": 13,
        "Pacific Heights": 12,
        "Bayview": 26,
        "Marina District": 9,
        "Richmond District": 18,
        "Sunset District": 27,
        "Golden Gate Park": 25,
    },
    "Marina District": {
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Union Square": 16,
        "Pacific Heights": 7,
        "Bayview": 27,
        "Fisherman's Wharf": 10,
        "Richmond District": 11,
        "Sunset District": 19,
        "Golden Gate Park": 18,
    },
    "Richmond District": {
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Union Square": 21,
        "Pacific Heights": 10,
        "Bayview": 27,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Sunset District": 11,
        "Golden Gate Park": 9,
    },
    "Sunset District": {
        "Haight-Ashbury": 15,
        "Mission District": 25,
        "Union Square": 30,
        "Pacific Heights": 21,
        "Bayview": 22,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Richmond District": 12,
        "Golden Gate Park": 11,
    },
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Union Square": 22,
        "Pacific Heights": 16,
        "Bayview": 23,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Richmond District": 7,
        "Sunset District": 10,
    },
}

# Ensure every pair exists to avoid KeyError
locations = list(T.keys())
for a in locations:
    for b in locations:
        if a == b:
            continue
        if b not in T[a]:
            # If missing, conservatively set to a large number (shouldn't happen with provided data)
            T[a][b] = 9999

# Meeting constraints
friends = [
    {
        "person": "Elizabeth",
        "location": "Mission District",
        "start": parse_time("10:30AM"),
        "end": parse_time("8:00PM"),
        "min_duration": 90,
    },
    {
        "person": "David",
        "location": "Union Square",
        "start": parse_time("3:15PM"),
        "end": parse_time("7:00PM"),
        "min_duration": 45,
    },
    {
        "person": "Sandra",
        "location": "Pacific Heights",
        "start": parse_time("7:00AM"),
        "end": parse_time("8:00PM"),
        "min_duration": 120,
    },
    {
        "person": "Thomas",
        "location": "Bayview",
        "start": parse_time("7:30PM"),
        "end": parse_time("8:30PM"),
        "min_duration": 30,
    },
    {
        "person": "Robert",
        "location": "Fisherman's Wharf",
        "start": parse_time("10:00AM"),
        "end": parse_time("3:00PM"),
        "min_duration": 15,
    },
    {
        "person": "Kenneth",
        "location": "Marina District",
        "start": parse_time("10:45AM"),
        "end": parse_time("1:00PM"),
        "min_duration": 45,
    },
    {
        "person": "Melissa",
        "location": "Richmond District",
        "start": parse_time("6:15PM"),
        "end": parse_time("8:00PM"),
        "min_duration": 15,
    },
    {
        "person": "Kimberly",
        "location": "Sunset District",
        "start": parse_time("10:15AM"),
        "end": parse_time("6:15PM"),
        "min_duration": 105,
    },
    {
        "person": "Amanda",
        "location": "Golden Gate Park",
        "start": parse_time("7:45AM"),
        "end": parse_time("6:45PM"),
        "min_duration": 15,
    },
]

start_location = "Haight-Ashbury"
start_time = parse_time("9:00AM")

# DFS with pruning to maximize number of friends met; tie-breaker earliest finish, then min travel
best_solution = {
    "count": 0,
    "end_time": start_time,
    "total_travel": 0,
    "itinerary": [],
}

# Sort friends by window end (earliest-deadline-first) to improve pruning
friends_sorted = sorted(friends, key=lambda f: f["end"])

def dfs(current_loc, current_time, remaining_indices, itinerary, total_travel):
    global best_solution

    # Consider current itinerary as a candidate
    current_count = len(itinerary)
    improved = False
    if current_count > best_solution["count"]:
        improved = True
    elif current_count == best_solution["count"]:
        # Earlier finish preferred; if same, less travel
        if current_time < best_solution["end_time"]:
            improved = True
        elif current_time == best_solution["end_time"] and total_travel < best_solution["total_travel"]:
            improved = True
    if improved:
        best_solution = {
            "count": current_count,
            "end_time": current_time,
            "total_travel": total_travel,
            "itinerary": itinerary[:],
        }

    # Upper bound pruning
    if current_count + len(remaining_indices) < best_solution["count"]:
        return

    # Try each remaining friend as next
    for idx in list(remaining_indices):
        f = friends_sorted[idx]
        travel = T[current_loc][f["location"]]
        arrival = current_time + travel
        start_meet = max(arrival, f["start"])
        end_meet = start_meet + f["min_duration"]
        if end_meet <= f["end"]:
            # feasible
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time": start_meet,
                "end_time": end_meet,
            }]
            new_remaining = remaining_indices.copy()
            new_remaining.remove(idx)
            dfs(f["location"], end_meet, new_remaining, new_itinerary, total_travel + travel)
        else:
            # prune this friend in this branch as infeasible at this point
            continue

# Initial remaining indices correspond to sorted friends list
remaining_indices = list(range(len(friends_sorted)))
dfs(start_location, start_time, remaining_indices, [], 0)

# Convert minutes to formatted strings
output_itinerary = []
for item in best_solution["itinerary"]:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"]),
    })

result = {
    "itinerary": output_itinerary
}

print(json.dumps(result, ensure_ascii=False))