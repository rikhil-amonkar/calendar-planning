# SOLUTION:
import json
from functools import lru_cache

# Helper functions for time handling
def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (in minutes) between locations
travel = {
    "Bayview": {
        "North Beach": 22,
        "Fisherman's Wharf": 25,
        "Haight-Ashbury": 19,
        "Nob Hill": 20,
        "Golden Gate Park": 22,
        "Union Square": 18,
        "Alamo Square": 16,
        "Presidio": 32,
        "Chinatown": 19,
        "Pacific Heights": 23,
    },
    "North Beach": {
        "Bayview": 25,
        "Fisherman's Wharf": 5,
        "Haight-Ashbury": 18,
        "Nob Hill": 7,
        "Golden Gate Park": 22,
        "Union Square": 7,
        "Alamo Square": 16,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8,
    },
    "Fisherman's Wharf": {
        "Bayview": 26,
        "North Beach": 6,
        "Haight-Ashbury": 22,
        "Nob Hill": 11,
        "Golden Gate Park": 25,
        "Union Square": 13,
        "Alamo Square": 21,
        "Presidio": 17,
        "Chinatown": 12,
        "Pacific Heights": 12,
    },
    "Haight-Ashbury": {
        "Bayview": 18,
        "North Beach": 19,
        "Fisherman's Wharf": 23,
        "Nob Hill": 15,
        "Golden Gate Park": 7,
        "Union Square": 19,
        "Alamo Square": 5,
        "Presidio": 15,
        "Chinatown": 19,
        "Pacific Heights": 12,
    },
    "Nob Hill": {
        "Bayview": 19,
        "North Beach": 8,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 13,
        "Golden Gate Park": 17,
        "Union Square": 7,
        "Alamo Square": 11,
        "Presidio": 17,
        "Chinatown": 6,
        "Pacific Heights": 8,
    },
    "Golden Gate Park": {
        "Bayview": 23,
        "North Beach": 23,
        "Fisherman's Wharf": 24,
        "Haight-Ashbury": 7,
        "Nob Hill": 20,
        "Union Square": 22,
        "Alamo Square": 9,
        "Presidio": 11,
        "Chinatown": 23,
        "Pacific Heights": 16,
    },
    "Union Square": {
        "Bayview": 15,
        "North Beach": 10,
        "Fisherman's Wharf": 15,
        "Haight-Ashbury": 18,
        "Nob Hill": 9,
        "Golden Gate Park": 22,
        "Alamo Square": 15,
        "Presidio": 24,
        "Chinatown": 7,
        "Pacific Heights": 15,
    },
    "Alamo Square": {
        "Bayview": 16,
        "North Beach": 15,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 5,
        "Nob Hill": 11,
        "Golden Gate Park": 9,
        "Union Square": 14,
        "Presidio": 17,
        "Chinatown": 15,
        "Pacific Heights": 10,
    },
    "Presidio": {
        "Bayview": 31,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Haight-Ashbury": 15,
        "Nob Hill": 18,
        "Golden Gate Park": 12,
        "Union Square": 22,
        "Alamo Square": 19,
        "Chinatown": 21,
        "Pacific Heights": 11,
    },
    "Chinatown": {
        "Bayview": 20,
        "North Beach": 3,
        "Fisherman's Wharf": 8,
        "Haight-Ashbury": 19,
        "Nob Hill": 9,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Alamo Square": 17,
        "Presidio": 19,
        "Pacific Heights": 10,
    },
    "Pacific Heights": {
        "Bayview": 22,
        "North Beach": 9,
        "Fisherman's Wharf": 13,
        "Haight-Ashbury": 11,
        "Nob Hill": 8,
        "Golden Gate Park": 15,
        "Union Square": 12,
        "Alamo Square": 10,
        "Presidio": 11,
        "Chinatown": 11,
    },
}
# Ensure self travel time is 0
for a in list(travel.keys()):
    travel[a][a] = 0

# Participants and constraints
people = [
    {"name": "Brian", "location": "North Beach", "start": to_min("13:00"), "end": to_min("19:00"), "min": 90},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": to_min("11:00"), "end": to_min("12:45"), "min": 60},
    {"name": "Ashley", "location": "Haight-Ashbury", "start": to_min("15:00"), "end": to_min("20:30"), "min": 90},
    {"name": "Elizabeth", "location": "Nob Hill", "start": to_min("11:45"), "end": to_min("18:30"), "min": 75},
    {"name": "Jessica", "location": "Golden Gate Park", "start": to_min("20:00"), "end": to_min("21:45"), "min": 105},
    {"name": "Deborah", "location": "Union Square", "start": to_min("17:30"), "end": to_min("22:00"), "min": 60},
    {"name": "Kimberly", "location": "Alamo Square", "start": to_min("17:30"), "end": to_min("21:15"), "min": 45},
    {"name": "Matthew", "location": "Presidio", "start": to_min("8:15"), "end": to_min("9:00"), "min": 15},
    {"name": "Kenneth", "location": "Chinatown", "start": to_min("13:45"), "end": to_min("19:30"), "min": 105},
    {"name": "Anthony", "location": "Pacific Heights", "start": to_min("14:15"), "end": to_min("16:00"), "min": 30},
]

# Starting conditions
start_location = "Bayview"
start_time = to_min("9:00")

N = len(people)

# Precompute index for people and simple sums
index_map = {i: p for i, p in enumerate(people)}

# Simple memoization of best known (earliest) time to reach (loc, visited_mask)
best_time_seen = {}

best_solution = {
    "count": 0,
    "total_meeting_minutes": 0,
    "finish_time": start_time,
    "itinerary": []
}

# Sort order hint for DFS: try those that end earlier first to find good schedules quickly
candidate_order = list(range(N))
candidate_order.sort(key=lambda i: (people[i]["end"], people[i]["start"]))

def reachable_count_upper(current_loc, current_time, visited_mask):
    count = 0
    for i in range(N):
        if (visited_mask >> i) & 1:
            continue
        p = people[i]
        tr = travel[current_loc][p["location"]]
        arrival = current_time + tr
        start = max(arrival, p["start"])
        if start + p["min"] <= p["end"]:
            count += 1
    return count

def dfs(current_loc, current_time, visited_mask, itinerary, total_meeting_minutes):
    # Prune using best_time_seen (dominance): if we've been here with same visited set earlier, skip
    key = (current_loc, visited_mask)
    prev_best = best_time_seen.get(key)
    if prev_best is not None and current_time >= prev_best:
        return
    best_time_seen[key] = current_time

    current_count = bin(visited_mask).count("1")

    # Update global best solution if improved
    improved = False
    if (current_count > best_solution["count"] or
       (current_count == best_solution["count"] and total_meeting_minutes > best_solution["total_meeting_minutes"]) or
       (current_count == best_solution["count"] and total_meeting_minutes == best_solution["total_meeting_minutes"] and current_time < best_solution["finish_time"])):
        best_solution["count"] = current_count
        best_solution["total_meeting_minutes"] = total_meeting_minutes
        best_solution["finish_time"] = current_time
        best_solution["itinerary"] = list(itinerary)
        improved = True

    # Upper bound pruning: if even meeting all reachable remaining cannot beat best, stop
    upper = current_count + reachable_count_upper(current_loc, current_time, visited_mask)
    if upper < best_solution["count"]:
        return

    # Try next meetings
    for i in candidate_order:
        if (visited_mask >> i) & 1:
            continue
        p = people[i]
        tr = travel[current_loc][p["location"]]
        arrival = current_time + tr
        start = max(arrival, p["start"])
        end = start + p["min"]
        if end <= p["end"]:
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            })
            dfs(p["location"], end, visited_mask | (1 << i), itinerary, total_meeting_minutes + p["min"])
            itinerary.pop()

# Run DFS from starting point
dfs(start_location, start_time, 0, [], 0)

# Build output JSON
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))