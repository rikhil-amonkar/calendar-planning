import json

def to_minutes(tstr):
    # tstr format 'H:MM' in 24h
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (minutes)
dist = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

# Input variables
arrival_location = "Union Square"
arrival_time = to_minutes("9:00")

people = [
    {"name": "Kevin", "location": "Mission District", "start": to_minutes("20:45"), "end": to_minutes("21:45"), "min_duration": 60},
    {"name": "Mark", "location": "Fisherman's Wharf", "start": to_minutes("17:15"), "end": to_minutes("20:00"), "min_duration": 90},
    {"name": "Jessica", "location": "Russian Hill", "start": to_minutes("9:00"), "end": to_minutes("15:00"), "min_duration": 120},
    {"name": "Jason", "location": "Marina District", "start": to_minutes("15:15"), "end": to_minutes("21:45"), "min_duration": 120},
    {"name": "John", "location": "North Beach", "start": to_minutes("9:45"), "end": to_minutes("18:00"), "min_duration": 15},
    {"name": "Karen", "location": "Chinatown", "start": to_minutes("16:45"), "end": to_minutes("19:00"), "min_duration": 75},
    {"name": "Sarah", "location": "Pacific Heights", "start": to_minutes("17:30"), "end": to_minutes("18:15"), "min_duration": 45},
    {"name": "Amanda", "location": "The Castro", "start": to_minutes("20:00"), "end": to_minutes("21:15"), "min_duration": 60},
    {"name": "Nancy", "location": "Nob Hill", "start": to_minutes("9:45"), "end": to_minutes("13:00"), "min_duration": 45},
    {"name": "Rebecca", "location": "Sunset District", "start": to_minutes("8:45"), "end": to_minutes("15:00"), "min_duration": 75},
]

# Map person to index for bitmasking
name_to_idx = {p["name"]: i for i, p in enumerate(people)}

# DFS with memoization
best_solution = {"count": 0, "end_time": float('inf'), "itinerary": []}
memo = {}

def feasible_meeting(current_loc, current_time, person):
    # Travel time
    travel = dist[current_loc][person["location"]]
    arrival = current_time + travel
    start = max(arrival, person["start"])
    end = start + person["min_duration"]
    if end <= person["end"]:
        return start, end
    return None

def dfs(current_loc, current_time, visited_mask, itinerary):
    global best_solution

    # Memo pruning
    key = (current_loc, current_time, visited_mask)
    prev_best = memo.get(key)
    if prev_best is not None:
        # prev_best: maximum count achieved from this state onward
        # If remaining possible + current itinerary length can't beat best, prune
        if prev_best >= len(itinerary):
            pass
    # We update memo with current count to help prune future identical states
    memo[key] = len(itinerary)

    # Update best solution if improved
    if len(itinerary) > best_solution["count"] or (len(itinerary) == best_solution["count"] and current_time < best_solution["end_time"]):
        best_solution = {
            "count": len(itinerary),
            "end_time": current_time,
            "itinerary": list(itinerary)
        }

    # Generate feasible next meetings
    candidates = []
    for p in people:
        idx = name_to_idx[p["name"]]
        if (visited_mask >> idx) & 1:
            continue
        feas = feasible_meeting(current_loc, current_time, p)
        if feas:
            start, end = feas
            candidates.append((end, start, p))  # sort by earliest finish

    # Sort to explore earliest finishing meetings first (heuristic)
    candidates.sort()

    # Branch
    for end, start, p in candidates:
        idx = name_to_idx[p["name"]]
        new_it = itinerary + [{
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end)
        }]
        dfs(p["location"], end, visited_mask | (1 << idx), new_it)

# Start search
dfs(arrival_location, arrival_time, 0, [])

# Output JSON
print(json.dumps({"itinerary": best_solution["itinerary"]}, ensure_ascii=False))