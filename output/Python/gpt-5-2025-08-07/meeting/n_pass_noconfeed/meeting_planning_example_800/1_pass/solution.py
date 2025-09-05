import json
from copy import deepcopy

# Helper functions for time conversion
def to_minutes(tstr):
    # tstr like '9:00' or '13:30'
    h, m = map(int, tstr.split(':'))
    return h * 60 + m

def to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Union Square": {
        "The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14,
        "Haight-Ashbury": 18
    },
    "The Castro": {
        "Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
        "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7,
        "Haight-Ashbury": 6
    },
    "North Beach": {
        "Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16,
        "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18,
        "Haight-Ashbury": 18
    },
    "Embarcadero": {
        "Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19,
        "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20,
        "Haight-Ashbury": 21
    },
    "Alamo Square": {
        "Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16,
        "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10,
        "Haight-Ashbury": 5
    },
    "Nob Hill": {
        "Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9,
        "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13,
        "Haight-Ashbury": 13
    },
    "Presidio": {
        "Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20,
        "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 19, "Mission District": 26,
        "Haight-Ashbury": 15
    },
    "Fisherman's Wharf": {
        "Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8,
        "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22,
        "Haight-Ashbury": 22
    },
    "Mission District": {
        "Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19,
        "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22,
        "Haight-Ashbury": 12
    },
    "Haight-Ashbury": {
        "Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20,
        "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23,
        "Mission District": 11
    }
}

# Friends constraints
friends = [
    {
        "person": "Melissa",
        "location": "The Castro",
        "start": to_minutes("20:15"),
        "end": to_minutes("21:15"),
        "duration": 30
    },
    {
        "person": "Kimberly",
        "location": "North Beach",
        "start": to_minutes("7:00"),
        "end": to_minutes("10:30"),
        "duration": 15
    },
    {
        "person": "Joseph",
        "location": "Embarcadero",
        "start": to_minutes("15:30"),
        "end": to_minutes("19:30"),
        "duration": 75
    },
    {
        "person": "Barbara",
        "location": "Alamo Square",
        "start": to_minutes("20:45"),
        "end": to_minutes("21:45"),
        "duration": 15
    },
    {
        "person": "Kenneth",
        "location": "Nob Hill",
        "start": to_minutes("12:15"),
        "end": to_minutes("17:15"),
        "duration": 105
    },
    {
        "person": "Joshua",
        "location": "Presidio",
        "start": to_minutes("16:30"),
        "end": to_minutes("18:15"),
        "duration": 105
    },
    {
        "person": "Brian",
        "location": "Fisherman's Wharf",
        "start": to_minutes("9:30"),
        "end": to_minutes("15:30"),
        "duration": 45
    },
    {
        "person": "Steven",
        "location": "Mission District",
        "start": to_minutes("19:30"),
        "end": to_minutes("21:00"),
        "duration": 90
    },
    {
        "person": "Betty",
        "location": "Haight-Ashbury",
        "start": to_minutes("19:00"),
        "end": to_minutes("20:30"),
        "duration": 90
    }
]

start_location = "Union Square"
start_time = to_minutes("9:00")

# DFS search to maximize number of meetings; tie-breakers: total meeting time desc, total travel asc, end time asc
best_solution = {
    "count": 0,
    "meeting_minutes": 0,
    "total_travel": 10**9,
    "end_time": 10**9,
    "itinerary": []
}

def compare_and_update(candidate):
    global best_solution
    # Primary: count (desc)
    if candidate["count"] > best_solution["count"]:
        best_solution = deepcopy(candidate)
        return
    if candidate["count"] < best_solution["count"]:
        return
    # Secondary: total meeting minutes (desc)
    if candidate["meeting_minutes"] > best_solution["meeting_minutes"]:
        best_solution = deepcopy(candidate)
        return
    if candidate["meeting_minutes"] < best_solution["meeting_minutes"]:
        return
    # Tertiary: total travel (asc)
    if candidate["total_travel"] < best_solution["total_travel"]:
        best_solution = deepcopy(candidate)
        return
    if candidate["total_travel"] > best_solution["total_travel"]:
        return
    # Quaternary: end time (asc)
    if candidate["end_time"] < best_solution["end_time"]:
        best_solution = deepcopy(candidate)
        return

def dfs(current_loc, current_time, remaining_indices, itinerary, total_travel, meeting_minutes):
    # Update best with current partial itinerary
    candidate = {
        "count": len(itinerary),
        "meeting_minutes": meeting_minutes,
        "total_travel": total_travel,
        "end_time": current_time,
        "itinerary": deepcopy(itinerary)
    }
    compare_and_update(candidate)

    # Try to add each remaining friend next
    for idx in list(remaining_indices):
        f = friends[idx]
        # If there's no travel path, skip (shouldn't happen with given data)
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            continue

        t_travel = travel[current_loc][f["location"]]
        arrive = current_time + t_travel
        start = max(arrive, f["start"])
        end = start + f["duration"]

        if end <= f["end"]:
            # Feasible to meet
            entry = {
                "action": "meet",
                "location": f["location"],
                "person": f["person"],
                "start_time": to_timestr(start),
                "end_time": to_timestr(end)
            }
            itinerary.append(entry)
            remaining_indices.remove(idx)
            dfs(
                f["location"],
                end,
                remaining_indices,
                itinerary,
                total_travel + t_travel,
                meeting_minutes + f["duration"]
            )
            # backtrack
            remaining_indices.add(idx)
            itinerary.pop()

# Prepare remaining indices as a set for DFS
remaining = set(range(len(friends)))
dfs(start_location, start_time, remaining, [], 0, 0)

# Output best itinerary as JSON
output = {
    "itinerary": best_solution["itinerary"]
}
print(json.dumps(output, ensure_ascii=False))