import json

# Helper to convert minutes to "H:MM" 24-hour format without leading zero for hour
def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (in minutes)
travel = {
    "Richmond District": {
        "Chinatown": 20, "Sunset District": 11, "Alamo Square": 13, "Financial District": 22,
        "North Beach": 17, "Embarcadero": 19, "Presidio": 7, "Golden Gate Park": 9, "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20, "Sunset District": 29, "Alamo Square": 17, "Financial District": 5,
        "North Beach": 3, "Embarcadero": 5, "Presidio": 19, "Golden Gate Park": 23, "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12, "Chinatown": 30, "Alamo Square": 17, "Financial District": 30,
        "North Beach": 28, "Embarcadero": 30, "Presidio": 16, "Golden Gate Park": 11, "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11, "Chinatown": 15, "Sunset District": 16, "Financial District": 17,
        "North Beach": 15, "Embarcadero": 16, "Presidio": 17, "Golden Gate Park": 9, "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21, "Chinatown": 5, "Sunset District": 30, "Alamo Square": 17,
        "North Beach": 7, "Embarcadero": 4, "Presidio": 22, "Golden Gate Park": 23, "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18, "Chinatown": 6, "Sunset District": 27, "Alamo Square": 16,
        "Financial District": 8, "Embarcadero": 6, "Presidio": 17, "Golden Gate Park": 22, "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21, "Chinatown": 7, "Sunset District": 30, "Alamo Square": 19,
        "Financial District": 5, "North Beach": 5, "Presidio": 20, "Golden Gate Park": 25, "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7, "Chinatown": 21, "Sunset District": 15, "Alamo Square": 19,
        "Financial District": 23, "North Beach": 18, "Embarcadero": 20, "Golden Gate Park": 12, "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7, "Chinatown": 23, "Sunset District": 10, "Alamo Square": 9,
        "Financial District": 26, "North Beach": 23, "Embarcadero": 25, "Presidio": 11, "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25, "Chinatown": 19, "Sunset District": 23, "Alamo Square": 16,
        "Financial District": 19, "North Beach": 22, "Embarcadero": 19, "Presidio": 32, "Golden Gate Park": 22
    }
}

# Friends constraints
friends = [
    {"name": "Robert",  "location": "Chinatown",         "start": 7*60+45,  "end": 17*60+30, "min_dur": 120},
    {"name": "David",   "location": "Sunset District",   "start": 12*60+30, "end": 19*60+45, "min_dur": 45},
    {"name": "Matthew", "location": "Alamo Square",      "start": 8*60+45,  "end": 13*60+45, "min_dur": 90},
    {"name": "Jessica", "location": "Financial District","start": 9*60+30,  "end": 18*60+45, "min_dur": 45},
    {"name": "Melissa", "location": "North Beach",       "start": 7*60+15,  "end": 16*60+45, "min_dur": 45},
    {"name": "Mark",    "location": "Embarcadero",       "start": 15*60+15, "end": 17*60,    "min_dur": 45},
    {"name": "Deborah", "location": "Presidio",          "start": 19*60,    "end": 19*60+45, "min_dur": 45},
    {"name": "Karen",   "location": "Golden Gate Park",  "start": 19*60+30, "end": 22*60,    "min_dur": 120},
    {"name": "Laura",   "location": "Bayview",           "start": 21*60+15, "end": 22*60+15, "min_dur": 15},
]

start_location = "Richmond District"
start_time = 9*60  # 9:00

# DFS to explore sequences and choose optimal by:
# 1) maximize number of meetings
# 2) minimize total waiting time
# 3) minimize end time
# 4) minimize total travel time
best_solution = {
    "path": [],
    "count": 0,
    "wait": float('inf'),
    "end_time": float('inf'),
    "travel": float('inf')
}

# For initial baseline, set best to empty schedule with zero wait and travel and end at start_time
best_solution = {
    "path": [],
    "count": 0,
    "wait": 0,
    "end_time": start_time,
    "travel": 0
}

def better(sol_a, sol_b):
    # Return True if sol_a is better than sol_b per criteria.
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    if sol_a["wait"] != sol_b["wait"]:
        return sol_a["wait"] < sol_b["wait"]
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    if sol_a["travel"] != sol_b["travel"]:
        return sol_a["travel"] < sol_b["travel"]
    return False

def dfs(current_loc, current_time, remaining, path, total_wait, total_travel):
    global best_solution

    # Evaluate current path as a candidate
    current_sol = {
        "path": path[:],
        "count": len(path),
        "wait": total_wait,
        "end_time": current_time if path else start_time,
        "travel": total_travel
    }
    if better(current_sol, best_solution):
        best_solution = current_sol

    # Try to extend with each remaining friend
    for i, friend in enumerate(remaining):
        dest = friend["location"]
        # If no direct travel time defined (shouldn't happen), skip
        if current_loc not in travel or dest not in travel[current_loc]:
            continue
        t_travel = travel[current_loc][dest]
        arrival = current_time + t_travel
        start_mt = max(arrival, friend["start"])
        end_mt = start_mt + friend["min_dur"]
        if end_mt <= friend["end"]:
            wait_here = max(0, start_mt - arrival)
            new_meet = {
                "action": "meet",
                "location": dest,
                "person": friend["name"],
                "start_time": minutes_to_str(start_mt),
                "end_time": minutes_to_str(end_mt)
            }
            new_remaining = remaining[:i] + remaining[i+1:]
            dfs(
                dest,
                end_mt,
                new_remaining,
                path + [new_meet],
                total_wait + wait_here,
                total_travel + t_travel
            )
        else:
            # Prune if cannot meet this friend at all from current state
            continue

# Start DFS
dfs(start_location, start_time, friends, [], 0, 0)

# Output result as JSON with the required structure
output = {
    "itinerary": best_solution["path"]
}
print(json.dumps(output, ensure_ascii=False))