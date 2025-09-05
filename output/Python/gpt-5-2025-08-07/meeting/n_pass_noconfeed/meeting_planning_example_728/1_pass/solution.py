import json
from itertools import permutations

def minutes(h, m):
    return h * 60 + m

def str_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Marina District"
start_time = minutes(9, 0)  # 9:00

# Travel times (directed, in minutes)
travel = {
    "Marina District": {
        "Mission District": 20, "Fisherman's Wharf": 10, "Presidio": 10,
        "Union Square": 16, "Sunset District": 19, "Financial District": 17,
        "Haight-Ashbury": 16, "Russian Hill": 8
    },
    "Mission District": {
        "Marina District": 19, "Fisherman's Wharf": 22, "Presidio": 25,
        "Union Square": 15, "Sunset District": 24, "Financial District": 15,
        "Haight-Ashbury": 12, "Russian Hill": 15
    },
    "Fisherman's Wharf": {
        "Marina District": 9, "Mission District": 22, "Presidio": 17,
        "Union Square": 13, "Sunset District": 27, "Financial District": 11,
        "Haight-Ashbury": 22, "Russian Hill": 7
    },
    "Presidio": {
        "Marina District": 11, "Mission District": 26, "Fisherman's Wharf": 19,
        "Union Square": 22, "Sunset District": 15, "Financial District": 23,
        "Haight-Ashbury": 15, "Russian Hill": 14
    },
    "Union Square": {
        "Marina District": 18, "Mission District": 14, "Fisherman's Wharf": 15,
        "Presidio": 24, "Sunset District": 27, "Financial District": 9,
        "Haight-Ashbury": 18, "Russian Hill": 13
    },
    "Sunset District": {
        "Marina District": 21, "Mission District": 25, "Fisherman's Wharf": 29,
        "Presidio": 16, "Union Square": 30, "Financial District": 30,
        "Haight-Ashbury": 15, "Russian Hill": 24
    },
    "Financial District": {
        "Marina District": 15, "Mission District": 17, "Fisherman's Wharf": 10,
        "Presidio": 22, "Union Square": 9, "Sunset District": 30,
        "Haight-Ashbury": 19, "Russian Hill": 11
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Mission District": 11, "Fisherman's Wharf": 23,
        "Presidio": 15, "Union Square": 19, "Sunset District": 15,
        "Financial District": 21, "Russian Hill": 17
    },
    "Russian Hill": {
        "Marina District": 7, "Mission District": 16, "Fisherman's Wharf": 7,
        "Presidio": 14, "Union Square": 10, "Sunset District": 23,
        "Financial District": 11, "Haight-Ashbury": 17
    }
}
# Ensure zero travel time to same location entries
for a in travel:
    travel[a][a] = 0

# Friends and constraints
friends = [
    {
        "name": "Karen",
        "location": "Mission District",
        "start": minutes(14, 15),
        "end": minutes(22, 0),
        "min_dur": 30
    },
    {
        "name": "Richard",
        "location": "Fisherman's Wharf",
        "start": minutes(14, 30),
        "end": minutes(17, 30),
        "min_dur": 30
    },
    {
        "name": "Robert",
        "location": "Presidio",
        "start": minutes(21, 45),
        "end": minutes(22, 45),
        "min_dur": 60
    },
    {
        "name": "Joseph",
        "location": "Union Square",
        "start": minutes(11, 45),
        "end": minutes(14, 45),
        "min_dur": 120
    },
    {
        "name": "Helen",
        "location": "Sunset District",
        "start": minutes(14, 45),
        "end": minutes(20, 45),
        "min_dur": 105
    },
    {
        "name": "Elizabeth",
        "location": "Financial District",
        "start": minutes(10, 0),
        "end": minutes(12, 45),
        "min_dur": 75
    },
    {
        "name": "Kimberly",
        "location": "Haight-Ashbury",
        "start": minutes(14, 15),
        "end": minutes(17, 30),
        "min_dur": 105
    },
    {
        "name": "Ashley",
        "location": "Russian Hill",
        "start": minutes(11, 30),
        "end": minutes(21, 30),
        "min_dur": 45
    }
]

# Search (DFS) to maximize number of friends met.
# Tie-breaks: minimal total travel time, then minimal total waiting time, then earliest finish time, then lexicographic by names.
best_solution = {
    "count": -1,
    "travel": float('inf'),
    "wait": float('inf'),
    "finish": float('inf'),
    "names": (),
    "schedule": []
}

def dfs(current_loc, current_time, remaining_idx, schedule, total_travel, total_wait, met_names):
    global best_solution

    # Update best solution
    count = len(schedule)
    finish_time = schedule[-1]["end"] if schedule else current_time
    names_tuple = tuple(sorted(met_names))
    candidate = {
        "count": count,
        "travel": total_travel,
        "wait": total_wait,
        "finish": finish_time,
        "names": names_tuple,
        "schedule": list(schedule)
    }

    def better(a, b):
        # Return True if a is better than b
        if a["count"] != b["count"]:
            return a["count"] > b["count"]
        if a["travel"] != b["travel"]:
            return a["travel"] < b["travel"]
        if a["wait"] != b["wait"]:
            return a["wait"] < b["wait"]
        if a["finish"] != b["finish"]:
            return a["finish"] < b["finish"]
        return a["names"] < b["names"]

    if better(candidate, best_solution):
        best_solution = candidate

    # Order remaining by earliest end time, then earliest start, then name (heuristic to prune)
    ordered = sorted(remaining_idx, key=lambda i: (friends[i]["end"], friends[i]["start"], friends[i]["name"]))

    for i in ordered:
        f = friends[i]
        # Travel time
        t_travel = travel[current_loc][f["location"]]
        arrival = current_time + t_travel
        start_meet = max(arrival, f["start"])
        end_meet = start_meet + f["min_dur"]

        if end_meet <= f["end"]:
            # Feasible to meet
            wait = max(0, start_meet - arrival)
            entry = {
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start": start_meet,
                "end": end_meet
            }
            schedule.append(entry)
            new_remaining = [x for x in remaining_idx if x != i]
            met_names.add(f["name"])

            dfs(
                f["location"],
                end_meet,
                new_remaining,
                schedule,
                total_travel + t_travel,
                total_wait + wait,
                met_names
            )

            # backtrack
            met_names.remove(f["name"])
            schedule.pop()

# Run search
remaining_indices = list(range(len(friends)))
dfs(start_location, start_time, remaining_indices, [], 0, 0, set())

# Build output
itinerary = []
for e in best_solution["schedule"]:
    itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": str_time(e["start"]),
        "end_time": str_time(e["end"])
    })

output = {"itinerary": itinerary}

print(json.dumps(output, indent=2))