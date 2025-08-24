import json
from functools import lru_cache

# Helper functions
def to_minutes(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Pacific Heights"
arrival_time = to_minutes(9, 0)

# Travel times (minutes)
T = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15,
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17,
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7,
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13,
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20,
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14,
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25,
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10,
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17,
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15,
    },
}

# People constraints
people = [
    {
        "name": "Helen",
        "location": "Golden Gate Park",
        "start": to_minutes(9, 30),
        "end": to_minutes(12, 15),
        "min_duration": 45,
    },
    {
        "name": "Steven",
        "location": "The Castro",
        "start": to_minutes(20, 15),
        "end": to_minutes(22, 0),
        "min_duration": 105,
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "start": to_minutes(8, 30),
        "end": to_minutes(12, 0),
        "min_duration": 30,
    },
    {
        "name": "Matthew",
        "location": "Marina District",
        "start": to_minutes(9, 15),
        "end": to_minutes(14, 15),
        "min_duration": 45,
    },
    {
        "name": "Joseph",
        "location": "Union Square",
        "start": to_minutes(14, 15),
        "end": to_minutes(18, 45),
        "min_duration": 120,
    },
    {
        "name": "Ronald",
        "location": "Sunset District",
        "start": to_minutes(16, 0),
        "end": to_minutes(20, 45),
        "min_duration": 60,
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "start": to_minutes(18, 30),
        "end": to_minutes(21, 15),
        "min_duration": 120,
    },
    {
        "name": "Rebecca",
        "location": "Financial District",
        "start": to_minutes(14, 45),
        "end": to_minutes(16, 15),
        "min_duration": 30,
    },
    {
        "name": "Elizabeth",
        "location": "Mission District",
        "start": to_minutes(18, 30),
        "end": to_minutes(21, 0),
        "min_duration": 120,
    },
]

# Sort people by end time to guide search (earliest deadlines first)
people_indices = list(range(len(people)))
people_order = sorted(people_indices, key=lambda i: (people[i]["end"], people[i]["start"]))

# Memoization: map (loc, time, visited_mask) -> best achievable remaining count from here
# We'll keep as "max meetings achievable from this state" to prune.
memo = {}

best_result = {
    "count": 0,
    "end_time": float('inf'),
    "travel_time": float('inf'),
    "schedule": [],
}

# Precompute pairwise travel times default
def travel_time(a, b):
    if a == b:
        return 0
    return T[a][b]

def better_schedule(a, b):
    # Compare by count, then earlier finish, then less travel time, then lexicographically by names for determinism
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["end_time"] != b["end_time"]:
        return a["end_time"] < b["end_time"]
    if a["travel_time"] != b["travel_time"]:
        return a["travel_time"] < b["travel_time"]
    # Deterministic fallback
    names_a = [entry["person"] for entry in a["schedule"]]
    names_b = [entry["person"] for entry in b["schedule"]]
    return names_a < names_b

def dfs(curr_loc, curr_time, visited_mask, schedule, travel_accum):
    global best_result
    # Update best with current schedule
    curr_count = bin(visited_mask).count("1")
    current_end_time = curr_time if schedule else arrival_time
    candidate = {
        "count": curr_count,
        "end_time": current_end_time,
        "travel_time": travel_accum,
        "schedule": list(schedule),
    }
    if better_schedule(candidate, best_result):
        best_result = candidate

    # Upper bound prune: if even meeting all remaining cannot beat current best, prune
    remaining = len(people) - curr_count
    if curr_count + remaining < best_result["count"]:
        return

    # Memo prune
    key = (curr_loc, curr_time, visited_mask)
    if key in memo:
        prev_best_remaining = memo[key]
        # If from this state we cannot add more than stored bound, prune
        # Store the max achievable from this state discovered so far
        if prev_best_remaining >= curr_count:
            # If we've been here with equal or more meetings already, prune
            return
    memo[key] = curr_count

    # Generate candidate next meetings (unvisited)
    candidates = []
    for i in people_order:
        if (visited_mask >> i) & 1:
            continue
        p = people[i]
        t_travel = travel_time(curr_loc, p["location"])
        arrival = curr_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet <= p["end"]:
            # feasible
            candidates.append((i, start_meet, end_meet, t_travel))

    # Order candidates by earliest end_meet to encourage tighter schedules
    candidates.sort(key=lambda x: (x[2], people[x[0]]["end"]))

    for i, start_meet, end_meet, t_travel in candidates:
        p = people[i]
        schedule.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt(start_meet),
            "end_time": fmt(end_meet),
        })
        dfs(
            p["location"],
            end_meet,
            visited_mask | (1 << i),
            schedule,
            travel_accum + t_travel
        )
        schedule.pop()

def main():
    # Start the search
    dfs(start_location, arrival_time, 0, [], 0)

    # Output result JSON
    print(json.dumps({"itinerary": best_result["schedule"]}, ensure_ascii=False))

if __name__ == "__main__":
    main()