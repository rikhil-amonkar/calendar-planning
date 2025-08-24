import json
from functools import lru_cache

# Helper functions for time handling
def to_minutes(t):
    # t like '9:00' or '13:30'
    h, m = map(int, t.split(':'))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

# Build travel time dictionary (asymmetric)
locations = [
    "Union Square", "Presidio", "Alamo Square", "Marina District",
    "Financial District", "Nob Hill", "Sunset District", "Chinatown",
    "Russian Hill", "North Beach", "Haight-Ashbury"
]

travel = {loc: {} for loc in locations}

def set_t(a, b, minutes):
    travel[a][b] = minutes

# Given travel times
set_t("Union Square", "Presidio", 24)
set_t("Union Square", "Alamo Square", 15)
set_t("Union Square", "Marina District", 18)
set_t("Union Square", "Financial District", 9)
set_t("Union Square", "Nob Hill", 9)
set_t("Union Square", "Sunset District", 27)
set_t("Union Square", "Chinatown", 7)
set_t("Union Square", "Russian Hill", 13)
set_t("Union Square", "North Beach", 10)
set_t("Union Square", "Haight-Ashbury", 18)

set_t("Presidio", "Union Square", 22)
set_t("Presidio", "Alamo Square", 19)
set_t("Presidio", "Marina District", 11)
set_t("Presidio", "Financial District", 23)
set_t("Presidio", "Nob Hill", 18)
set_t("Presidio", "Sunset District", 15)
set_t("Presidio", "Chinatown", 21)
set_t("Presidio", "Russian Hill", 14)
set_t("Presidio", "North Beach", 18)
set_t("Presidio", "Haight-Ashbury", 15)

set_t("Alamo Square", "Union Square", 14)
set_t("Alamo Square", "Presidio", 17)
set_t("Alamo Square", "Marina District", 15)
set_t("Alamo Square", "Financial District", 17)
set_t("Alamo Square", "Nob Hill", 11)
set_t("Alamo Square", "Sunset District", 16)
set_t("Alamo Square", "Chinatown", 15)
set_t("Alamo Square", "Russian Hill", 13)
set_t("Alamo Square", "North Beach", 15)
set_t("Alamo Square", "Haight-Ashbury", 5)

set_t("Marina District", "Union Square", 16)
set_t("Marina District", "Presidio", 10)
set_t("Marina District", "Alamo Square", 15)
set_t("Marina District", "Financial District", 17)
set_t("Marina District", "Nob Hill", 12)
set_t("Marina District", "Sunset District", 19)
set_t("Marina District", "Chinatown", 15)
set_t("Marina District", "Russian Hill", 8)
set_t("Marina District", "North Beach", 11)
set_t("Marina District", "Haight-Ashbury", 16)

set_t("Financial District", "Union Square", 9)
set_t("Financial District", "Presidio", 22)
set_t("Financial District", "Alamo Square", 17)
set_t("Financial District", "Marina District", 15)
set_t("Financial District", "Nob Hill", 8)
set_t("Financial District", "Sunset District", 30)
set_t("Financial District", "Chinatown", 5)
set_t("Financial District", "Russian Hill", 11)
set_t("Financial District", "North Beach", 7)
set_t("Financial District", "Haight-Ashbury", 19)

set_t("Nob Hill", "Union Square", 7)
set_t("Nob Hill", "Presidio", 17)
set_t("Nob Hill", "Alamo Square", 11)
set_t("Nob Hill", "Marina District", 11)
set_t("Nob Hill", "Financial District", 9)
set_t("Nob Hill", "Sunset District", 24)
set_t("Nob Hill", "Chinatown", 6)
set_t("Nob Hill", "Russian Hill", 5)
set_t("Nob Hill", "North Beach", 8)
set_t("Nob Hill", "Haight-Ashbury", 13)

set_t("Sunset District", "Union Square", 30)
set_t("Sunset District", "Presidio", 16)
set_t("Sunset District", "Alamo Square", 17)
set_t("Sunset District", "Marina District", 21)
set_t("Sunset District", "Financial District", 30)
set_t("Sunset District", "Nob Hill", 27)
set_t("Sunset District", "Chinatown", 30)
set_t("Sunset District", "Russian Hill", 24)
set_t("Sunset District", "North Beach", 28)
set_t("Sunset District", "Haight-Ashbury", 15)

set_t("Chinatown", "Union Square", 7)
set_t("Chinatown", "Presidio", 19)
set_t("Chinatown", "Alamo Square", 17)
set_t("Chinatown", "Marina District", 12)
set_t("Chinatown", "Financial District", 5)
set_t("Chinatown", "Nob Hill", 9)
set_t("Chinatown", "Sunset District", 29)
set_t("Chinatown", "Russian Hill", 7)
set_t("Chinatown", "North Beach", 3)
set_t("Chinatown", "Haight-Ashbury", 19)

set_t("Russian Hill", "Union Square", 10)
set_t("Russian Hill", "Presidio", 14)
set_t("Russian Hill", "Alamo Square", 15)
set_t("Russian Hill", "Marina District", 7)
set_t("Russian Hill", "Financial District", 11)
set_t("Russian Hill", "Nob Hill", 5)
set_t("Russian Hill", "Sunset District", 23)
set_t("Russian Hill", "Chinatown", 9)
set_t("Russian Hill", "North Beach", 5)
set_t("Russian Hill", "Haight-Ashbury", 17)

set_t("North Beach", "Union Square", 7)
set_t("North Beach", "Presidio", 17)
set_t("North Beach", "Alamo Square", 16)
set_t("North Beach", "Marina District", 9)
set_t("North Beach", "Financial District", 8)
set_t("North Beach", "Nob Hill", 7)
set_t("North Beach", "Sunset District", 27)
set_t("North Beach", "Chinatown", 6)
set_t("North Beach", "Russian Hill", 4)
set_t("North Beach", "Haight-Ashbury", 18)

set_t("Haight-Ashbury", "Union Square", 19)
set_t("Haight-Ashbury", "Presidio", 15)
set_t("Haight-Ashbury", "Alamo Square", 5)
set_t("Haight-Ashbury", "Marina District", 17)
set_t("Haight-Ashbury", "Financial District", 21)
set_t("Haight-Ashbury", "Nob Hill", 15)
set_t("Haight-Ashbury", "Sunset District", 15)
set_t("Haight-Ashbury", "Chinatown", 19)
set_t("Haight-Ashbury", "Russian Hill", 17)
set_t("Haight-Ashbury", "North Beach", 19)

# Add zero self-travel for completeness
for loc in locations:
    travel[loc][loc] = 0

# Participant constraints
participants = [
    {"name": "Kimberly", "location": "Presidio", "start": to_minutes("15:30"), "end": to_minutes("16:00"), "min_dur": 15},
    {"name": "Elizabeth", "location": "Alamo Square", "start": to_minutes("19:15"), "end": to_minutes("20:15"), "min_dur": 15},
    {"name": "Joshua", "location": "Marina District", "start": to_minutes("10:30"), "end": to_minutes("14:15"), "min_dur": 45},
    {"name": "Sandra", "location": "Financial District", "start": to_minutes("19:30"), "end": to_minutes("20:15"), "min_dur": 45},
    {"name": "Kenneth", "location": "Nob Hill", "start": to_minutes("12:45"), "end": to_minutes("21:45"), "min_dur": 30},
    {"name": "Betty", "location": "Sunset District", "start": to_minutes("14:00"), "end": to_minutes("19:00"), "min_dur": 60},
    {"name": "Deborah", "location": "Chinatown", "start": to_minutes("17:15"), "end": to_minutes("20:30"), "min_dur": 15},
    {"name": "Barbara", "location": "Russian Hill", "start": to_minutes("17:30"), "end": to_minutes("21:15"), "min_dur": 120},
    {"name": "Steven", "location": "North Beach", "start": to_minutes("17:45"), "end": to_minutes("20:45"), "min_dur": 90},
    {"name": "Daniel", "location": "Haight-Ashbury", "start": to_minutes("18:30"), "end": to_minutes("18:45"), "min_dur": 15},
]

# Sort participants by window end to improve pruning
participants_sorted = sorted(participants, key=lambda p: (p["end"], p["start"]))

start_location = "Union Square"
start_time = to_minutes("9:00")

# DFS with branch and bound
best_solution = {
    "count": 0,
    "total_minutes": 0,
    "end_time": start_time,
    "itinerary": []
}

# Precompute a map for quick index
name_to_idx = {p["name"]: i for i, p in enumerate(participants_sorted)}

@lru_cache(maxsize=None)
def optimistic_count(current_time, remaining_mask):
    # Upper bound on how many meetings can still be met (ignoring travel)
    count = 0
    for i, p in enumerate(participants_sorted):
        if (remaining_mask >> i) & 1:
            # Can we still start and finish sometime after current_time ignoring travel?
            latest_start = p["end"] - p["min_dur"]
            if latest_start >= current_time:
                count += 1
    return count

def dfs(current_loc, current_time, remaining_mask, current_itinerary, current_total_minutes):
    global best_solution

    current_count = len(current_itinerary)

    # Prune if optimistic bound cannot beat best
    opt_remain = optimistic_count(current_time, remaining_mask)
    if current_count + opt_remain < best_solution["count"]:
        return

    # Update best solution
    def better(count, total, endt, best):
        if count > best["count"]:
            return True
        if count == best["count"] and total > best["total_minutes"]:
            return True
        if count == best["count"] and total == best["total_minutes"] and endt < best["end_time"]:
            return True
        return False

    if better(current_count, current_total_minutes, current_time, best_solution):
        best_solution = {
            "count": current_count,
            "total_minutes": current_total_minutes,
            "end_time": current_time,
            "itinerary": list(current_itinerary)
        }

    # Order the next candidates by earliest feasible finish time heuristic
    candidates = []
    for i, p in enumerate(participants_sorted):
        if (remaining_mask >> i) & 1:
            # travel time
            t_travel = travel[current_loc][p["location"]]
            arrive = current_time + t_travel
            start_meet = max(arrive, p["start"])
            end_meet = start_meet + p["min_dur"]
            if end_meet <= p["end"]:
                candidates.append((end_meet, start_meet, i, p))
    # Sort by earlier end_meet then earlier start
    candidates.sort(key=lambda x: (x[0], x[1]))

    for end_meet, start_meet, i, p in candidates:
        # Schedule this meeting
        entry = {
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_minutes(start_meet),
            "end_time": fmt_minutes(end_meet)
        }
        current_itinerary.append(entry)
        dfs(p["location"], end_meet, remaining_mask ^ (1 << i), current_itinerary, current_total_minutes + p["min_dur"])
        current_itinerary.pop()

# Initial remaining mask: all participants available
initial_mask = 0
for i in range(len(participants_sorted)):
    initial_mask |= (1 << i)

dfs(start_location, start_time, initial_mask, [], 0)

# Prepare JSON output
output = {"itinerary": best_solution["itinerary"]}
print(json.dumps(output, ensure_ascii=False))