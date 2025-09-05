# SOLUTION:
import json
from functools import lru_cache

def parse_time(t):
    # t like '13:15' or '9:00'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) between locations (directed)
dist = {
    "Sunset District": {
        "Presidio": 16, "Nob Hill": 27, "Pacific Heights": 21, "Mission District": 25,
        "Marina District": 21, "North Beach": 28, "Russian Hill": 24, "Richmond District": 12,
        "Embarcadero": 30, "Alamo Square": 17
    },
    "Presidio": {
        "Sunset District": 15, "Nob Hill": 18, "Pacific Heights": 11, "Mission District": 26,
        "Marina District": 11, "North Beach": 18, "Russian Hill": 14, "Richmond District": 7,
        "Embarcadero": 20, "Alamo Square": 19
    },
    "Nob Hill": {
        "Sunset District": 24, "Presidio": 17, "Pacific Heights": 8, "Mission District": 13,
        "Marina District": 11, "North Beach": 8, "Russian Hill": 5, "Richmond District": 14,
        "Embarcadero": 9, "Alamo Square": 11
    },
    "Pacific Heights": {
        "Sunset District": 21, "Presidio": 11, "Nob Hill": 8, "Mission District": 15,
        "Marina District": 6, "North Beach": 9, "Russian Hill": 7, "Richmond District": 12,
        "Embarcadero": 10, "Alamo Square": 10
    },
    "Mission District": {
        "Sunset District": 24, "Presidio": 25, "Nob Hill": 12, "Pacific Heights": 16,
        "Marina District": 19, "North Beach": 17, "Russian Hill": 15, "Richmond District": 20,
        "Embarcadero": 19, "Alamo Square": 11
    },
    "Marina District": {
        "Sunset District": 19, "Presidio": 10, "Nob Hill": 12, "Pacific Heights": 7,
        "Mission District": 20, "North Beach": 11, "Russian Hill": 8, "Richmond District": 11,
        "Embarcadero": 14, "Alamo Square": 15
    },
    "North Beach": {
        "Sunset District": 27, "Presidio": 17, "Nob Hill": 7, "Pacific Heights": 8,
        "Mission District": 18, "Marina District": 9, "Russian Hill": 4, "Richmond District": 18,
        "Embarcadero": 6, "Alamo Square": 16
    },
    "Russian Hill": {
        "Sunset District": 23, "Presidio": 14, "Nob Hill": 5, "Pacific Heights": 7,
        "Mission District": 16, "Marina District": 7, "North Beach": 5, "Richmond District": 14,
        "Embarcadero": 8, "Alamo Square": 15
    },
    "Richmond District": {
        "Sunset District": 11, "Presidio": 7, "Nob Hill": 17, "Pacific Heights": 10,
        "Mission District": 20, "Marina District": 9, "North Beach": 17, "Russian Hill": 13,
        "Embarcadero": 19, "Alamo Square": 13
    },
    "Embarcadero": {
        "Sunset District": 30, "Presidio": 20, "Nob Hill": 10, "Pacific Heights": 11,
        "Mission District": 20, "Marina District": 12, "North Beach": 5, "Russian Hill": 8,
        "Richmond District": 21, "Alamo Square": 19
    },
    "Alamo Square": {
        "Sunset District": 16, "Presidio": 17, "Nob Hill": 11, "Pacific Heights": 10,
        "Mission District": 10, "Marina District": 15, "North Beach": 15, "Russian Hill": 13,
        "Richmond District": 11, "Embarcadero": 16
    }
}

# Participants and constraints
people = [
    {"name": "Charles", "location": "Presidio", "start": parse_time("13:15"), "end": parse_time("15:00"), "min": 105},
    {"name": "Robert", "location": "Nob Hill", "start": parse_time("13:15"), "end": parse_time("17:30"), "min": 90},
    {"name": "Nancy", "location": "Pacific Heights", "start": parse_time("14:45"), "end": parse_time("22:00"), "min": 105},
    {"name": "Brian", "location": "Mission District", "start": parse_time("15:30"), "end": parse_time("22:00"), "min": 60},
    {"name": "Kimberly", "location": "Marina District", "start": parse_time("17:00"), "end": parse_time("19:45"), "min": 75},
    {"name": "David", "location": "North Beach", "start": parse_time("14:45"), "end": parse_time("16:30"), "min": 75},
    {"name": "William", "location": "Russian Hill", "start": parse_time("12:30"), "end": parse_time("19:15"), "min": 120},
    {"name": "Jeffrey", "location": "Richmond District", "start": parse_time("12:00"), "end": parse_time("19:15"), "min": 45},
    {"name": "Karen", "location": "Embarcadero", "start": parse_time("14:15"), "end": parse_time("20:45"), "min": 60},
    {"name": "Joshua", "location": "Alamo Square", "start": parse_time("18:45"), "end": parse_time("22:00"), "min": 60},
]

# Sort people by earliest start to guide search heuristics
people_sorted = sorted(people, key=lambda x: (x["start"], x["end"]))

start_location = "Sunset District"
start_time = parse_time("9:00")

# Build quick lookup index
name_to_person = {p["name"]: p for p in people_sorted}
all_names = tuple(p["name"] for p in people_sorted)

# For branch-and-bound: precompute an optimistic feasibility check for each person from any time (ignoring travel)
# Here we only check if end - min >= t for some t, but we'll still keep it simple.
def optimistic_remaining_count(current_time, remaining_names):
    # Count how many have enough time left beyond current_time ignoring travel and waiting
    c = 0
    for n in remaining_names:
        p = name_to_person[n]
        latest_start = p["end"] - p["min"]
        if latest_start >= current_time:
            c += 1
    return c

best_solution = {
    "count": 0,
    "total_meeting_minutes": 0,
    "end_time": start_time,
    "total_travel_minutes": 0,
    "itinerary": []
}

def better(sol_a, sol_b):
    # Return True if sol_a is better than sol_b
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    if sol_a["total_meeting_minutes"] != sol_b["total_meeting_minutes"]:
        return sol_a["total_meeting_minutes"] > sol_b["total_meeting_minutes"]
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    if sol_a["total_travel_minutes"] != sol_b["total_travel_minutes"]:
        return sol_a["total_travel_minutes"] < sol_b["total_travel_minutes"]
    # Final tie-breaker: lexicographically by itinerary string
    return json.dumps(sol_a["itinerary"]) < json.dumps(sol_b["itinerary"])

@lru_cache(maxsize=None)
def search(curr_loc, curr_time, remaining_names_tuple):
    remaining_names = list(remaining_names_tuple)

    # Baseline: no more meetings
    best_local = {
        "count": 0,
        "total_meeting_minutes": 0,
        "end_time": curr_time,
        "total_travel_minutes": 0,
        "itinerary": []
    }

    # Branch and bound: if even optimistically we can't beat global best, prune in the caller by returning baseline
    # Note: Cannot access global best here reliably for pruning in cache scope; we keep local optimal growth.

    # Try all possible next meetings
    for n in remaining_names:
        p = name_to_person[n]
        # Travel time from curr_loc to p["location"]
        if curr_loc not in dist or p["location"] not in dist[curr_loc]:
            continue  # no path known
        travel = dist[curr_loc][p["location"]]
        arrival = curr_time + travel
        start = max(arrival, p["start"])
        end = start + p["min"]
        if end <= p["end"]:
            # Feasible
            next_remaining = tuple(x for x in remaining_names if x != n)
            sub = search(p["location"], end, next_remaining)
            # Compose solution including this meeting
            candidate = {
                "count": sub["count"] + 1,
                "total_meeting_minutes": sub["total_meeting_minutes"] + p["min"],
                "end_time": sub["end_time"],
                "total_travel_minutes": sub["total_travel_minutes"] + travel,
                "itinerary": [{
                    "action": "meet",
                    "location": p["location"],
                    "person": p["name"],
                    "start_time": fmt_time(start),
                    "end_time": fmt_time(end)
                }] + sub["itinerary"]
            }
            if better(candidate, best_local):
                best_local = candidate

    return best_local

# Kick off search from start, considering all people
result = search(start_location, start_time, all_names)

# The search returns the best itinerary from "now" to the end, but it does not include initial travel/wait explicitly.
# That's acceptable per problem statement: itinerary only contains meeting actions.

output = {
    "itinerary": result["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))