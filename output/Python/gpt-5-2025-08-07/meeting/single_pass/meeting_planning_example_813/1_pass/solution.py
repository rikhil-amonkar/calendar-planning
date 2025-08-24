import json
from copy import deepcopy

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes), directed
travel = {
    "Marina District": {
        "Embarcadero": 14, "Bayview": 27, "Union Square": 16, "Chinatown": 15,
        "Sunset District": 19, "Golden Gate Park": 18, "Financial District": 17,
        "Haight-Ashbury": 16, "Mission District": 20
    },
    "Embarcadero": {
        "Marina District": 12, "Bayview": 21, "Union Square": 10, "Chinatown": 7,
        "Sunset District": 30, "Golden Gate Park": 25, "Financial District": 5,
        "Haight-Ashbury": 21, "Mission District": 20
    },
    "Bayview": {
        "Marina District": 27, "Embarcadero": 19, "Union Square": 18, "Chinatown": 19,
        "Sunset District": 23, "Golden Gate Park": 22, "Financial District": 19,
        "Haight-Ashbury": 19, "Mission District": 13
    },
    "Union Square": {
        "Marina District": 18, "Embarcadero": 11, "Bayview": 15, "Chinatown": 7,
        "Sunset District": 27, "Golden Gate Park": 22, "Financial District": 9,
        "Haight-Ashbury": 18, "Mission District": 14
    },
    "Chinatown": {
        "Marina District": 12, "Embarcadero": 5, "Bayview": 20, "Union Square": 7,
        "Sunset District": 29, "Golden Gate Park": 23, "Financial District": 5,
        "Haight-Ashbury": 19, "Mission District": 17
    },
    "Sunset District": {
        "Marina District": 21, "Embarcadero": 30, "Bayview": 22, "Union Square": 30,
        "Chinatown": 30, "Golden Gate Park": 11, "Financial District": 30,
        "Haight-Ashbury": 15, "Mission District": 25
    },
    "Golden Gate Park": {
        "Marina District": 16, "Embarcadero": 25, "Bayview": 23, "Union Square": 22,
        "Chinatown": 23, "Sunset District": 10, "Financial District": 26,
        "Haight-Ashbury": 7, "Mission District": 17
    },
    "Financial District": {
        "Marina District": 15, "Embarcadero": 4, "Bayview": 19, "Union Square": 9,
        "Chinatown": 5, "Sunset District": 30, "Golden Gate Park": 23,
        "Haight-Ashbury": 19, "Mission District": 17
    },
    "Haight-Ashbury": {
        "Marina District": 17, "Embarcadero": 20, "Bayview": 18, "Union Square": 19,
        "Chinatown": 19, "Sunset District": 15, "Golden Gate Park": 7,
        "Financial District": 21, "Mission District": 11
    },
    "Mission District": {
        "Marina District": 19, "Embarcadero": 19, "Bayview": 14, "Union Square": 15,
        "Chinatown": 16, "Sunset District": 24, "Golden Gate Park": 17,
        "Financial District": 15, "Haight-Ashbury": 12
    }
}

# People constraints (times in minutes since 0:00)
people = [
    {"name": "Joshua", "location": "Embarcadero", "start": 9*60+45, "end": 18*60, "min": 105},
    {"name": "Jeffrey", "location": "Bayview", "start": 9*60+45, "end": 20*60+15, "min": 75},
    {"name": "Charles", "location": "Union Square", "start": 10*60+45, "end": 20*60+15, "min": 120},
    {"name": "Joseph", "location": "Chinatown", "start": 7*60, "end": 15*60+30, "min": 60},
    {"name": "Elizabeth", "location": "Sunset District", "start": 9*60, "end": 9*60+45, "min": 45},
    {"name": "Matthew", "location": "Golden Gate Park", "start": 11*60, "end": 19*60+30, "min": 45},
    {"name": "Carol", "location": "Financial District", "start": 10*60+45, "end": 11*60+15, "min": 15},
    {"name": "Paul", "location": "Haight-Ashbury", "start": 19*60+15, "end": 20*60+30, "min": 15},
    {"name": "Rebecca", "location": "Mission District", "start": 17*60, "end": 21*60+45, "min": 45},
]

start_location = "Marina District"
start_time = 9*60  # 9:00

best_result = {
    "count": 0,
    "end_time": start_time,
    "total_travel": 0,
    "itinerary": []
}

def explore(current_loc, current_time, visited, itinerary, total_travel):
    global best_result
    remaining = [p for p in people if p["name"] not in visited]
    # Upper bound pruning
    if len(itinerary) + len(remaining) < best_result["count"]:
        return

    # Gather feasible next meetings
    candidates = []
    for p in remaining:
        if current_loc not in travel or p["location"] not in travel[current_loc]:
            continue
        t_travel = travel[current_loc][p["location"]]
        arrival = current_time + t_travel
        earliest_start = max(arrival, p["start"])
        latest_start = p["end"] - p["min"]
        if earliest_start <= latest_start:
            start_t = earliest_start
            end_t = start_t + p["min"]
            candidates.append((p, start_t, end_t, t_travel))

    # Sort candidates to explore promising options first
    candidates.sort(key=lambda x: (x[2], x[1]))  # earliest finish, then earliest start

    extended = False
    for p, start_t, end_t, t_travel in candidates:
        extended = True
        visited_next = visited | {p["name"]}
        itinerary_next = itinerary + [{
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start_t),
            "end_time": fmt_time(end_t)
        }]
        explore(p["location"], end_t, visited_next, itinerary_next, total_travel + t_travel)

    if not extended:
        # Update best result based on criteria:
        # 1) Maximize number of meetings
        # 2) Among ties, earliest finish time
        # 3) Among ties, minimize total travel time
        count = len(itinerary)
        if (count > best_result["count"] or
           (count == best_result["count"] and (current_time < best_result["end_time"] or
            (current_time == best_result["end_time"] and total_travel < best_result["total_travel"])))):
            best_result = {
                "count": count,
                "end_time": current_time,
                "total_travel": total_travel,
                "itinerary": itinerary
            }

# Run search
explore(start_location, start_time, set(), [], 0)

# Output result as JSON
output = {
    "itinerary": best_result["itinerary"]
}
print(json.dumps(output, ensure_ascii=False))