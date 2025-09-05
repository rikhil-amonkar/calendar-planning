# SOLUTION:
import json
from itertools import permutations

def parse_time(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Alamo Square"
start_time_str = "9:00"

# Travel times (directed, minutes)
travel_data = [
    ("Alamo Square", "Russian Hill", 13),
    ("Alamo Square", "Presidio", 18),
    ("Alamo Square", "Chinatown", 16),
    ("Alamo Square", "Sunset District", 16),
    ("Alamo Square", "The Castro", 8),
    ("Alamo Square", "Embarcadero", 17),
    ("Alamo Square", "Golden Gate Park", 9),

    ("Russian Hill", "Alamo Square", 15),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Chinatown", 9),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "The Castro", 21),
    ("Russian Hill", "Embarcadero", 8),
    ("Russian Hill", "Golden Gate Park", 21),

    ("Presidio", "Alamo Square", 18),
    ("Presidio", "Russian Hill", 14),
    ("Presidio", "Chinatown", 21),
    ("Presidio", "Sunset District", 15),
    ("Presidio", "The Castro", 21),
    ("Presidio", "Embarcadero", 20),
    ("Presidio", "Golden Gate Park", 12),

    ("Chinatown", "Alamo Square", 17),
    ("Chinatown", "Russian Hill", 7),
    ("Chinatown", "Presidio", 19),
    ("Chinatown", "Sunset District", 29),
    ("Chinatown", "The Castro", 22),
    ("Chinatown", "Embarcadero", 5),
    ("Chinatown", "Golden Gate Park", 23),

    ("Sunset District", "Alamo Square", 17),
    ("Sunset District", "Russian Hill", 24),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Chinatown", 30),
    ("Sunset District", "The Castro", 17),
    ("Sunset District", "Embarcadero", 31),
    ("Sunset District", "Golden Gate Park", 11),

    ("The Castro", "Alamo Square", 8),
    ("The Castro", "Russian Hill", 18),
    ("The Castro", "Presidio", 20),
    ("The Castro", "Chinatown", 20),
    ("The Castro", "Sunset District", 17),
    ("The Castro", "Embarcadero", 22),
    ("The Castro", "Golden Gate Park", 11),

    ("Embarcadero", "Alamo Square", 19),
    ("Embarcadero", "Russian Hill", 8),
    ("Embarcadero", "Presidio", 20),
    ("Embarcadero", "Chinatown", 7),
    ("Embarcadero", "Sunset District", 30),
    ("Embarcadero", "The Castro", 25),
    ("Embarcadero", "Golden Gate Park", 25),

    ("Golden Gate Park", "Alamo Square", 10),
    ("Golden Gate Park", "Russian Hill", 19),
    ("Golden Gate Park", "Presidio", 11),
    ("Golden Gate Park", "Chinatown", 23),
    ("Golden Gate Park", "Sunset District", 10),
    ("Golden Gate Park", "The Castro", 13),
    ("Golden Gate Park", "Embarcadero", 25),
]

# Build travel lookup
travel = {}
for a, b, t in travel_data:
    travel.setdefault(a, {})[b] = t

# People constraints
people = [
    {
        "name": "Emily",
        "location": "Russian Hill",
        "start": parse_time("12:15"),
        "end": parse_time("14:15"),
        "min_duration": 105
    },
    {
        "name": "Mark",
        "location": "Presidio",
        "start": parse_time("14:45"),
        "end": parse_time("19:30"),
        "min_duration": 60
    },
    {
        "name": "Deborah",
        "location": "Chinatown",
        "start": parse_time("7:30"),
        "end": parse_time("15:30"),
        "min_duration": 45
    },
    {
        "name": "Margaret",
        "location": "Sunset District",
        "start": parse_time("21:30"),
        "end": parse_time("22:30"),
        "min_duration": 60
    },
    {
        "name": "George",
        "location": "The Castro",
        "start": parse_time("7:30"),
        "end": parse_time("14:15"),
        "min_duration": 60
    },
    {
        "name": "Andrew",
        "location": "Embarcadero",
        "start": parse_time("20:15"),
        "end": parse_time("22:00"),
        "min_duration": 75
    },
    {
        "name": "Steven",
        "location": "Golden Gate Park",
        "start": parse_time("11:15"),
        "end": parse_time("21:15"),
        "min_duration": 105
    }
]

# Index people by name for easy reference
people_by_name = {p["name"]: p for p in people}

start_time = parse_time(start_time_str)

best = {
    "count": 0,
    "meeting_minutes": 0,
    "travel_minutes": float('inf'),
    "end_time": float('inf'),
    "itinerary": []
}

def compare_and_update(candidate):
    # Objective: maximize count, then total meeting minutes,
    # then minimize travel minutes, then earlier end time.
    global best
    better = False
    if candidate["count"] > best["count"]:
        better = True
    elif candidate["count"] == best["count"]:
        if candidate["meeting_minutes"] > best["meeting_minutes"]:
            better = True
        elif candidate["meeting_minutes"] == best["meeting_minutes"]:
            if candidate["travel_minutes"] < best["travel_minutes"]:
                better = True
            elif candidate["travel_minutes"] == best["travel_minutes"]:
                if candidate["end_time"] < best["end_time"]:
                    better = True
    if better:
        best = candidate

def dfs(current_loc, current_time, remaining_names, itinerary, meeting_minutes_acc, travel_minutes_acc):
    # Update best with current partial solution (could be terminal)
    compare_and_update({
        "count": len(itinerary),
        "meeting_minutes": meeting_minutes_acc,
        "travel_minutes": travel_minutes_acc,
        "end_time": current_time,
        "itinerary": itinerary
    })

    if not remaining_names:
        return

    # Simple pruning: compute theoretical max additional people possible (ignoring travel)
    potential_max = len(itinerary) + len(remaining_names)
    if potential_max < best["count"]:
        return

    # Try each next person
    for name in sorted(remaining_names):
        p = people_by_name[name]
        if current_loc not in travel or p["location"] not in travel[current_loc]:
            continue
        t_travel = travel[current_loc][p["location"]]
        arrival = current_time + t_travel
        earliest_start = max(arrival, p["start"])
        latest_start = p["end"] - p["min_duration"]
        if earliest_start > latest_start:
            continue  # cannot meet minimum

        min_end = earliest_start + p["min_duration"]

        # Build candidate end times
        candidate_end_times = set()
        # Always consider minimal meeting and full window
        candidate_end_times.add(min_end)
        candidate_end_times.add(p["end"])

        # Consider aligning with each other person's start/latest-start
        others = [people_by_name[o] for o in remaining_names if o != name]
        for q in others:
            if p["location"] not in travel or q["location"] not in travel[p["location"]]:
                continue
            t_pq = travel[p["location"]][q["location"]]
            # Align to q.start
            cand1 = q["start"] - t_pq
            if min_end <= cand1 <= p["end"]:
                candidate_end_times.add(cand1)
            # Align to q.latest start
            q_latest_start = q["end"] - q["min_duration"]
            cand2 = q_latest_start - t_pq
            if min_end <= cand2 <= p["end"]:
                candidate_end_times.add(cand2)

        # Evaluate each candidate end time
        for t_end in sorted(candidate_end_times):
            duration = t_end - earliest_start
            if duration < p["min_duration"]:
                continue
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": fmt_time(earliest_start),
                "end_time": fmt_time(t_end)
            }]
            new_remaining = tuple(x for x in remaining_names if x != name)
            dfs(
                p["location"],
                t_end,
                new_remaining,
                new_itinerary,
                meeting_minutes_acc + duration,
                travel_minutes_acc + t_travel
            )

# Run DFS search
all_names = tuple(p["name"] for p in people)
dfs(start_location, start_time, all_names, [], 0, 0)

# Prepare output
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))