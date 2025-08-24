# SOLUTION:
import json
from itertools import permutations

def time_to_minutes(tstr):
    # tstr like '9:00' or '13:30'
    parts = tstr.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (constraints and travel times)
start_location = "Pacific Heights"
arrival_time_str = "9:00"

travel_times = {
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Marina District"): 10,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Presidio"): 10,
}

people = {
    "Jason": {
        "location": "Presidio",
        "start": "10:00",
        "end": "16:15",
        "min_duration": 90
    },
    "Kenneth": {
        "location": "Marina District",
        "start": "15:30",
        "end": "16:45",
        "min_duration": 45
    }
}

# Convert times to minutes
arrival_time = time_to_minutes(arrival_time_str)
for p in people.values():
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

def get_travel(a, b):
    return travel_times[(a, b)]

def schedule_single(person_name):
    p = people[person_name]
    arrival = arrival_time + get_travel(start_location, p["location"])
    start_meet = max(arrival, p["start_min"])
    if start_meet + p["min_duration"] > p["end_min"]:
        return None
    # Maximize meeting time -> go until availability end
    end_meet = p["end_min"]
    itinerary = [{
        "action": "meet",
        "location": p["location"],
        "person": person_name,
        "start_time": minutes_to_time(start_meet),
        "end_time": minutes_to_time(end_meet)
    }]
    total_meeting = end_meet - start_meet
    waiting_time_total = max(0, start_meet - arrival)
    return {
        "itinerary": itinerary,
        "num_meetings": 1,
        "total_meeting": total_meeting,
        "waiting_time_total": waiting_time_total,
        "last_end_time": end_meet
    }

def schedule_pair(p1_name, p2_name):
    p1 = people[p1_name]
    p2 = people[p2_name]

    # First meeting
    arrival1 = arrival_time + get_travel(start_location, p1["location"])
    s1 = max(arrival1, p1["start_min"])
    if s1 + p1["min_duration"] > p1["end_min"]:
        return None

    best = None

    # Iterate possible end times for first meeting to optimize the second
    for e1 in range(s1 + p1["min_duration"], p1["end_min"] + 1):
        arrival2 = e1 + get_travel(p1["location"], p2["location"])
        s2 = max(arrival2, p2["start_min"])
        # Feasibility for second meeting
        if s2 + p2["min_duration"] > p2["end_min"]:
            continue
        # Maximize total meeting time -> extend second to its end
        e2 = p2["end_min"]
        total_meeting = (e1 - s1) + (e2 - s2)
        waiting1 = max(0, s1 - arrival1)
        waiting2 = max(0, s2 - arrival2)
        waiting_time_total = waiting1 + waiting2
        candidate = {
            "e1": e1,
            "s1": s1,
            "s2": s2,
            "e2": e2,
            "waiting_time_total": waiting_time_total,
            "total_meeting": total_meeting
        }
        # Select best by total meeting, then minimize waiting, then prefer longer first meeting
        if best is None:
            best = candidate
        else:
            if candidate["total_meeting"] > best["total_meeting"]:
                best = candidate
            elif candidate["total_meeting"] == best["total_meeting"]:
                if candidate["waiting_time_total"] < best["waiting_time_total"]:
                    best = candidate
                elif candidate["waiting_time_total"] == best["waiting_time_total"]:
                    if candidate["e1"] > best["e1"]:
                        best = candidate

    if best is None:
        return None

    e1 = best["e1"]
    s1 = best["s1"]
    s2 = best["s2"]
    e2 = best["e2"]

    itinerary = [
        {
            "action": "meet",
            "location": p1["location"],
            "person": p1_name,
            "start_time": minutes_to_time(s1),
            "end_time": minutes_to_time(e1)
        },
        {
            "action": "meet",
            "location": p2["location"],
            "person": p2_name,
            "start_time": minutes_to_time(s2),
            "end_time": minutes_to_time(e2)
        }
    ]
    last_end_time = e2
    waiting1 = max(0, s1 - arrival1)
    arrival2 = e1 + get_travel(p1["location"], p2["location"])
    waiting2 = max(0, s2 - arrival2)

    return {
        "itinerary": itinerary,
        "num_meetings": 2,
        "total_meeting": (e1 - s1) + (e2 - s2),
        "waiting_time_total": waiting1 + waiting2,
        "last_end_time": last_end_time
    }

def better(a, b):
    if b is None:
        return True
    if a["num_meetings"] != b["num_meetings"]:
        return a["num_meetings"] > b["num_meetings"]
    if a["total_meeting"] != b["total_meeting"]:
        return a["total_meeting"] > b["total_meeting"]
    if a["waiting_time_total"] != b["waiting_time_total"]:
        return a["waiting_time_total"] < b["waiting_time_total"]
    return a["last_end_time"] < b["last_end_time"]

# Generate and evaluate schedules
friends = list(people.keys())
candidate_results = []

# Single-person schedules
for name in friends:
    res = schedule_single(name)
    if res:
        candidate_results.append(res)

# Pair schedules (both orders)
for order in permutations(friends, 2):
    res = schedule_pair(order[0], order[1])
    if res:
        candidate_results.append(res)

# Choose best result
best_result = None
for res in candidate_results:
    if better(res, best_result):
        best_result = res

# If nothing feasible (shouldn't happen here), return empty itinerary
output = {"itinerary": best_result["itinerary"] if best_result else []}

print(json.dumps(output, ensure_ascii=False))