import json

# Utilities for time conversion
def to_minutes(t):
    # t is in 'H:MM' or 'HH:MM'
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (meeting constraints and travel times)
start_location = "Nob Hill"
start_time_str = "9:00"

travel_minutes = {
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Mission District"): 13,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Mission District"): 15,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Pacific Heights"): 16,
}

people = {
    "Thomas": {
        "location": "Pacific Heights",
        "window_start": "15:30",
        "window_end": "19:15",
        "min_minutes": 75,
    },
    "Kenneth": {
        "location": "Mission District",
        "window_start": "12:00",
        "window_end": "15:45",
        "min_minutes": 45,
    },
}

# Convert inputs to minutes
start_time = to_minutes(start_time_str)
for p in people.values():
    p["ws"] = to_minutes(p["window_start"])
    p["we"] = to_minutes(p["window_end"])

def window_length(p):
    return p["we"] - p["ws"]

def travel(a, b):
    if a == b:
        return 0
    return travel_minutes[(a, b)]

def feasible_single(person_name):
    p = people[person_name]
    loc = p["location"]
    start_meet = max(p["ws"], start_time + travel(start_location, loc))
    end_meet = p["we"]
    if end_meet - start_meet >= p["min_minutes"]:
        return {
            "itinerary": [
                {
                    "action": "meet",
                    "location": loc,
                    "person": person_name,
                    "start_time_min": start_meet,
                    "end_time_min": end_meet,
                }
            ],
            "friends_met": 1,
            "total_meeting_minutes": end_meet - start_meet,
            "finish_time": end_meet,
        }
    else:
        return None

def feasible_both(order):
    # order is list like ["Kenneth", "Thomas"]
    p1 = people[order[0]]
    p2 = people[order[1]]
    loc1 = p1["location"]
    loc2 = p2["location"]
    # Earliest start of first meeting
    start1 = max(p1["ws"], start_time + travel(start_location, loc1))
    if p1["we"] - start1 < p1["min_minutes"]:
        return None
    # Check second person's window length supports min duration at all
    if (p2["we"] - p2["ws"]) < p2["min_minutes"]:
        return None

    t12 = travel(loc1, loc2)

    # Strategy A: arrive at p2 right at their window start (maximize p2 time)
    e1_candidate1 = min(p1["we"], p2["ws"] - t12)
    schedule = None

    def build_schedule(e1):
        start2 = max(p2["ws"], e1 + t12)
        end2 = p2["we"]
        d2 = end2 - start2
        d1 = e1 - start1
        if d1 >= p1["min_minutes"] and d2 >= p2["min_minutes"] and e1 >= start1:
            return {
                "itinerary": [
                    {
                        "action": "meet",
                        "location": loc1,
                        "person": order[0],
                        "start_time_min": start1,
                        "end_time_min": e1,
                    },
                    {
                        "action": "meet",
                        "location": loc2,
                        "person": order[1],
                        "start_time_min": start2,
                        "end_time_min": end2,
                    },
                ],
                "friends_met": 2,
                "total_meeting_minutes": d1 + d2,
                "finish_time": end2,
            }
        return None

    if e1_candidate1 >= start1 + p1["min_minutes"]:
        schedule = build_schedule(e1_candidate1)

    # Strategy B: leave p1 as late as possible while still ensuring p2 min
    if schedule is None:
        e1_candidate2 = min(p1["we"], p2["we"] - p2["min_minutes"] - t12)
        if e1_candidate2 >= start1 + p1["min_minutes"]:
            schedule = build_schedule(e1_candidate2)

    return schedule

# Consider schedules
candidates = []

# Both friends, both orderings
for order in [["Kenneth", "Thomas"], ["Thomas", "Kenneth"]]:
    sched = feasible_both(order)
    if sched:
        candidates.append(sched)

# Single friend schedules
for name in people.keys():
    sched = feasible_single(name)
    if sched:
        candidates.append(sched)

# If no candidate, output empty itinerary
if not candidates:
    result = {"itinerary": []}
else:
    # Choose best: maximize friends_met, then total_meeting_minutes, then earliest finish_time
    candidates.sort(
        key=lambda s: (s["friends_met"], s["total_meeting_minutes"], -s["finish_time"]),
        reverse=True,
    )
    best = candidates[0]
    # Format times
    itinerary_out = []
    for item in best["itinerary"]:
        itinerary_out.append(
            {
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": to_str(item["start_time_min"]),
                "end_time": to_str(item["end_time_min"]),
            }
        )
    result = {"itinerary": itinerary_out}

print(json.dumps(result, ensure_ascii=False))