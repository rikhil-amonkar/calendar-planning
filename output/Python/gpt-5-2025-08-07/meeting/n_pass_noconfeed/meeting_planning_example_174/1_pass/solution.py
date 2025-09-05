import json
from typing import Dict, Tuple, List

def parse_time(t: str) -> int:
    # t example: "9:00", "13:30"
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def fmt_time(m: int) -> str:
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input parameters (can be edited)
start_location = "Nob Hill"
start_time_str = "9:00"

travel_minutes: Dict[Tuple[str, str], int] = {
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
        "min_duration": 75,
    },
    "Kenneth": {
        "location": "Mission District",
        "window_start": "12:00",
        "window_end": "15:45",
        "min_duration": 45,
    }
}

# Convert input times to minutes
start_time = parse_time(start_time_str)
for person in people.values():
    person["ws_min"] = parse_time(person["window_start"])
    person["we_min"] = parse_time(person["window_end"])

def ttime(a: str, b: str) -> int:
    return travel_minutes[(a, b)]

def schedule_single(person_name: str):
    # Returns (feasible, itinerary, finish_time, total_wait, total_travel)
    p = people[person_name]
    loc = p["location"]
    ws = p["ws_min"]
    we = p["we_min"]
    dur = p["min_duration"]

    # Earliest arrival if we left immediately
    arr_earliest = start_time + ttime(start_location, loc)
    # We can always leave later to have zero wait; choose start to minimize finish time
    s = max(ws, arr_earliest)
    if s + dur > we:
        return (False, [], None, None, None)
    e = s + dur
    itinerary = [{
        "action": "meet",
        "location": loc,
        "person": person_name,
        "start_time": fmt_time(s),
        "end_time": fmt_time(e),
    }]
    # We can time our departure to arrive just-in-time, so wait before first meeting is 0
    total_wait = 0
    total_travel = ttime(start_location, loc)
    return (True, itinerary, e, total_wait, total_travel)

def schedule_two(first: str, second: str):
    # Returns (feasible, itinerary, finish_time, total_wait, total_travel)
    a = people[first]
    b = people[second]

    # Data for A
    a_loc = a["location"]; a_ws = a["ws_min"]; a_we = a["we_min"]; a_dur = a["min_duration"]
    # Data for B
    b_loc = b["location"]; b_ws = b["ws_min"]; b_we = b["we_min"]; b_dur = b["min_duration"]

    # Earliest arrival at A if we left immediately; we can leave later to reduce waiting at A to zero
    arrive_A_earliest = start_time + ttime(start_location, a_loc)
    sA_min = max(a_ws, arrive_A_earliest)
    sA_max = a_we - a_dur
    if sA_min > sA_max:
        return (False, [], None, None, None)

    # Desired start for A so that arrival to B is exactly at B's window start (to minimize wait at B)
    desired_sA = b_ws - ttime(a_loc, b_loc) - a_dur

    if sA_min <= min(sA_max, desired_sA):
        # There exists an sA such that we arrive at B right at b_ws; choose as late as possible (min waiting at B and no effect on finish time)
        sA = min(sA_max, desired_sA)
        # We can adjust departure to arrive exactly at sA, so wait at A is 0
        waitA = 0
    else:
        # Even with earliest sA, arrival to B will be after b_ws; choose earliest sA to minimize finish time
        sA = sA_min
        waitA = 0  # as we can depart to arrive just-in-time

    eA = sA + a_dur
    arrival_B = eA + ttime(a_loc, b_loc)
    sB = max(b_ws, arrival_B)
    eB = sB + b_dur

    if eB > b_we:
        return (False, [], None, None, None)

    waitB = max(0, b_ws - arrival_B)
    total_wait = waitA + waitB
    total_travel = ttime(start_location, a_loc) + ttime(a_loc, b_loc)

    itinerary = [
        {
            "action": "meet",
            "location": a_loc,
            "person": first,
            "start_time": fmt_time(sA),
            "end_time": fmt_time(eA),
        },
        {
            "action": "meet",
            "location": b_loc,
            "person": second,
            "start_time": fmt_time(sB),
            "end_time": fmt_time(eB),
        },
    ]
    return (True, itinerary, eB, total_wait, total_travel)

# Generate candidate schedules
candidates: List[Tuple[int, int, int, int, List[Dict]]] = []  # stores (-num_met, finish_time, total_wait, total_travel, itinerary)

# Meet both in order [Kenneth, Thomas]
ok, itn, fin, tw, tt = schedule_two("Kenneth", "Thomas")
if ok:
    candidates.append((-2, fin, tw, tt, itn))

# Meet both in order [Thomas, Kenneth]
ok, itn, fin, tw, tt = schedule_two("Thomas", "Kenneth")
if ok:
    candidates.append((-2, fin, tw, tt, itn))

# Only Kenneth
ok, itn, fin, tw, tt = schedule_single("Kenneth")
if ok:
    candidates.append((-1, fin, tw, tt, itn))

# Only Thomas
ok, itn, fin, tw, tt = schedule_single("Thomas")
if ok:
    candidates.append((-1, fin, tw, tt, itn))

# If somehow no candidates, output empty itinerary
if not candidates:
    result = {"itinerary": []}
else:
    # Choose optimal according to objectives:
    # 1) maximize number of friends met  -> we stored as negative count, so smaller is better
    # 2) minimize finish time
    # 3) minimize total waiting
    # 4) minimize total travel time
    candidates.sort(key=lambda x: (x[0], x[1], x[2], x[3]))
    best_itinerary = candidates[0][4]
    result = {"itinerary": best_itinerary}

print(json.dumps(result, ensure_ascii=False))