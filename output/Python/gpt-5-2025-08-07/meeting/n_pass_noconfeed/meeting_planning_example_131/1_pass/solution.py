# SOLUTION:
import json
from itertools import permutations

# ----------------------------
# Input variables (constraints)
# ----------------------------
# Locations
PACIFIC_HEIGHTS = "Pacific Heights"
PRESIDIO = "Presidio"
MARINA_DISTRICT = "Marina District"

# Travel times in minutes (asymmetric where specified)
travel_minutes = {
    (PACIFIC_HEIGHTS, PRESIDIO): 11,
    (PACIFIC_HEIGHTS, MARINA_DISTRICT): 6,
    (PRESIDIO, PACIFIC_HEIGHTS): 11,
    (PRESIDIO, MARINA_DISTRICT): 10,
    (MARINA_DISTRICT, PACIFIC_HEIGHTS): 7,
    (MARINA_DISTRICT, PRESIDIO): 10,
}

# Start information
arrival_location = PACIFIC_HEIGHTS
arrival_time = (9 * 60) + 0  # 9:00 -> minutes since midnight

# Friends and constraints
friends = {
    "Jason": {
        "location": PRESIDIO,
        "avail_start": (10 * 60) + 0,   # 10:00
        "avail_end": (16 * 60) + 15,    # 16:15
        "min_duration": 90
    },
    "Kenneth": {
        "location": MARINA_DISTRICT,
        "avail_start": (15 * 60) + 30,  # 15:30
        "avail_end": (16 * 60) + 45,    # 16:45
        "min_duration": 45
    }
}

# ----------------------------
# Helper functions
# ----------------------------
def fmt_time(minutes_since_midnight: int) -> str:
    h = minutes_since_midnight // 60
    m = minutes_since_midnight % 60
    return f"{h}:{m:02d}"

def travel_time(from_loc: str, to_loc: str) -> int:
    return travel_minutes[(from_loc, to_loc)]

def can_arrive_by(start_loc: str, current_time: int, dest_loc: str, deadline: int) -> bool:
    return current_time + travel_time(start_loc, dest_loc) <= deadline

# ----------------------------
# Search over possible schedules
# ----------------------------
def evaluate_single(person_name: str):
    f = friends[person_name]
    loc = f["location"]
    s_earliest = max(f["avail_start"], arrival_time + travel_time(arrival_location, loc))
    s_latest = f["avail_end"] - f["min_duration"]

    best = None
    if s_earliest <= s_latest:
        for s in range(s_earliest, s_latest + 1):
            min_dur = f["min_duration"]
            max_dur = f["avail_end"] - s
            for d in range(min_dur, max_dur + 1):
                e = s + d
                # Metrics: maximize (num_met, total_meeting, -finish_time, -total_travel)
                score = (1, d, -e, -travel_time(arrival_location, loc))
                itinerary = [{
                    "action": "meet",
                    "location": loc,
                    "person": person_name,
                    "start_time": fmt_time(s),
                    "end_time": fmt_time(e)
                }]
                cand = (score, itinerary, e)
                if best is None or cand[0] > best[0]:
                    best = cand
    return best

def evaluate_pair(order):
    p1, p2 = order
    f1, f2 = friends[p1], friends[p2]
    loc1, loc2 = f1["location"], f2["location"]

    # First meeting start window considering travel from arrival
    s1_earliest = max(f1["avail_start"], arrival_time + travel_time(arrival_location, loc1))
    s1_latest = f1["avail_end"] - f1["min_duration"]

    best = None
    if s1_earliest <= s1_latest:
        for s1 in range(s1_earliest, s1_latest + 1):
            d1_min = f1["min_duration"]
            d1_max = f1["avail_end"] - s1
            for d1 in range(d1_min, d1_max + 1):
                e1 = s1 + d1

                # Travel to second
                s2_candidate = e1 + travel_time(loc1, loc2)
                s2 = max(f2["avail_start"], s2_candidate)
                if s2 > f2["avail_end"] - f2["min_duration"]:
                    continue

                d2_min = f2["min_duration"]
                d2_max = f2["avail_end"] - s2
                for d2 in range(d2_min, d2_max + 1):
                    e2 = s2 + d2
                    total_meeting = d1 + d2
                    total_travel = travel_time(arrival_location, loc1) + travel_time(loc1, loc2)

                    # Prefer earlier second start if tied to push earlier engagement start
                    # Metrics: maximize (num_met, total_meeting, -finish_time, -total_travel, -second_start)
                    score = (2, total_meeting, -e2, -total_travel, -s2)

                    itinerary = [
                        {
                            "action": "meet",
                            "location": loc1,
                            "person": p1,
                            "start_time": fmt_time(s1),
                            "end_time": fmt_time(e1)
                        },
                        {
                            "action": "meet",
                            "location": loc2,
                            "person": p2,
                            "start_time": fmt_time(s2),
                            "end_time": fmt_time(e2)
                        }
                    ]
                    cand = (score, itinerary, e2)
                    if best is None or cand[0] > best[0]:
                        best = cand
    return best

def compute_optimal_schedule():
    candidates = []

    # Single-person schedules
    for person in friends.keys():
        res = evaluate_single(person)
        if res is not None:
            candidates.append(res)

    # Two-person schedules (all orders)
    for order in permutations(friends.keys(), 2):
        res = evaluate_pair(order)
        if res is not None:
            candidates.append(res)

    if not candidates:
        # No feasible meetings (unlikely with given constraints)
        return {"itinerary": []}

    # Select best candidate by score
    best = max(candidates, key=lambda x: x[0])
    return {"itinerary": best[1]}

# ----------------------------
# Run and output JSON
# ----------------------------
if __name__ == "__main__":
    result = compute_optimal_schedule()
    print(json.dumps(result, ensure_ascii=False))