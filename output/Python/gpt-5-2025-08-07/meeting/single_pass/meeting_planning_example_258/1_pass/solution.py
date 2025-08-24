import json
from itertools import permutations

def tm(h, m=0):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input variables (meeting constraints and travel times)
start_location = "Embarcadero"
start_time = tm(9, 0)

travel = {
    "Embarcadero": {
        "Presidio": 20,
        "Richmond District": 21,
        "Fisherman's Wharf": 6,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Richmond District": 7,
        "Fisherman's Wharf": 19,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Presidio": 7,
        "Fisherman's Wharf": 18,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Presidio": 17,
        "Richmond District": 18,
    },
}

people = [
    {
        "name": "Betty",
        "location": "Presidio",
        "window_start": tm(10, 15),
        "window_end": tm(21, 30),
        "min_duration": 45,
    },
    {
        "name": "David",
        "location": "Richmond District",
        "window_start": tm(13, 0),
        "window_end": tm(20, 15),
        "min_duration": 90,
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "window_start": tm(9, 15),
        "window_end": tm(20, 15),
        "min_duration": 120,
    },
]

def schedule_for_order(order, start_loc, start_t):
    current_loc = start_loc
    current_time = start_t
    itinerary = []
    total_wait = 0
    total_travel = 0
    total_meet = 0

    for person in order:
        dest = person["location"]
        # Travel
        if current_loc == dest:
            travel_time = 0
        else:
            travel_time = travel[current_loc][dest]
        arrival = current_time + travel_time
        # Wait if early
        meeting_start = max(arrival, person["window_start"])
        wait = max(0, meeting_start - arrival)
        meeting_end = meeting_start + person["min_duration"]

        # Feasibility check
        if meeting_end > person["window_end"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": dest,
            "person": person["name"],
            "start": meeting_start,
            "end": meeting_end,
        })

        total_wait += wait
        total_travel += travel_time
        total_meet += person["min_duration"]
        current_loc = dest
        current_time = meeting_end

    result = {
        "itinerary": itinerary,
        "metrics": {
            "met_count": len(itinerary),
            "finish_time": current_time,
            "total_wait": total_wait,
            "total_travel": total_travel,
            "total_meet": total_meet,
        }
    }
    return result

def choose_best_schedule(people, start_loc, start_t):
    n = len(people)
    best = None
    best_score = None

    # Try all permutation lengths from n down to 1 (meet as many friends as possible)
    for k in range(n, 0, -1):
        for order in permutations(people, k):
            result = schedule_for_order(order, start_loc, start_t)
            if result is None:
                continue
            met_count = result["metrics"]["met_count"]
            finish = result["metrics"]["finish_time"]
            total_wait = result["metrics"]["total_wait"]
            total_travel = result["metrics"]["total_travel"]
            total_meet = result["metrics"]["total_meet"]

            # Objective:
            # 1) Maximize number of friends met
            # 2) Minimize finish time
            # 3) Minimize total waiting time
            # 4) Minimize total travel time
            # 5) Maximize total meeting time (redundant with fixed minima but included for completeness)
            score = (
                met_count,
                -finish,
                -total_wait,
                -total_travel,
                total_meet,
            )

            if best_score is None or score > best_score:
                best_score = score
                best = result

        # If we found at least one feasible schedule for this k, no need to search smaller k
        if best is not None and best["metrics"]["met_count"] == k:
            break

    return best

best = choose_best_schedule(people, start_location, start_time)

# Prepare JSON output
output = {"itinerary": []}
if best:
    for item in best["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"]),
        })

print(json.dumps(output, ensure_ascii=False))