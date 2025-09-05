import itertools
import json

def minutes(h, m):
    return h * 60 + m

def m2str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def schedule_order(order, friends, travel, start_loc, start_time):
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        info = friends[person]
        travel_time = travel[current_loc][info["location"]]
        arrival = current_time + travel_time
        meeting_start = max(arrival, info["start"])
        meeting_end = meeting_start + info["duration"]
        if meeting_end > info["end"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": info["location"],
            "person": person,
            "start_min": meeting_start,
            "end_min": meeting_end
        })
        total_travel += travel_time
        wait = max(0, info["start"] - arrival)
        total_wait += wait
        current_time = meeting_end
        current_loc = info["location"]

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

def compute_optimal_schedule():
    # Locations
    E = "Embarcadero"
    R = "Richmond District"
    U = "Union Square"
    F = "Financial District"
    P = "Pacific Heights"
    N = "Nob Hill"
    B = "Bayview"

    # Travel times (minutes) - directed
    travel = {
        E: {R:21, U:10, F:5, P:11, N:10, B:21},
        R: {E:19, U:21, F:22, P:10, N:17, B:26},
        U: {E:11, R:20, F:9,  P:15, N:9,  B:15},
        F: {E:4,  R:21, U:9,  P:13, N:8,  B:19},
        P: {E:10, R:12, U:12, F:13, N:8,  B:22},
        N: {E:9,  R:14, U:7,  F:9,  P:8,  B:19},
        B: {E:19, R:25, U:17, F:19, P:23, N:20},
    }

    # Friends constraints
    friends = {
        "Kenneth": {"location": R, "start": minutes(21,15), "end": minutes(22,0), "duration": 30},
        "Lisa":    {"location": U, "start": minutes(9,0),   "end": minutes(16,30), "duration": 45},
        "Joshua":  {"location": F, "start": minutes(12,0),  "end": minutes(15,15), "duration": 15},
        "Nancy":   {"location": P, "start": minutes(8,0),   "end": minutes(11,30), "duration": 90},
        "Andrew":  {"location": N, "start": minutes(11,30), "end": minutes(20,15), "duration": 60},
        "John":    {"location": B, "start": minutes(16,45), "end": minutes(21,30), "duration": 75},
    }

    start_loc = E
    start_time = minutes(9,0)

    people = list(friends.keys())

    best_solution = None
    best_key = None

    # Try all subset sizes from max to min
    n = len(people)
    for k in range(n, 0, -1):
        any_feasible_at_k = False
        for order in itertools.permutations(people, k):
            sched = schedule_order(order, friends, travel, start_loc, start_time)
            if sched is None:
                continue
            any_feasible_at_k = True
            # Primary: maximize count (k)
            # Secondary: minimize end time
            # Tertiary: minimize total travel
            # Quaternary: minimize total wait
            key = (-k, sched["end_time"], sched["total_travel"], sched["total_wait"])
            if best_key is None or key < best_key:
                best_key = key
                best_solution = (order, sched)
        if any_feasible_at_k:
            break

    # Build output JSON
    output = {"itinerary": []}
    if best_solution:
        order, sched = best_solution
        for item in sched["itinerary"]:
            output["itinerary"].append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": m2str(item["start_min"]),
                "end_time": m2str(item["end_min"])
            })
    return output

if __name__ == "__main__":
    result = compute_optimal_schedule()
    print(json.dumps(result, ensure_ascii=False))