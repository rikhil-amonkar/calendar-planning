import itertools
import json

def minutes(h, m):
    return h * 60 + m

def parse_time_24(t):
    # expects 'H:MM' or 'HH:MM'
    parts = t.split(":")
    return int(parts[0]) * 60 + int(parts[1])

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input parameters (meeting constraints)
start_location = "Sunset District"
arrival_time_str = "9:00"
arrival_time = parse_time_24(arrival_time_str)

friends = [
    {"name": "Charles", "location": "Alamo Square", "start": parse_time_24("18:00"), "end": parse_time_24("20:45"), "min_duration": 90},
    {"name": "Margaret", "location": "Russian Hill", "start": parse_time_24("9:00"), "end": parse_time_24("16:00"), "min_duration": 30},
    {"name": "Daniel", "location": "Golden Gate Park", "start": parse_time_24("8:00"), "end": parse_time_24("13:30"), "min_duration": 15},
    {"name": "Stephanie", "location": "Mission District", "start": parse_time_24("20:30"), "end": parse_time_24("22:00"), "min_duration": 90},
]

# Travel matrix (in minutes), asymmetric where specified
L_SUNSET = "Sunset District"
L_ALAMO = "Alamo Square"
L_RUSSIAN = "Russian Hill"
L_GGP = "Golden Gate Park"
L_MISSION = "Mission District"

travel = {
    L_SUNSET: {
        L_ALAMO: 17,
        L_RUSSIAN: 24,
        L_GGP: 11,
        L_MISSION: 24,
    },
    L_ALAMO: {
        L_SUNSET: 16,
        L_RUSSIAN: 13,
        L_GGP: 9,
        L_MISSION: 10,
    },
    L_RUSSIAN: {
        L_SUNSET: 23,
        L_ALAMO: 15,
        L_GGP: 21,
        L_MISSION: 16,
    },
    L_GGP: {
        L_SUNSET: 10,
        L_ALAMO: 10,
        L_RUSSIAN: 19,
        L_MISSION: 17,
    },
    L_MISSION: {
        L_SUNSET: 24,
        L_ALAMO: 11,
        L_RUSSIAN: 15,
        L_GGP: 17,
    },
}

def get_travel(a, b):
    if a == b:
        return 0
    return travel[a][b]

def schedule_order(order):
    # Compute latest feasible start times via backward pass to minimize idle
    n = len(order)
    if n == 0:
        return False, None, None

    L = [None] * n  # latest start times
    # last meeting
    last = order[-1]
    L[-1] = last["end"] - last["min_duration"]
    # backward for others
    for i in range(n - 2, -1, -1):
        cur = order[i]
        nxt = order[i + 1]
        latest_due_to_window = cur["end"] - cur["min_duration"]
        latest_due_to_next = L[i + 1] - get_travel(cur["location"], nxt["location"]) - cur["min_duration"]
        L[i] = min(latest_due_to_window, latest_due_to_next)
        # Early pruning: if latest start before window start, infeasible
        if L[i] < cur["start"]:
            return False, None, None
    # Also ensure last is not before its window start
    if L[-1] < last["start"]:
        return False, None, None

    # Forward pass to set actual starts at latest feasible times while respecting arrival constraints
    itinerary = []
    prev_loc = start_location
    prev_end = arrival_time
    total_travel = 0
    for i, p in enumerate(order):
        t = get_travel(prev_loc, p["location"])
        total_travel += t
        earliest_arrival = prev_end + t
        low = max(earliest_arrival, p["start"])
        if low > L[i]:
            return False, None, None
        start_time_meet = L[i]
        end_time_meet = start_time_meet + p["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start_time_meet),
            "end_time": fmt_time(end_time_meet),
        })
        prev_loc = p["location"]
        prev_end = end_time_meet

    # Metrics for tie-breaking
    # Primary objective: maximize count (handled externally)
    # Secondary: minimize total travel
    return True, itinerary, {"travel": total_travel}

best_itinerary = None
best_metrics = None
best_count = -1

# Enumerate subsets by size descending to maximize number of meetings
N = len(friends)
for size in range(N, 0, -1):
    found_for_size = False
    for subset in itertools.combinations(friends, size):
        for perm in itertools.permutations(subset):
            # Quick feasibility pruning: Charles before Stephanie (evening order constraint)
            # Not necessary but speeds up.
            names = [p["name"] for p in perm]
            if "Charles" in names and "Stephanie" in names:
                if names.index("Charles") > names.index("Stephanie"):
                    # reverse order would be infeasible because Charles ends by 20:45 and Stephanie starts 20:30.
                    continue
            feasible, itinerary, metrics = schedule_order(list(perm))
            if feasible:
                found_for_size = True
                if size > best_count:
                    best_count = size
                    best_itinerary = itinerary
                    best_metrics = metrics
                else:
                    # tie-break by travel
                    if size == best_count:
                        if metrics["travel"] < best_metrics["travel"]:
                            best_itinerary = itinerary
                            best_metrics = metrics
                        elif metrics["travel"] == best_metrics["travel"]:
                            # tiebreaker by lexicographic itinerary string to have determinism
                            it_str = json.dumps(itinerary, ensure_ascii=False)
                            best_str = json.dumps(best_itinerary, ensure_ascii=False)
                            if it_str < best_str:
                                best_itinerary = itinerary
                                best_metrics = metrics
    if found_for_size:
        break

output = {
    "itinerary": best_itinerary if best_itinerary is not None else []
}

print(json.dumps(output))