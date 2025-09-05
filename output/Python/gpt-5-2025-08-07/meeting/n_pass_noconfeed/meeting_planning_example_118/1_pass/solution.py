"""SOLUTION:"""

import itertools
import json

# Helper functions
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
locations = ["Bayview", "Union Square", "Presidio"]

# Directed travel times in minutes
travel_time = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

# Start conditions
start_location = "Bayview"
start_time = to_minutes(9, 0)  # 9:00

# Friends constraints
friends = [
    {
        "name": "Richard",
        "location": "Union Square",
        "avail_start": to_minutes(8, 45),
        "avail_end": to_minutes(13, 0),
        "min_duration": 120,
    },
    {
        "name": "Charles",
        "location": "Presidio",
        "avail_start": to_minutes(9, 45),
        "avail_end": to_minutes(13, 0),
        "min_duration": 120,
    },
]

# Scheduling logic
def compute_schedule_for_order(order):
    # First, feasibility check with earliest schedule using minimum durations
    curr_loc = start_location
    curr_t = start_time
    n = len(order)

    earliest_starts = [0] * n
    arrivals_min = [0] * n

    for i, p in enumerate(order):
        if (curr_loc, p["location"]) not in travel_time:
            return None
        arr = curr_t + travel_time[(curr_loc, p["location"])]
        arrivals_min[i] = arr
        start = max(arr, p["avail_start"])
        earliest_starts[i] = start
        if start + p["min_duration"] > p["avail_end"]:
            return None  # infeasible: cannot fit minimum block
        curr_t = start + p["min_duration"]
        curr_loc = p["location"]

    # Backward pass: latest feasible starts that still allow minimum durations for all following
    s_latest = [0] * n
    # Last person
    last = order[-1]
    s_latest[-1] = last["avail_end"] - last["min_duration"]
    # Previous persons
    for j in range(n - 2, -1, -1):
        p = order[j]
        nxt = order[j + 1]
        t_travel = travel_time[(p["location"], nxt["location"])]
        s_latest[j] = min(p["avail_end"] - p["min_duration"], s_latest[j + 1] - t_travel - nxt["min_duration"])

    # Check earliest start <= latest start for all
    for i in range(n):
        if earliest_starts[i] > s_latest[i]:
            return None

    # Forward pass: build maximal-duration meetings without violating later feasibility
    itinerary = []
    curr_loc = start_location
    curr_t = start_time
    total_meeting_minutes = 0
    total_waiting_minutes = 0

    for i, p in enumerate(order):
        arr = curr_t + travel_time[(curr_loc, p["location"])]
        start = max(arr, p["avail_start"])
        waiting = max(0, p["avail_start"] - arr)
        total_waiting_minutes += waiting

        # Latest time we can depart this meeting
        if i < n - 1:
            latest_depart = s_latest[i + 1] - travel_time[(p["location"], order[i + 1]["location"])]
        else:
            latest_depart = p["avail_end"]

        # Maximize meeting end time without violating constraints
        end = min(p["avail_end"], latest_depart)
        # Ensure minimum duration
        if end < start + p["min_duration"]:
            end = start + p["min_duration"]
        # Final feasibility check
        if end > p["avail_end"] or end < start:
            return None

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
        })
        total_meeting_minutes += (end - start)

        curr_loc = p["location"]
        curr_t = end

    # Build metrics
    finish_time = curr_t
    metrics = {
        "count_met": n,
        "total_meeting_minutes": total_meeting_minutes,
        "total_waiting_minutes": total_waiting_minutes,
        "finish_time": finish_time,
    }
    return itinerary, metrics

def optimize_schedule():
    best = None
    best_metrics = None

    # Explore all non-empty subsets and their orders
    for r in range(1, len(friends) + 1):
        for subset in itertools.combinations(friends, r):
            for order in itertools.permutations(subset):
                res = compute_schedule_for_order(order)
                if not res:
                    continue
                itinerary, metrics = res

                # Objective:
                # 1) Maximize count_met
                # 2) Maximize total_meeting_minutes
                # 3) Minimize total_waiting_minutes
                # 4) Minimize finish_time
                if best is None:
                    best = itinerary
                    best_metrics = metrics
                else:
                    better = False
                    if metrics["count_met"] > best_metrics["count_met"]:
                        better = True
                    elif metrics["count_met"] == best_metrics["count_met"]:
                        if metrics["total_meeting_minutes"] > best_metrics["total_meeting_minutes"]:
                            better = True
                        elif metrics["total_meeting_minutes"] == best_metrics["total_meeting_minutes"]:
                            if metrics["total_waiting_minutes"] < best_metrics["total_waiting_minutes"]:
                                better = True
                            elif metrics["total_waiting_minutes"] == best_metrics["total_waiting_minutes"]:
                                if metrics["finish_time"] < best_metrics["finish_time"]:
                                    better = True
                    if better:
                        best = itinerary
                        best_metrics = metrics

    if best is None:
        return {"itinerary": []}
    else:
        return {"itinerary": best}

def main():
    result = optimize_schedule()
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()