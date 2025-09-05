import itertools
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Input variables based on the given constraints
start_location = "Embarcadero"
start_time = minutes(9, 0)

travel_times = {
    "Embarcadero": {
        "Embarcadero": 0,
        "Presidio": 20,
        "Richmond District": 21,
        "Fisherman's Wharf": 6,
    },
    "Presidio": {
        "Embarcadero": 20,
        "Presidio": 0,
        "Richmond District": 7,
        "Fisherman's Wharf": 19,
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Presidio": 7,
        "Richmond District": 0,
        "Fisherman's Wharf": 18,
    },
    "Fisherman's Wharf": {
        "Embarcadero": 8,
        "Presidio": 17,
        "Richmond District": 18,
        "Fisherman's Wharf": 0,
    },
}

participants = [
    {
        "name": "Betty",
        "location": "Presidio",
        "window_start": minutes(10, 15),
        "window_end": minutes(21, 30),
        "min_duration": 45,
    },
    {
        "name": "David",
        "location": "Richmond District",
        "window_start": minutes(13, 0),
        "window_end": minutes(20, 15),
        "min_duration": 90,
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "window_start": minutes(9, 15),
        "window_end": minutes(20, 15),
        "min_duration": 120,
    },
]

def feasible_schedule(order):
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_wait = 0

    for person in order:
        travel = travel_times[cur_loc][person["location"]]
        arrival = cur_time + travel
        start = max(arrival, person["window_start"])
        wait = max(0, person["window_start"] - arrival)

        end = start + person["min_duration"]
        if end > person["window_end"]:
            return None  # infeasible

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": start,
            "end_time": end
        })
        total_travel += travel
        total_wait += wait
        cur_loc = person["location"]
        cur_time = end

    return {
        "itinerary": itinerary,
        "finish_time": cur_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

def choose_best_schedule(participants):
    best = None

    # Try all subsets (largest first) and all permutations within each subset
    n = len(participants)
    for k in range(n, 0, -1):
        found_for_k = False
        for subset in itertools.combinations(participants, k):
            for order in itertools.permutations(subset):
                sched = feasible_schedule(order)
                if sched is None:
                    continue
                found_for_k = True
                if best is None:
                    best = sched
                else:
                    # Compare with current best:
                    # Primary: max number of meetings
                    # Secondary: earliest finish time
                    # Tertiary: minimal total travel
                    # Quaternary: minimal total wait
                    best_meetings = len(best["itinerary"])
                    cur_meetings = len(sched["itinerary"])
                    if cur_meetings > best_meetings:
                        best = sched
                    elif cur_meetings == best_meetings:
                        if sched["finish_time"] < best["finish_time"]:
                            best = sched
                        elif sched["finish_time"] == best["finish_time"]:
                            if sched["total_travel"] < best["total_travel"]:
                                best = sched
                            elif sched["total_travel"] == best["total_travel"]:
                                if sched["total_wait"] < best["total_wait"]:
                                    best = sched
        if found_for_k:
            break  # We found at least one schedule for this k, no need to try smaller subsets
    return best

best_schedule = choose_best_schedule(participants)

# Convert times to required string format
output_itinerary = []
if best_schedule:
    for item in best_schedule["itinerary"]:
        output_itinerary.append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start_time"]),
            "end_time": fmt_time(item["end_time"]),
        })

result = {
    "itinerary": output_itinerary
}

print(json.dumps(result))