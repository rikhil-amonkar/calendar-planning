import json
import itertools

def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input parameters and constraints
start_location = "Presidio"
start_time_str = "9:00"

people = [
    {
        "name": "Jason",
        "location": "Richmond District",
        "window_start": "13:00",
        "window_end": "20:45",
        "min_duration": 90
    },
    {
        "name": "Melissa",
        "location": "North Beach",
        "window_start": "18:45",
        "window_end": "20:15",
        "min_duration": 45
    },
    {
        "name": "Brian",
        "location": "Financial District",
        "window_start": "9:45",
        "window_end": "21:45",
        "min_duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Golden Gate Park",
        "window_start": "8:45",
        "window_end": "21:30",
        "min_duration": 105
    },
    {
        "name": "Laura",
        "location": "Union Square",
        "window_start": "14:15",
        "window_end": "19:30",
        "min_duration": 75
    },
]

# Convert string times to minutes
for p in people:
    p["ws_min"] = parse_time(p["window_start"])
    p["we_min"] = parse_time(p["window_end"])

start_time = parse_time(start_time_str)

# Travel times (in minutes), directed
travel = {
    "Presidio": {
        "Richmond District": 7,
        "North Beach": 18,
        "Financial District": 23,
        "Golden Gate Park": 12,
        "Union Square": 22
    },
    "Richmond District": {
        "Presidio": 7,
        "North Beach": 17,
        "Financial District": 22,
        "Golden Gate Park": 9,
        "Union Square": 21
    },
    "North Beach": {
        "Presidio": 17,
        "Richmond District": 18,
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Union Square": 7
    },
    "Financial District": {
        "Presidio": 22,
        "Richmond District": 21,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Union Square": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Richmond District": 7,
        "North Beach": 24,
        "Financial District": 26,
        "Union Square": 22
    },
    "Union Square": {
        "Presidio": 24,
        "Richmond District": 20,
        "North Beach": 10,
        "Financial District": 9,
        "Golden Gate Park": 22
    }
}

# Ensure zero self-travel
locations = set(travel.keys())
for loc in list(locations):
    if loc not in travel:
        travel[loc] = {}
    for loc2 in locations:
        if loc2 == loc:
            travel[loc2][loc] = 0
        else:
            # If a directed edge is missing (shouldn't happen), skip; handled later
            pass

def schedule_for_order(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    total_meet = 0

    for p in order:
        # Travel time between locations; if missing, fail
        if cur_loc not in travel or p["location"] not in travel[cur_loc]:
            return None  # infeasible due to missing travel data
        t_travel = travel[cur_loc][p["location"]]
        total_travel += t_travel
        arrive = cur_time + t_travel

        # Earliest feasible start
        start_mt = max(arrive, p["ws_min"])
        wait = max(0, start_mt - arrive)
        total_wait += wait

        end_mt = start_mt + p["min_duration"]
        if end_mt > p["we_min"]:
            return None  # cannot fit min duration
        # Append meeting
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_str(start_mt),
            "end_time": minutes_to_str(end_mt)
        })
        total_meet += p["min_duration"]
        # Update current
        cur_loc = p["location"]
        cur_time = end_mt

    return {
        "itinerary": itinerary,
        "end_time": cur_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "total_meet": total_meet,
    }

def optimize_schedule(people):
    n = len(people)
    best = None

    # Search by decreasing subset size to maximize number of friends met
    for k in range(n, 0, -1):
        found_any = False
        for subset in itertools.combinations(people, k):
            for order in itertools.permutations(subset):
                sched = schedule_for_order(order)
                if sched is None:
                    continue
                found_any = True
                # Evaluate tie-breakers:
                # 1) Max number met (handled by loop)
                # 2) Earliest finish
                # 3) Minimum total travel
                # 4) Minimum total wait
                key = (k, -sched["total_meet"], sched["end_time"], sched["total_travel"], sched["total_wait"])
                # Note: total_meet is constant for given subset (sum of mins). We include as - to prefer larger meetings if ever expanded.
                if best is None or (k > best["k"]) or (k == best["k"] and (sched["end_time"] < best["sched"]["end_time"] or
                    (sched["end_time"] == best["sched"]["end_time"] and (sched["total_travel"] < best["sched"]["total_travel"] or
                    (sched["total_travel"] == best["sched"]["total_travel"] and sched["total_wait"] < best["sched"]["total_wait"]))))):
                    best = {"k": k, "sched": sched}
        if found_any:
            break
    if best is None:
        return {"itinerary": []}
    return {"itinerary": best["sched"]["itinerary"]}

result = optimize_schedule(people)
print(json.dumps(result))