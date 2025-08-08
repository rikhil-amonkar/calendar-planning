import json
import itertools

def parse_time(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Nob Hill"
start_time_str = "9:00"

people = {
    "Jeffrey": {
        "location": "Presidio",
        "start": "8:00",
        "end": "10:00",
        "min_duration": 105
    },
    "Steven": {
        "location": "North Beach",
        "start": "13:30",
        "end": "22:00",
        "min_duration": 45
    },
    "Barbara": {
        "location": "Fisherman's Wharf",
        "start": "18:00",
        "end": "21:30",
        "min_duration": 30
    },
    "John": {
        "location": "Pacific Heights",
        "start": "9:00",
        "end": "13:30",
        "min_duration": 15
    }
}

# Convert time strings to minutes
for p in people.values():
    p["start_min"] = parse_time(p["start"])
    p["end_min"] = parse_time(p["end"])

start_time = parse_time(start_time_str)

# Travel times (in minutes)
travel = {
    "Nob Hill": {
        "Presidio": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Pacific Heights": 8
    },
    "Presidio": {
        "Nob Hill": 18,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Pacific Heights": 11
    },
    "North Beach": {
        "Nob Hill": 7,
        "Presidio": 17,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "Presidio": 17,
        "North Beach": 6,
        "Pacific Heights": 12
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Presidio": 11,
        "North Beach": 9,
        "Fisherman's Wharf": 13
    }
}

locations = list(travel.keys())

def travel_time(a, b):
    if a == b:
        return 0
    return travel[a][b]

def compute_schedule(order_names):
    # Build ordered list of meeting specs
    order = [ (name, people[name]["location"], people[name]["start_min"], people[name]["end_min"], people[name]["min_duration"]) for name in order_names ]
    itinerary = []
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_idle = 0

    for (name, loc, avail_start, avail_end, dur) in order:
        t_travel = travel_time(cur_loc, loc)
        arrive = cur_time + t_travel
        meet_start = max(arrive, avail_start)
        meet_end = meet_start + dur
        # infeasible if end after availability end
        if meet_end > avail_end:
            return None
        idle_wait = meet_start - arrive  # waiting anywhere between prev end and current start
        total_idle += idle_wait if idle_wait > 0 else 0
        total_travel += t_travel

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(meet_start),
            "end_time": fmt_time(meet_end)
        })
        cur_loc = loc
        cur_time = meet_end

    return {
        "itinerary": itinerary,
        "metrics": {
            "num_meetings": len(order),
            "total_travel": total_travel,
            "total_idle": total_idle,
            "end_time": cur_time
        }
    }

# Evaluate all combinations and permutations to find optimal by:
# 1) Maximize number of meetings
# 2) Minimize total idle time
# 3) Minimize total travel time
# 4) Minimize end time
names = list(people.keys())
best = None
best_score = None

# Iterate subsets by size descending to ensure we prefer larger number of meetings,
# but still compute a unified score to break ties across permutations.
for r in range(len(names), 0, -1):
    found_any = False
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            result = compute_schedule(perm)
            if result is None:
                continue
            found_any = True
            m = result["metrics"]
            # Score: prioritize num_meetings, then minimize idle, then travel, then end time
            score = (
                m["num_meetings"] * 1_000_000
                - m["total_idle"] * 1_000
                - m["total_travel"] * 10
                - m["end_time"]
            )
            if best is None or score > best_score:
                best = result
                best_score = score
    if found_any:
        break

# Fallback: no meetings feasible (shouldn't happen here)
output = {"itinerary": []}
if best is not None:
    output["itinerary"] = best["itinerary"]

print(json.dumps(output, ensure_ascii=False))