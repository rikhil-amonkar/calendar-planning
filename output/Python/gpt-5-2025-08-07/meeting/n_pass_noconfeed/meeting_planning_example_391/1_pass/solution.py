import itertools
import json

# ---------------------------
# Helper functions
# ---------------------------
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# ---------------------------
# Input variables
# ---------------------------
start_location = "Sunset District"
start_time = to_minutes(9, 0)  # 9:00

# Travel times in minutes (directed)
travel = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,

    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,

    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,

    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,

    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22,
}

def t(from_loc, to_loc):
    return travel[(from_loc, to_loc)]

people = {
    "Kevin": {
        "location": "Alamo Square",
        "window": (to_minutes(8, 15), to_minutes(21, 30)),
        "min_duration": 75
    },
    "Kimberly": {
        "location": "Russian Hill",
        "window": (to_minutes(8, 45), to_minutes(12, 30)),
        "min_duration": 30
    },
    "Joseph": {
        "location": "Presidio",
        "window": (to_minutes(18, 30), to_minutes(19, 15)),
        "min_duration": 45
    },
    "Thomas": {
        "location": "Financial District",
        "window": (to_minutes(19, 0), to_minutes(21, 45)),
        "min_duration": 45
    },
}

# ---------------------------
# Scheduling logic
# ---------------------------
def try_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_wait = 0
    total_travel = 0

    for person in order:
        info = people[person]
        loc = info["location"]
        w_start, w_end = info["window"]
        dur = info["min_duration"]

        travel_time = t(current_loc, loc)
        total_travel += travel_time
        arrival = current_time + travel_time

        start = max(arrival, w_start)
        end = start + dur

        if end > w_end:
            return None  # infeasible

        wait = max(0, start - arrival)
        total_wait += wait

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })

        current_loc = loc
        current_time = end

    return {
        "itinerary": itinerary,
        "meta": {
            "count": len(order),
            "total_wait": total_wait,
            "total_travel": total_travel,
            "end_time": current_time
        }
    }

def find_best_schedule():
    names = list(people.keys())
    n = len(names)
    best = None

    # Optimize primary: maximize number of people met
    # Secondary: minimize total waiting time
    # Tertiary: minimize end time, then minimize total travel
    for k in range(n, 0, -1):
        candidates = []
        for subset in itertools.combinations(names, k):
            for order in itertools.permutations(subset):
                plan = try_schedule(order)
                if plan is not None:
                    candidates.append(plan)
        if candidates:
            best = min(
                candidates,
                key=lambda x: (x["meta"]["total_wait"], x["meta"]["end_time"], x["meta"]["total_travel"])
            )
            break
    return best

# ---------------------------
# Compute and output result
# ---------------------------
best_schedule = find_best_schedule()
output = {"itinerary": best_schedule["itinerary"] if best_schedule else []}
print(json.dumps(output, ensure_ascii=False, indent=2))