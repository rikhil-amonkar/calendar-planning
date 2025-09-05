import itertools
import json

def parse_time(tstr):
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Union Square"
start_time_str = "9:00"

# Travel times (directed, in minutes)
travel = {
    "Union Square": {
        "Nob Hill": 9,
        "Haight-Ashbury": 18,
        "Chinatown": 7,
        "Marina District": 18
    },
    "Nob Hill": {
        "Union Square": 7,
        "Haight-Ashbury": 13,
        "Chinatown": 6,
        "Marina District": 11
    },
    "Haight-Ashbury": {
        "Union Square": 17,
        "Nob Hill": 15,
        "Chinatown": 19,
        "Marina District": 17
    },
    "Chinatown": {
        "Union Square": 7,
        "Nob Hill": 8,
        "Haight-Ashbury": 19,
        "Marina District": 12
    },
    "Marina District": {
        "Union Square": 16,
        "Nob Hill": 12,
        "Haight-Ashbury": 16,
        "Chinatown": 16
    }
}

# People constraints
people = {
    "Karen": {
        "location": "Nob Hill",
        "available_start": "21:15",
        "available_end": "21:45",
        "min_duration": 30
    },
    "Joseph": {
        "location": "Haight-Ashbury",
        "available_start": "12:30",
        "available_end": "19:45",
        "min_duration": 90
    },
    "Sandra": {
        "location": "Chinatown",
        "available_start": "7:15",
        "available_end": "19:15",
        "min_duration": 75
    },
    "Nancy": {
        "location": "Marina District",
        "available_start": "11:00",
        "available_end": "20:15",
        "min_duration": 105
    }
}

# Convert time strings to minutes for internal computation
for p in people.values():
    p["avail_start_min"] = parse_time(p["available_start"])
    p["avail_end_min"] = parse_time(p["available_end"])

start_time = parse_time(start_time_str)

def compute_schedule(order):
    """
    Given an ordered tuple/list of person names, compute the earliest-feasible schedule.
    Returns a dict with feasibility, itinerary, total_travel, total_wait, finish_time.
    """
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_wait = 0

    for person_name in order:
        p = people[person_name]
        target_loc = p["location"]
        # Travel time from current_loc to target_loc
        if current_loc not in travel or target_loc not in travel[current_loc]:
            return {"feasible": False}
        t_travel = travel[current_loc][target_loc]
        arrival = current_time + t_travel
        total_travel += t_travel

        # Meeting window constraints
        window_start = p["avail_start_min"]
        window_end = p["avail_end_min"]
        duration = p["min_duration"]
        latest_start = window_end - duration

        # If even the latest start is before arrival, infeasible
        if arrival > latest_start:
            return {"feasible": False}

        # Start at the later of arrival or window start
        meet_start = max(arrival, window_start)
        meet_end = meet_start + duration

        # Waiting time if we arrived early
        wait = max(0, meet_start - arrival)
        total_wait += wait

        # Double-check within window
        if meet_end > window_end:
            return {"feasible": False}

        itinerary.append({
            "action": "meet",
            "location": target_loc,
            "person": person_name,
            "start_time": fmt_time(meet_start),
            "end_time": fmt_time(meet_end)
        })

        # Update state
        current_loc = target_loc
        current_time = meet_end

    return {
        "feasible": True,
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "finish_time": current_time
    }

def better_solution(a, b):
    """
    Return True if solution a is better than b per objectives:
    1) Maximize number of meetings
    2) Minimize total travel time
    3) Minimize total waiting time
    4) Minimize finish time
    """
    if a is None:
        return False
    if b is None:
        return True
    # 1) number of meetings
    if len(a["itinerary"]) != len(b["itinerary"]):
        return len(a["itinerary"]) > len(b["itinerary"])
    # 2) total travel
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    # 3) total waiting
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    # 4) finish time
    return a["finish_time"] < b["finish_time"]

def find_optimal_schedule():
    names = list(people.keys())
    best = None

    # Try subsets in descending size to maximize number of meetings
    for r in range(len(names), 0, -1):
        found_in_this_r = False
        for subset in itertools.combinations(names, r):
            for order in itertools.permutations(subset):
                sol = compute_schedule(order)
                if sol["feasible"]:
                    if best is None or better_solution(sol, best):
                        best = sol
                        found_in_this_r = True
        if found_in_this_r and best is not None and len(best["itinerary"]) == r:
            # Since we iterate r from max to min, once we found at least one feasible
            # solution for this r and we have the best among them, we can stop.
            break

    return best

best_schedule = find_optimal_schedule()

# Ensure output format
output = {"itinerary": best_schedule["itinerary"] if best_schedule else []}
print(json.dumps(output, ensure_ascii=False))