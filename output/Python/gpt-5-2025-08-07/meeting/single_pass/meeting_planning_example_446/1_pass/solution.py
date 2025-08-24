"SOLUTION:"
import json
from itertools import permutations, combinations

# -----------------------------
# Input parameters
# -----------------------------

start_location = "Richmond District"
start_time_str = "9:00"

# Travel times in minutes (directed)
travel = {
    "Richmond District": {
        "Marina District": 9,
        "Chinatown": 20,
        "Financial District": 22,
        "Bayview": 26,
        "Union Square": 21,
    },
    "Marina District": {
        "Richmond District": 11,
        "Chinatown": 16,
        "Financial District": 17,
        "Bayview": 27,
        "Union Square": 16,
    },
    "Chinatown": {
        "Richmond District": 20,
        "Marina District": 12,
        "Financial District": 5,
        "Bayview": 22,
        "Union Square": 7,
    },
    "Financial District": {
        "Richmond District": 21,
        "Marina District": 15,
        "Chinatown": 5,
        "Bayview": 19,
        "Union Square": 9,
    },
    "Bayview": {
        "Richmond District": 25,
        "Marina District": 25,
        "Chinatown": 18,
        "Financial District": 19,
        "Union Square": 17,
    },
    "Union Square": {
        "Richmond District": 20,
        "Marina District": 18,
        "Chinatown": 7,
        "Financial District": 9,
        "Bayview": 15,
    },
}

people = [
    {
        "name": "Kimberly",
        "location": "Marina District",
        "window_start": "13:15",
        "window_end": "16:45",
        "min_duration": 15,
    },
    {
        "name": "Robert",
        "location": "Chinatown",
        "window_start": "12:15",
        "window_end": "20:15",
        "min_duration": 15,
    },
    {
        "name": "Rebecca",
        "location": "Financial District",
        "window_start": "13:15",
        "window_end": "16:45",
        "min_duration": 75,
    },
    {
        "name": "Margaret",
        "location": "Bayview",
        "window_start": "9:30",
        "window_end": "13:30",
        "min_duration": 30,
    },
    {
        "name": "Kenneth",
        "location": "Union Square",
        "window_start": "19:30",
        "window_end": "21:15",
        "min_duration": 75,
    },
]

# -----------------------------
# Utilities
# -----------------------------

def parse_time(hhmm: str) -> int:
    """Parse 'H:MM' (24h) to minutes since midnight."""
    hh, mm = hhmm.split(":")
    return int(hh) * 60 + int(mm)

def fmt_time(minutes: int) -> str:
    """Format minutes since midnight to 'H:MM' (no leading zero on hour)."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# -----------------------------
# Preprocess people time windows
# -----------------------------

for p in people:
    p["start_min"] = parse_time(p["window_start"])
    p["end_min"] = parse_time(p["window_end"])

start_time_min = parse_time(start_time_str)

# -----------------------------
# Scheduling logic
# -----------------------------

def simulate_order(order):
    """
    Given an ordered list of people dicts, schedule each meeting at the earliest feasible time,
    accounting for travel and availability windows. Returns (feasible, itinerary, stats)
    where stats include finish_time, total_travel, total_wait.
    """
    current_loc = start_location
    current_time = start_time_min
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        loc = person["location"]
        # Travel time between current_loc and loc
        if current_loc == loc:
            ttime = 0
        else:
            if current_loc not in travel or loc not in travel[current_loc]:
                return False, [], {}
            ttime = travel[current_loc][loc]

        arrival_time = current_time + ttime
        # Earliest possible start time within window
        start = max(arrival_time, person["start_min"])
        end = start + person["min_duration"]

        # Check feasibility within window
        if end > person["end_min"]:
            return False, [], {}

        # Accumulate stats
        total_travel += ttime
        wait = max(0, start - arrival_time)
        total_wait += wait

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
        })

        # Update state
        current_loc = loc
        current_time = end

    finish_time = current_time
    stats = {
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
    }
    return True, itinerary, stats

def choose_best_schedule(people):
    """
    Explore all subsets and permutations to maximize:
    1) number of friends met
    2) earliest finish time
    3) minimal total waiting time
    4) minimal total travel time
    """
    best = None  # (count, finish_time, total_wait, total_travel, itinerary)

    n = len(people)
    # Try larger subsets first to maximize count
    for k in range(n, 0, -1):
        any_feasible_for_k = False
        for subset in combinations(people, k):
            for order in permutations(subset):
                feasible, itinerary, stats = simulate_order(order)
                if not feasible:
                    continue
                any_feasible_for_k = True

                score = (
                    k,
                    stats["finish_time"],
                    stats["total_wait"],
                    stats["total_travel"],
                )
                if best is None:
                    best = (score, itinerary)
                else:
                    # Comparison: maximize count -> minimize finish_time/wait/travel
                    # We invert by comparing tuples with appropriate signs
                    prev_score = best[0]
                    # Compare count (higher better)
                    if score[0] > prev_score[0]:
                        best = (score, itinerary)
                    elif score[0] == prev_score[0]:
                        # Earlier finish better
                        if score[1] < prev_score[1]:
                            best = (score, itinerary)
                        elif score[1] == prev_score[1]:
                            # Less waiting better
                            if score[2] < prev_score[2]:
                                best = (score, itinerary)
                            elif score[2] == prev_score[2]:
                                # Less travel better
                                if score[3] < prev_score[3]:
                                    best = (score, itinerary)
        if any_feasible_for_k:
            # We found at least one schedule of size k. Since we iterate k from n down,
            # k is maximal; we keep scanning to break ties among size-k schedules only.
            # After finishing all size-k subsets, stop.
            break

    if best is None:
        return []
    return best[1]

# -----------------------------
# Compute and output result
# -----------------------------

best_itinerary = choose_best_schedule(people)
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))