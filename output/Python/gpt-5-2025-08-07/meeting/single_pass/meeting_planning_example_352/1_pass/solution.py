import json
from itertools import permutations, combinations

# ---------- Helper functions ----------
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# ---------- Input data (constraints and travel times) ----------
start_location = "Union Square"
start_time = to_minutes(9, 0)  # 9:00 AM

# Directed travel times in minutes between neighborhoods
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

# Friends' availability windows and minimum meeting durations
friends = [
    {
        "name": "Karen",
        "location": "Nob Hill",
        "window_start": to_minutes(21, 15),
        "window_end": to_minutes(21, 45),
        "min_duration": 30
    },
    {
        "name": "Joseph",
        "location": "Haight-Ashbury",
        "window_start": to_minutes(12, 30),
        "window_end": to_minutes(19, 45),
        "min_duration": 90
    },
    {
        "name": "Sandra",
        "location": "Chinatown",
        "window_start": to_minutes(7, 15),
        "window_end": to_minutes(19, 15),
        "min_duration": 75
    },
    {
        "name": "Nancy",
        "location": "Marina District",
        "window_start": to_minutes(11, 0),
        "window_end": to_minutes(20, 15),
        "min_duration": 105
    }
]

# Map friend names to their data for quick lookup (optional)
friend_by_name = {f["name"]: f for f in friends}

# ---------- Scheduling logic ----------
def simulate_schedule(order):
    """
    Simulate meeting the given ordered list of friend dicts.
    Returns:
      - itinerary: list of meeting entries
      - feasible: bool
      - end_time: int minutes
      - total_travel: int minutes
      - total_wait: int minutes
    """
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for f in order:
        # Travel to friend's location
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            return None  # No travel path defined
        t_travel = travel[current_loc][f["location"]]
        arrival = current_time + t_travel
        total_travel += t_travel

        # Wait until their window starts if we arrive early
        start_meet = max(arrival, f["window_start"])
        wait = max(0, start_meet - arrival)
        total_wait += wait

        # End of meeting
        end_meet = start_meet + f["min_duration"]

        # Check feasibility within their availability window
        if end_meet > f["window_end"]:
            return None

        # Record meeting
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet)
        })

        # Update state
        current_loc = f["location"]
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "feasible": True,
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

# Generate all possible schedules considering all subsets and permutations
best_plan = None
best_score = None  # We'll maximize this tuple

# Objective: maximize number of friends met. Tie-breakers: minimize total travel, then minimize total waiting, then earliest finish time
friend_list = friends[:]
n = len(friend_list)

for r in range(n, 0, -1):  # larger subsets first; we still evaluate all but prefer larger
    for subset in combinations(friend_list, r):
        # To reduce search, we can leave it general; permutations covers all orders
        for order in permutations(subset):
            result = simulate_schedule(order)
            if result is None:
                continue
            # Score: (num_met, -total_travel, -total_wait, -end_time)
            score = (len(order), -result["total_travel"], -result["total_wait"], -result["end_time"])
            if best_score is None or score > best_score:
                best_score = score
                best_plan = result

# If no feasible plan found, return empty itinerary
output = {"itinerary": []}
if best_plan is not None:
    output["itinerary"] = best_plan["itinerary"]

print(json.dumps(output))