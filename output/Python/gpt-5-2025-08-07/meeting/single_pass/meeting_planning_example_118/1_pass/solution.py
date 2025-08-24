import json
from itertools import combinations, permutations
from typing import List, Dict, Tuple

# -----------------------------
# Utility functions for time handling
# -----------------------------
def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# -----------------------------
# Input parameters (can be edited)
# -----------------------------
start_location = "Bayview"
start_time_str = "9:00"

travel_minutes = {
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Presidio"): 31,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Presidio"): 24,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Union Square"): 22,
}

participants = [
    {
        "name": "Richard",
        "location": "Union Square",
        "available_start": "8:45",
        "available_end": "13:00",
        "min_meet": 120,
    },
    {
        "name": "Charles",
        "location": "Presidio",
        "available_start": "9:45",
        "available_end": "13:00",
        "min_meet": 120,
    },
]

# -----------------------------
# Preprocess inputs
# -----------------------------
start_time = time_to_minutes(start_time_str)
for p in participants:
    p["avail_start_min"] = time_to_minutes(p["available_start"])
    p["avail_end_min"] = time_to_minutes(p["available_end"])

# -----------------------------
# Scheduling logic
# -----------------------------
def travel_time(a: str, b: str) -> int:
    if a == b:
        return 0
    return travel_minutes.get((a, b), float('inf'))

def feasible_and_optimal_schedule(order: List[Dict]) -> Tuple[bool, List[Dict], int]:
    """
    Given an ordered list of participants, determine if it's feasible to meet each
    for at least their minimum durations starting from the start state, and if so,
    compute the meeting times that maximize total meeting minutes (while preserving feasibility).
    Returns: (feasible, itinerary_list, total_meeting_minutes)
    """
    m = len(order)
    if m == 0:
        return True, [], 0

    # Backward pass to compute latest feasible start times to satisfy minima
    Lstart = [0] * m  # latest start time for meeting i to still satisfy downstream minima
    Lstart[m - 1] = order[m - 1]["avail_end_min"] - order[m - 1]["min_meet"]
    for i in range(m - 2, -1, -1):
        t_travel = travel_time(order[i]["location"], order[i + 1]["location"])
        Lstart[i] = min(order[i]["avail_end_min"] - order[i]["min_meet"], Lstart[i + 1] - t_travel - order[i]["min_meet"])

    # Forward pass to build the schedule and extend meetings maximally
    itinerary = []
    current_time = start_time
    current_loc = start_location
    total_meeting = 0

    for i, person in enumerate(order):
        # travel to person's location
        t_travel = travel_time(current_loc, person["location"])
        if t_travel == float('inf'):
            return False, [], 0
        arrival = current_time + t_travel

        # meeting start cannot be before availability, and cannot be after Lstart[i]
        start_meet = max(arrival, person["avail_start_min"])
        if start_meet > Lstart[i]:
            return False, [], 0

        # determine latest end we can push to (to maximize total meeting time)
        if i == m - 1:
            latest_end_allowed = person["avail_end_min"]
        else:
            # must depart in time to reach next person's latest start
            next_loc = order[i + 1]["location"]
            latest_end_allowed = min(person["avail_end_min"], Lstart[i + 1] - travel_time(person["location"], next_loc))

        # must at least meet the minimum duration
        min_end = start_meet + person["min_meet"]
        if min_end > latest_end_allowed:
            return False, [], 0

        end_meet = latest_end_allowed  # extend maximally

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(end_meet),
        })

        total_meeting += (end_meet - start_meet)
        current_time = end_meet
        current_loc = person["location"]

    return True, itinerary, total_meeting

def optimize_schedule(participants: List[Dict]) -> List[Dict]:
    n = len(participants)
    best_itinerary = []
    best_score = (-1, -1)  # (num_people_met, total_meeting_minutes)
    # Consider subsets of decreasing size to prioritize meeting as many friends as possible
    for k in range(n, -1, -1):
        found_for_k = []
        for subset in combinations(participants, k):
            for order in permutations(subset):
                feasible, itinerary, total_meeting = feasible_and_optimal_schedule(list(order))
                if feasible:
                    found_for_k.append((itinerary, total_meeting))
        if found_for_k:
            # Choose the itinerary with maximum total meeting time as tie-breaker
            found_for_k.sort(key=lambda x: (len(x[0]), x[1]), reverse=True)
            best_itinerary, best_total = found_for_k[0]
            best_score = (len(best_itinerary), best_total)
            break
    return best_itinerary

# -----------------------------
# Compute and output result
# -----------------------------
itinerary = optimize_schedule(participants)
result = {"itinerary": itinerary}
print(json.dumps(result, ensure_ascii=False))