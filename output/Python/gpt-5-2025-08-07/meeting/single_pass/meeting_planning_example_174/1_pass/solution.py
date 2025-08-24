import json
from itertools import permutations
from typing import Dict, Tuple, List

# ----------------------------
# Input parameters (variables)
# ----------------------------

# Locations
NOB_HILL = "Nob Hill"
PACIFIC_HEIGHTS = "Pacific Heights"
MISSION_DISTRICT = "Mission District"

# Travel times in minutes (directed)
travel_minutes: Dict[Tuple[str, str], int] = {
    (NOB_HILL, PACIFIC_HEIGHTS): 8,
    (NOB_HILL, MISSION_DISTRICT): 13,
    (PACIFIC_HEIGHTS, NOB_HILL): 8,
    (PACIFIC_HEIGHTS, MISSION_DISTRICT): 15,
    (MISSION_DISTRICT, NOB_HILL): 12,
    (MISSION_DISTRICT, PACIFIC_HEIGHTS): 16,
}

# Start conditions
start_location = NOB_HILL
start_time_str = "9:00"

# Friends and their constraints
friends = [
    {
        "name": "Thomas",
        "location": PACIFIC_HEIGHTS,
        "window_start": "15:30",
        "window_end": "19:15",
        "min_minutes": 75,
    },
    {
        "name": "Kenneth",
        "location": MISSION_DISTRICT,
        "window_start": "12:00",
        "window_end": "15:45",
        "min_minutes": 45,
    },
]

# ----------------------------
# Utility functions
# ----------------------------

def parse_time(t: str) -> int:
    """Convert 'H:MM' or 'HH:MM' to minutes since midnight."""
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    """Format minutes since midnight to 'H:MM' (24-hour, no leading zero in hour)."""
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel(a: str, b: str) -> int:
    if a == b:
        return 0
    return travel_minutes[(a, b)]

# ----------------------------
# Scheduling engine
# ----------------------------

def feasible_meeting(current_time: int, current_loc: str, person: dict):
    """
    Determine if we can meet person for at least min_minutes.
    Returns (is_feasible, depart_time, start_time, end_time, arrival_time, travel_time, wait_time)
    depart_time chosen to minimize waiting while feasible.
    """
    ws = parse_time(person["window_start"])
    we = parse_time(person["window_end"])
    d_min = person["min_minutes"]
    latest_start = we - d_min
    t_travel = get_travel(current_loc, person["location"])

    # Feasible if we can arrive by latest_start
    if current_time + t_travel > latest_start:
        return (False, None, None, None, None, t_travel, None)

    # Choose a departure time that avoids unnecessary waiting:
    # - Cannot depart before current_time
    # - Prefer to arrive at or just before ws
    ideal_depart = ws - t_travel
    depart_time = max(current_time, ideal_depart)

    arrival_time = depart_time + t_travel
    start_time = max(arrival_time, ws)
    if start_time > latest_start:
        # If arriving too close to the deadline, try departing immediately (earliest possible)
        arrival_time = current_time + t_travel
        start_time = max(arrival_time, ws)
        if start_time > latest_start:
            return (False, None, None, None, None, t_travel, None)
        depart_time = current_time

    end_time = start_time + d_min
    wait_time = max(0, start_time - arrival_time)
    return (True, depart_time, start_time, end_time, arrival_time, t_travel, wait_time)

def evaluate_sequence(sequence: List[dict], start_loc: str, start_time: int):
    """
    Evaluate a meeting sequence, returning an itinerary and objective metrics.
    Metrics:
      - num_met (maximize)
      - finish_time (minimize)
      - total_travel (minimize)
      - total_wait (minimize)
    """
    current_loc = start_loc
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    met_count = 0

    for person in sequence:
        ok, depart_time, start_time_m, end_time_m, arrival_time, t_travel, wait_time = feasible_meeting(
            current_time, current_loc, person
        )
        if not ok:
            # Infeasible to continue this sequence fully; stop here.
            break

        # Update metrics and state
        total_travel += t_travel
        total_wait += wait_time
        met_count += 1
        current_time = end_time_m
        current_loc = person["location"]

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": fmt_time(start_time_m),
            "end_time": fmt_time(end_time_m),
        })

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "num_met": met_count,
        "finish_time": finish_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
    }

def all_sequences(items: List[dict]) -> List[List[dict]]:
    """Generate all ordered subsets (including empty)."""
    seqs = []
    n = len(items)
    for k in range(n + 1):
        for perm in permutations(items, k):
            seqs.append(list(perm))
    return seqs

# ----------------------------
# Compute optimal schedule
# ----------------------------

def main():
    start_time = parse_time(start_time_str)

    sequences = all_sequences(friends)
    evaluated = []
    for seq in sequences:
        evaluated.append(evaluate_sequence(seq, start_location, start_time))

    # Choose best according to objectives:
    # - maximize num_met
    # - minimize finish_time
    # - minimize total_travel
    # - minimize total_wait
    best = min(
        evaluated,
        key=lambda e: (
            -e["num_met"],
            e["finish_time"],
            e["total_travel"],
            e["total_wait"],
        ),
    )

    # Output only the itinerary in required JSON structure
    output = {
        "itinerary": best["itinerary"]
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()