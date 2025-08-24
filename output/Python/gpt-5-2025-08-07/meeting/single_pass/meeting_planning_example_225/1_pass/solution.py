'SOLUTION:'

import json
from itertools import combinations, permutations

# ---------------------------
# Input parameters
# ---------------------------

# Travel times in minutes (directed)
travel = {
    ("Sunset District", "North Beach"): 29,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Alamo Square"): 16,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Alamo Square"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Union Square"): 14,
}

# Helpers for time conversion
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Starting point and time
start_location = "Sunset District"
start_time = to_minutes("9:00")

# Friends constraints
friends = [
    {
        "name": "Sarah",
        "location": "North Beach",
        "window_start": to_minutes("16:00"),
        "window_end": to_minutes("18:15"),
        "min_duration": 60,
    },
    {
        "name": "Jeffrey",
        "location": "Union Square",
        "window_start": to_minutes("15:00"),
        "window_end": to_minutes("22:00"),
        "min_duration": 75,
    },
    {
        "name": "Brian",
        "location": "Alamo Square",
        "window_start": to_minutes("16:00"),
        "window_end": to_minutes("17:30"),
        "min_duration": 75,
    },
]

# ---------------------------
# Scheduling logic
# ---------------------------

def minimal_forward_schedule(order):
    """
    Build a minimal feasible schedule (meeting each friend for at least the minimum duration),
    given a specific order. Returns list of entries with start/end or None if infeasible.
    """
    entries = []
    time = start_time
    prev_loc = start_location
    for f in order:
        t_travel = travel[(prev_loc, f["location"])]
        arrival = time + t_travel
        start = max(arrival, f["window_start"])
        end = start + f["min_duration"]
        if end > f["window_end"]:
            return None  # infeasible
        entries.append({
            "friend": f,
            "location": f["location"],
            "start": start,
            "end": end
        })
        time = end
        prev_loc = f["location"]
    return entries

def recompute_suffix(entries, start_index):
    """
    Recompute schedule from start_index onward with minimal durations, keeping prior end fixed.
    Returns True if feasible, False otherwise.
    """
    time = entries[start_index - 1]["end"]
    prev_loc = entries[start_index - 1]["location"]
    for i in range(start_index, len(entries)):
        f = entries[i]["friend"]
        t_travel = travel[(prev_loc, f["location"])]
        arrival = time + t_travel
        start = max(arrival, f["window_start"])
        end = start + f["min_duration"]
        if end > f["window_end"]:
            return False
        entries[i]["start"] = start
        entries[i]["end"] = end
        time = end
        prev_loc = f["location"]
    return True

def fill_waiting_and_extend(entries):
    """
    Given a minimal feasible schedule, extend meetings to maximize total meeting time by:
    - Filling waiting gaps between meetings by extending the previous meeting when possible.
    - Extending the last meeting to its window end.
    """
    n = len(entries)
    if n == 0:
        return entries

    # Fill waiting gaps between consecutive meetings
    for i in range(n - 1):
        while True:
            curr = entries[i]
            nxt = entries[i + 1]
            t_travel = travel[(curr["location"], nxt["location"])]
            arrival_next = curr["end"] + t_travel
            earliest_next_start = max(arrival_next, nxt["friend"]["window_start"])
            wait = max(0, earliest_next_start - arrival_next)
            if wait <= 0:
                break
            capacity = curr["friend"]["window_end"] - curr["end"]
            if capacity <= 0:
                break
            extend_by = min(wait, capacity)
            curr["end"] += extend_by
            # Recompute suffix respecting minimal durations
            if not recompute_suffix(entries, i + 1):
                # Shouldn't happen given extend_by <= wait, but guard anyway
                curr["end"] -= extend_by
                break

    # Extend the last meeting to its window end
    last = entries[-1]
    last_capacity = last["friend"]["window_end"] - last["end"]
    if last_capacity > 0:
        last["end"] += last_capacity

    return entries

def evaluate_schedule(entries, order):
    """
    Compute metrics for selection:
    - number of friends met
    - total meeting time
    - finish time
    - total travel time
    """
    if not entries:
        return (0, 0, float('inf'), float('inf'))

    # Compute total meeting minutes
    total_meeting = sum(e["end"] - e["start"] for e in entries)

    # Finish time
    finish = entries[-1]["end"]

    # Total travel time along the path (from start location to first, then between meetings)
    total_travel = 0
    prev_loc = start_location
    for e in entries:
        total_travel += travel[(prev_loc, e["location"])]
        prev_loc = e["location"]

    return (len(entries), total_meeting, finish, total_travel)

def compute_best_itinerary():
    best = None
    best_metrics = None

    # Consider subsets by decreasing size to maximize number of friends first
    for r in range(len(friends), 0, -1):
        found_at_size = False
        for subset in combinations(friends, r):
            for perm in permutations(subset):
                minimal = minimal_forward_schedule(perm)
                if minimal is None:
                    continue
                # Extend schedule
                extended = fill_waiting_and_extend(minimal)
                metrics = evaluate_schedule(extended, perm)

                if best is None or metrics > best_metrics:
                    best = extended
                    best_metrics = metrics
                    found_at_size = True
                elif metrics == best_metrics:
                    # Tie-break on lexicographic person ordering for determinism
                    # Create a comparable key
                    curr_names = [e["friend"]["name"] for e in extended]
                    best_names = [e["friend"]["name"] for e in best]
                    if curr_names < best_names:
                        best = extended
                        best_metrics = metrics
                        found_at_size = True
        if found_at_size:
            break

    # Format result as required JSON
    itinerary = []
    if best:
        for e in best:
            itinerary.append({
                "action": "meet",
                "location": e["location"],
                "person": e["friend"]["name"],
                "start_time": fmt_minutes(e["start"]),
                "end_time": fmt_minutes(e["end"]),
            })

    return {"itinerary": itinerary}

# ---------------------------
# Run and output JSON
# ---------------------------

if __name__ == "__main__":
    result = compute_best_itinerary()
    print(json.dumps(result, ensure_ascii=False))