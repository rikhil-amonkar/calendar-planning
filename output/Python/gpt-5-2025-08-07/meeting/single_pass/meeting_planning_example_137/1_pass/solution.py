import json
import itertools

# Input parameters (constraints)
start_location = "Financial District"
arrival_time_str = "9:00"

people = {
    "Kenneth": {
        "location": "Chinatown",
        "window_start": "12:00",
        "window_end": "15:00",
        "min_duration_min": 90
    },
    "Barbara": {
        "location": "Golden Gate Park",
        "window_start": "8:15",
        "window_end": "19:00",
        "min_duration_min": 45
    }
}

# Travel times in minutes between locations
travel = {
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Golden Gate Park"): 23,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23
}

# Helper functions
def parse_time(s):
    # format H:MM (possibly 1 or 2 digit hour)
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def ttime(a, b):
    if a == b:
        return 0
    return travel.get((a, b), None)

# Convert windows to minutes for internal use
start_time = parse_time(arrival_time_str)
people_min = {}
for name, info in people.items():
    people_min[name] = {
        "location": info["location"],
        "window_start": parse_time(info["window_start"]),
        "window_end": parse_time(info["window_end"]),
        "min_duration_min": info["min_duration_min"],
        "name": name
    }

def compute_schedule(order):
    # Build minimal feasible schedule first
    current_time = start_time
    current_loc = start_location
    events = []
    # First pass: minimal durations
    for name in order:
        p = people_min[name]
        travel_minutes = ttime(current_loc, p["location"])
        if travel_minutes is None:
            return []  # infeasible, missing travel time
        arrival = current_time + travel_minutes
        start_evt = max(arrival, p["window_start"])
        end_evt = start_evt + p["min_duration_min"]
        if end_evt > p["window_end"]:
            # Can't even meet this person minimally; stop here (partial schedule)
            break
        events.append({
            "person": p["name"],
            "location": p["location"],
            "start": start_evt,
            "end": end_evt,
            "window_start": p["window_start"],
            "window_end": p["window_end"],
            "min_dur": p["min_duration_min"]
        })
        current_time = end_evt
        current_loc = p["location"]

    # If we couldn't schedule the first in order, return empty schedule
    if len(events) == 0:
        return []

    # Stretch events forward where helpful to reduce waiting, while keeping feasibility
    for i in range(len(events) - 1):
        cur = events[i]
        nxt = events[i + 1]

        travel_minutes = ttime(cur["location"], nxt["location"])
        if travel_minutes is None:
            # Missing travel time; treat as infeasible
            return events[:i+1]

        # Compute bounds for extending cur.end
        min_end_cur = cur["start"] + cur["min_dur"]
        max_end_by_own_window = cur["window_end"]
        # Arrival to next must be <= next.window_end - next.min_dur
        max_arrival_to_next = nxt["window_end"] - nxt["min_dur"]
        max_end_cur_by_next = max_arrival_to_next - travel_minutes
        max_end_cur_feasible = min(max_end_by_own_window, max_end_cur_by_next)

        # Target to eliminate waiting at next (arrive exactly at next.window_start)
        target_end_cur = nxt["window_start"] - travel_minutes

        # New end is as late as possible without exceeding target (to avoid waiting),
        # but also within feasible max; at least minimal end.
        desired_end_cur = max(min_end_cur, target_end_cur)
        new_end_cur = min(max_end_cur_feasible, desired_end_cur)
        # Ensure not less than minimal end
        new_end_cur = max(new_end_cur, min_end_cur)

        # If feasibility broken (max_end_cur_feasible < min_end_cur), keep at minimal and hope for the best
        if max_end_cur_feasible < min_end_cur:
            new_end_cur = min_end_cur

        cur["end"] = new_end_cur

        # Update next start/end based on new arrival
        arrival_next = cur["end"] + travel_minutes
        new_start_next = max(arrival_next, nxt["window_start"])
        new_end_next = new_start_next + nxt["min_dur"]

        # Check feasibility for next
        if new_end_next > nxt["window_end"]:
            # Can't fit next; truncate schedule here
            events = events[:i+1]
            break

        # Apply updates to next event
        nxt["start"] = new_start_next
        nxt["end"] = new_end_next

    return events

def score_schedule(events):
    # Primary: number of people met
    num = len(events)
    if num == 0:
        return (0, float('inf'), float('inf'))  # worst finish and wait
    # Finish time: end of last event
    finish = events[-1]["end"]

    # Total waiting time between arrival and actual start
    total_wait = 0
    current_loc = start_location
    current_time = start_time
    for ev in events:
        tr = ttime(current_loc, ev["location"])
        arrival = current_time + tr
        wait = max(0, ev["start"] - arrival)
        total_wait += wait
        current_loc = ev["location"]
        current_time = ev["end"]

    # We maximize num, then prefer earliest finish, then minimal wait
    return (num, finish, total_wait)

# Generate all candidate orders: meet both in all orders, meet singletons, and empty
names = list(people_min.keys())
candidate_orders = []

# All permutations for meeting all people
for r in range(len(names), 0, -1):
    for perm in itertools.permutations(names, r):
        candidate_orders.append(list(perm))

# Include the empty schedule as a fallback
candidate_orders.append([])

best_events = []
best_score = (-1, float('inf'), float('inf'))

for order in candidate_orders:
    if not order:
        events = []
    else:
        events = compute_schedule(order)
    sc = score_schedule(events)
    # Choose best: maximize num; on tie, minimize finish; on tie, minimize wait
    if (sc[0] > best_score[0]) or \
       (sc[0] == best_score[0] and sc[1] < best_score[1]) or \
       (sc[0] == best_score[0] and sc[1] == best_score[1] and sc[2] < best_score[2]):
        best_score = sc
        best_events = events

# Build JSON output
output = {
    "itinerary": []
}

for ev in best_events:
    output["itinerary"].append({
        "action": "meet",
        "location": ev["location"],
        "person": ev["person"],
        "start_time": fmt_time(ev["start"]),
        "end_time": fmt_time(ev["end"])
    })

print(json.dumps(output, ensure_ascii=False))