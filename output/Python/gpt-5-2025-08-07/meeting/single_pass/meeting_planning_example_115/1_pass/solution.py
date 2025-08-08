import json
from itertools import combinations, permutations

# Helper functions for time handling
def time_to_minutes(tstr):
    # tstr like '9:00' or '13:30'
    parts = tstr.split(':')
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables (meeting constraints and travel times)
locations = ["Richmond District", "Pacific Heights", "Marina District"]

travel_minutes = {
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7
}

start_location = "Richmond District"
start_time = time_to_minutes("9:00")

people = [
    {
        "name": "Jessica",
        "location": "Pacific Heights",
        "window_start": time_to_minutes("15:30"),
        "window_end": time_to_minutes("16:45"),
        "min_duration": 45
    },
    {
        "name": "Carol",
        "location": "Marina District",
        "window_start": time_to_minutes("11:30"),
        "window_end": time_to_minutes("15:00"),
        "min_duration": 60
    }
]

def get_travel(a, b):
    return travel_minutes[(a, b)]

# Evaluate a schedule for scoring: primary - number of people met,
# secondary - total meeting time, tertiary - minimize idle time between meetings,
# quaternary - minimize total travel time between meetings, quinary - earliest finish.
def evaluate_schedule(entries):
    people_met = len(entries)
    total_meeting = sum(e['end'] - e['start'] for e in entries)
    if not entries:
        return (-1, -1, 10**9, 10**9, 10**9)  # very poor
    # Compute travel and idle between meetings
    total_travel = 0
    total_idle_between = 0
    for i in range(1, len(entries)):
        prev = entries[i - 1]
        curr = entries[i]
        gap = curr['start'] - prev['end']
        t = get_travel(prev['location'], curr['location'])
        total_travel += t
        idle = gap - t
        if idle < 0:
            # Shouldn't happen if schedule construction respected travel times
            idle = 0
        total_idle_between += idle
    finish_time = entries[-1]['end']
    # Objective tuple (higher is better for first two, lower for others)
    return (
        people_met,
        total_meeting,
        -total_idle_between,    # minimize idle -> maximize negative idle
        -total_travel,          # minimize travel
        -finish_time            # earlier finish preferred
    )

# Search all schedules by exploring non-empty subsets and their permutations,
# and for each, enumerating feasible start/end times (at 1-minute granularity)
best_entries = []
best_score = None

def search_order(order):
    global best_entries, best_score

    # Depth-first search over meeting times for a fixed order
    def dfs(idx, current_loc, current_time, entries):
        nonlocal best_entries, best_score
        if idx == len(order):
            score = evaluate_schedule(entries)
            if (best_score is None) or (score > best_score):
                best_score = score
                best_entries = [dict(e) for e in entries]
            return

        p = order[idx]
        # Travel to this person's location
        arrival = current_time + get_travel(current_loc, p["location"])
        earliest_start = max(arrival, p["window_start"])
        latest_start = p["window_end"] - p["min_duration"]
        if earliest_start > latest_start:
            # Cannot meet this person respecting minimum duration
            return

        # Enumerate feasible start and end times for this meeting segment
        for s in range(earliest_start, latest_start + 1):
            min_end = s + p["min_duration"]
            for e in range(min_end, p["window_end"] + 1):
                # Proceed to next
                new_entry = {
                    "person": p["name"],
                    "location": p["location"],
                    "start": s,
                    "end": e
                }
                dfs(idx + 1, p["location"], e, entries + [new_entry])

    # Launch DFS for this order starting from trip start
    dfs(0, start_location, start_time, [])

# Enumerate all non-empty subsets and their permutations
n = len(people)
for k in range(1, n + 1):
    for combo in combinations(people, k):
        for order in permutations(combo):
            search_order(order)

# Build the output JSON
itinerary = []
for e in best_entries:
    itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": minutes_to_time(e["start"]),
        "end_time": minutes_to_time(e["end"])
    })

result = {"itinerary": itinerary}
print(json.dumps(result, ensure_ascii=False))