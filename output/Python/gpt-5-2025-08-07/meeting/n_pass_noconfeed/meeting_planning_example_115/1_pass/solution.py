# SOLUTION:
import json
from itertools import permutations

# Helper functions
def to_minutes(tstr):
    h, m = tstr.split(":")
    return int(h) * 60 + int(m)

def to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Richmond District"
arrival_time_str = "9:00"

travel_times = {
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7,
}

people = [
    {
        "name": "Jessica",
        "location": "Pacific Heights",
        "availability_start": "15:30",
        "availability_end": "16:45",
        "min_duration": 45,
    },
    {
        "name": "Carol",
        "location": "Marina District",
        "availability_start": "11:30",
        "availability_end": "15:00",
        "min_duration": 60,
    },
]

# Convert time strings to minutes
arrival_time = to_minutes(arrival_time_str)
for p in people:
    p["start"] = to_minutes(p["availability_start"])
    p["end"] = to_minutes(p["availability_end"])

def get_travel(a, b):
    return travel_times[(a, b)]

# Search for optimal schedule
best_score = None
best_plan = None

def evaluate_plan(selected):
    if not selected:
        return
    # Calculate total waiting time (before first and between meetings)
    pre_travel = get_travel(start_location, selected[0]["location"])
    pre_wait = max(0, selected[0]["start"] - (arrival_time + pre_travel))
    between_wait = 0
    for i in range(len(selected) - 1):
        cur_end = selected[i]["end"]
        cur_loc = selected[i]["location"]
        next_start = selected[i + 1]["start"]
        next_loc = selected[i + 1]["location"]
        tt = get_travel(cur_loc, next_loc)
        between_wait += max(0, next_start - (cur_end + tt))
    total_wait = pre_wait + between_wait

    meet_count = len(selected)
    total_meeting = sum(item["end"] - item["start"] for item in selected)
    end_time = selected[-1]["end"]

    # Objective: maximize (meet_count, total_meeting), then minimize (total_wait, end_time)
    score = (meet_count, total_meeting, -total_wait, -end_time)
    global best_score, best_plan
    if best_score is None or score > best_score:
        best_score = score
        best_plan = selected

def search(order, idx, prev_loc, prev_end_time, chosen):
    if idx == len(order):
        # Evaluate the current plan
        # Ensure meetings are in chronological order
        chosen_sorted = sorted(chosen, key=lambda x: x["start"])
        evaluate_plan(chosen_sorted)
        return

    person = order[idx]
    loc = person["location"]
    min_dur = person["min_duration"]
    avail_start = person["start"]
    avail_end = person["end"]

    # Determine earliest possible start time for this meeting
    if idx == 0:
        earliest_possible_arrival = arrival_time + get_travel(start_location, loc)
    else:
        earliest_possible_arrival = prev_end_time + get_travel(prev_loc, loc)

    s_min = max(avail_start, earliest_possible_arrival)
    s_max = avail_end - min_dur
    if s_min > s_max:
        # Cannot schedule this person at all with current prefix; still evaluate if at least one chosen
        if chosen:
            chosen_sorted = sorted(chosen, key=lambda x: x["start"])
            evaluate_plan(chosen_sorted)
        return

    # Enumerate all feasible starts and durations for this person
    for s in range(s_min, s_max + 1):
        max_dur = avail_end - s
        for d in range(min_dur, max_dur + 1):
            e = s + d
            # Prune if next person (if any) cannot be met afterwards
            if idx < len(order) - 1:
                nxt = order[idx + 1]
                travel_to_next = get_travel(loc, nxt["location"])
                earliest_next_start = max(nxt["start"], e + travel_to_next)
                if earliest_next_start > nxt["end"] - nxt["min_duration"]:
                    continue  # Next cannot be satisfied; prune
            chosen.append({
                "action": "meet",
                "location": loc,
                "person": person["name"],
                "start": s,
                "end": e
            })
            search(order, idx + 1, loc, e, chosen)
            chosen.pop()

def plan():
    # Try meeting both friends (all permutations), then fall back to single meetings if needed
    orders_to_try = []
    for r in [2, 1]:
        for order in permutations(people, r):
            orders_to_try.append(order)

    for order in orders_to_try:
        search(order, 0, None, arrival_time, [])

    # Build output
    itinerary = []
    if best_plan:
        # Sort chronologically
        best_sorted = sorted(best_plan, key=lambda x: x["start"])
        for item in best_sorted:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": to_timestr(item["start"]),
                "end_time": to_timestr(item["end"]),
            })
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan()
    print(json.dumps(result, ensure_ascii=False))