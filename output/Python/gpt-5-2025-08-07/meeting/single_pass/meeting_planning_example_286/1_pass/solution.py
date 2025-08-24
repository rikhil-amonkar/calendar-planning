"SOLUTION:"

import itertools
import json

# Input variables
start_location = "Union Square"
start_time_str = "9:00"

people = [
    {
        "name": "Rebecca",
        "location": "Mission District",
        "window_start": "11:30",
        "window_end": "20:15",
        "min_minutes": 120,
    },
    {
        "name": "Karen",
        "location": "Bayview",
        "window_start": "12:45",
        "window_end": "15:00",
        "min_minutes": 120,
    },
    {
        "name": "Carol",
        "location": "Sunset District",
        "window_start": "10:15",
        "window_end": "11:45",
        "min_minutes": 30,
    },
]

# Travel times in minutes (asymmetric)
travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Sunset District"): 26,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Sunset District"): 24,
    ("Bayview", "Union Square"): 17,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Sunset District"): 23,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Bayview"): 22,
}

# Utilities
def parse_time(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def get_travel(a, b):
    if a == b:
        return 0
    return travel_times[(a, b)]

# Prepare people with parsed times
people_data = []
for p in people:
    people_data.append({
        "name": p["name"],
        "location": p["location"],
        "start": parse_time(p["window_start"]),
        "end": parse_time(p["window_end"]),
        "min": int(p["min_minutes"]),
    })

start_time = parse_time(start_time_str)

def schedule_order(order, extend_last_to_window_end=True):
    current_loc = start_location
    current_time = start_time
    itinerary = []

    for idx, person in enumerate(order):
        # Travel to person's location
        travel = get_travel(current_loc, person["location"])
        earliest_arrival = current_time + travel

        # Start time: not before arrival and not before window opens
        start_meet = max(earliest_arrival, person["start"])

        latest_start_allowed = person["end"] - person["min"]
        if start_meet > latest_start_allowed:
            return None  # infeasible

        min_end = start_meet + person["min"]

        if idx < len(order) - 1:
            next_person = order[idx + 1]
            travel_to_next = get_travel(person["location"], next_person["location"])
            latest_depart_to_meet_next = (next_person["end"] - next_person["min"]) - travel_to_next

            # If even with minimal meeting we cannot reach next in time, infeasible
            if min_end > latest_depart_to_meet_next:
                return None

            # Try to align arrival at next's window start to minimize waiting
            target_depart = next_person["start"] - travel_to_next
            depart_max = min(person["end"], latest_depart_to_meet_next)
            depart = max(min(target_depart, depart_max), min_end)
            end_meet = depart
        else:
            # Last meeting: optionally extend to window end to maximize meeting time
            end_meet = person["end"] if extend_last_to_window_end else min_end

        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
            "_start": start_meet,
            "_end": end_meet,
            "_loc": person["location"],
        })

        # Advance
        current_time = end_meet
        current_loc = person["location"]

    return itinerary

def evaluate_itinerary(itin):
    if not itin:
        return (0, 0, 0, 0, 0)  # score tuple plus helper totals

    # Number of people met
    n = len(itin)

    # Total meeting time
    total_meet = sum(item["_end"] - item["_start"] for item in itin)

    # Compute total travel and waiting time
    cur_loc = start_location
    cur_time = start_time
    total_travel = 0
    total_wait = 0
    for item in itin:
        travel = get_travel(cur_loc, item["_loc"])
        arrival = cur_time + travel
        wait = max(0, item["_start"] - arrival)
        total_travel += travel
        total_wait += wait
        cur_loc = item["_loc"]
        cur_time = item["_end"]

    finish_time = itin[-1]["_end"]

    # Score: prioritize more people, more meeting time, less wait, earlier finish, less travel
    score = (n, total_meet, -total_wait, -finish_time, -total_travel)
    return score

# Explore schedules across all subsets and permutations
best_score = None
best_itinerary = []

# Generate all non-empty subsets
for r in range(len(people_data), 0, -1):
    any_found_this_size = False
    for subset in itertools.combinations(people_data, r):
        for order in itertools.permutations(subset):
            itin = schedule_order(order, extend_last_to_window_end=True)
            if itin is None:
                continue
            score = evaluate_itinerary(itin)
            if (best_score is None) or (score > best_score):
                best_score = score
                best_itinerary = itin
                any_found_this_size = True
    # If we found at least one schedule using r people, no need to consider smaller subsets
    if any_found_this_size:
        break

# Prepare output: strip internal keys
output_itinerary = []
for item in best_itinerary:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": item["start_time"],
        "end_time": item["end_time"],
    })

result = {
    "itinerary": output_itinerary
}

print(json.dumps(result, ensure_ascii=False))