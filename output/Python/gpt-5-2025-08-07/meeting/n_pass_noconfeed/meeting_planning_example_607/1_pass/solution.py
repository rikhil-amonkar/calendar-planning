import itertools
import json

# Time utilities
def to_minutes(tstr):
    # tstr like '9:00' or '13:30'
    h, m = tstr.split(':')
    return int(h) * 60 + int(m)

def to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
start_location = "Sunset District"
start_time_str = "9:00"
start_time = to_minutes(start_time_str)

# Travel times (minutes), directional as provided
travel = {
    "Sunset District": {
        "Russian Hill": 24,
        "The Castro": 17,
        "Richmond District": 12,
        "Marina District": 21,
        "North Beach": 29,
        "Union Square": 30,
        "Golden Gate Park": 11,
    },
    "Russian Hill": {
        "Sunset District": 23,
        "The Castro": 21,
        "Richmond District": 14,
        "Marina District": 7,
        "North Beach": 5,
        "Union Square": 11,
        "Golden Gate Park": 21,
    },
    "The Castro": {
        "Sunset District": 17,
        "Russian Hill": 18,
        "Richmond District": 16,
        "Marina District": 21,
        "North Beach": 20,
        "Union Square": 19,
        "Golden Gate Park": 11,
    },
    "Richmond District": {
        "Sunset District": 11,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "North Beach": 17,
        "Union Square": 21,
        "Golden Gate Park": 9,
    },
    "Marina District": {
        "Sunset District": 19,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "North Beach": 11,
        "Union Square": 16,
        "Golden Gate Park": 18,
    },
    "North Beach": {
        "Sunset District": 27,
        "Russian Hill": 4,
        "The Castro": 22,
        "Richmond District": 18,
        "Marina District": 9,
        "Union Square": 7,
        "Golden Gate Park": 22,
    },
    "Union Square": {
        "Sunset District": 26,
        "Russian Hill": 13,
        "The Castro": 19,
        "Richmond District": 20,
        "Marina District": 18,
        "North Beach": 10,
        "Golden Gate Park": 22,
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Russian Hill": 19,
        "The Castro": 13,
        "Richmond District": 7,
        "Marina District": 16,
        "North Beach": 24,
        "Union Square": 22,
    },
}

# Friends constraints
friends = {
    "Karen": {
        "location": "Russian Hill",
        "window_start": to_minutes("20:45"),
        "window_end": to_minutes("21:45"),
        "min_duration": 60,
    },
    "Jessica": {
        "location": "The Castro",
        "window_start": to_minutes("15:45"),
        "window_end": to_minutes("19:30"),
        "min_duration": 60,
    },
    "Matthew": {
        "location": "Richmond District",
        "window_start": to_minutes("7:30"),
        "window_end": to_minutes("15:15"),
        "min_duration": 15,
    },
    "Michelle": {
        "location": "Marina District",
        "window_start": to_minutes("10:30"),
        "window_end": to_minutes("18:45"),
        "min_duration": 75,
    },
    "Carol": {
        "location": "North Beach",
        "window_start": to_minutes("12:00"),
        "window_end": to_minutes("17:00"),
        "min_duration": 90,
    },
    "Stephanie": {
        "location": "Union Square",
        "window_start": to_minutes("10:45"),
        "window_end": to_minutes("14:15"),
        "min_duration": 30,
    },
    "Linda": {
        "location": "Golden Gate Park",
        "window_start": to_minutes("10:45"),
        "window_end": to_minutes("22:00"),
        "min_duration": 90,
    },
}

people = list(friends.keys())

def simulate(order):
    current_time = start_time
    current_loc = start_location
    schedule = []
    total_wait = 0
    total_travel = 0

    for person in order:
        loc = friends[person]["location"]
        # If no direct travel time is provided (shouldn't happen), skip
        if current_loc == loc:
            travel_time = 0
        else:
            if current_loc not in travel or loc not in travel[current_loc]:
                # No path defined, skip this person
                continue
            travel_time = travel[current_loc][loc]
        arrive_time = current_time + travel_time
        start_window = friends[person]["window_start"]
        end_window = friends[person]["window_end"]
        dur = friends[person]["min_duration"]

        # Earliest possible start respecting travel and window
        start_meet = max(arrive_time, start_window)
        end_meet = start_meet + dur

        if end_meet <= end_window:
            # Feasible meeting
            wait = max(0, start_meet - arrive_time)
            total_wait += wait
            total_travel += travel_time
            schedule.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time_min": start_meet,
                "end_time_min": end_meet,
            })
            current_time = end_meet
            current_loc = loc
        else:
            # Not feasible in this order at this point, skip
            continue

    return schedule, total_wait, total_travel, current_time

# Evaluate all permutations to maximize number of meetings; tie-break by minimal wait, then minimal travel, then earliest end time
best_schedule = []
best_metrics = None  # (num_meetings, total_wait, total_travel, end_time)
for order in itertools.permutations(people):
    schedule, wait, travel_time, end_time = simulate(order)
    num_meetings = len(schedule)
    metrics = (num_meetings, -wait, -travel_time, -end_time)  # maximize meetings; then prefer less wait/travel/earlier end
    if best_metrics is None or metrics > best_metrics:
        best_metrics = metrics
        best_schedule = schedule

# Build JSON-friendly itinerary
itinerary = []
for e in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": to_str(e["start_time_min"]),
        "end_time": to_str(e["end_time_min"]),
    })

output = {"itinerary": itinerary}
print(json.dumps(output, ensure_ascii=False))