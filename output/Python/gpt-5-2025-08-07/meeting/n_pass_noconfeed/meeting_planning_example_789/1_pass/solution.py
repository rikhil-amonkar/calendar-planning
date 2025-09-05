# SOLUTION:
import itertools
import json

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables

start_location = "Union Square"
start_time_str = "9:00"

# Directed travel times (in minutes)
dist = {
    "Union Square": {
        "Russian Hill": 13, "Alamo Square": 15, "Haight-Ashbury": 18, "Marina District": 18,
        "Bayview": 15, "Chinatown": 7, "Presidio": 24, "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10, "Alamo Square": 15, "Haight-Ashbury": 17, "Marina District": 7,
        "Bayview": 23, "Chinatown": 9, "Presidio": 14, "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14, "Russian Hill": 13, "Haight-Ashbury": 5, "Marina District": 15,
        "Bayview": 16, "Chinatown": 15, "Presidio": 17, "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19, "Russian Hill": 17, "Alamo Square": 5, "Marina District": 17,
        "Bayview": 18, "Chinatown": 19, "Presidio": 15, "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16, "Russian Hill": 8, "Alamo Square": 15, "Haight-Ashbury": 16,
        "Bayview": 27, "Chinatown": 15, "Presidio": 10, "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18, "Russian Hill": 23, "Alamo Square": 16, "Haight-Ashbury": 19,
        "Marina District": 27, "Chinatown": 19, "Presidio": 32, "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7, "Russian Hill": 7, "Alamo Square": 17, "Haight-Ashbury": 19,
        "Marina District": 12, "Bayview": 20, "Presidio": 19, "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22, "Russian Hill": 14, "Alamo Square": 19, "Haight-Ashbury": 15,
        "Marina District": 11, "Bayview": 31, "Chinatown": 21, "Sunset District": 15
    },
    "Sunset District": {
        "Union Square": 30, "Russian Hill": 24, "Alamo Square": 17, "Haight-Ashbury": 15,
        "Marina District": 21, "Bayview": 22, "Chinatown": 30, "Presidio": 16
    }
}

# Participants with availability and minimum meeting times
participants = [
    {"name": "Betty", "location": "Russian Hill", "start": "7:00", "end": "16:45", "min_minutes": 105},
    {"name": "Melissa", "location": "Alamo Square", "start": "9:30", "end": "17:15", "min_minutes": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": "12:15", "end": "19:00", "min_minutes": 90},
    {"name": "Jeffrey", "location": "Marina District", "start": "12:15", "end": "18:00", "min_minutes": 45},
    {"name": "James", "location": "Bayview", "start": "7:30", "end": "20:00", "min_minutes": 90},
    {"name": "Anthony", "location": "Chinatown", "start": "11:45", "end": "13:30", "min_minutes": 75},
    {"name": "Timothy", "location": "Presidio", "start": "12:30", "end": "14:45", "min_minutes": 90},
    {"name": "Emily", "location": "Sunset District", "start": "19:30", "end": "21:30", "min_minutes": 120},
]

# Preprocess times to minutes
for p in participants:
    p["start_min"] = time_to_minutes(p["start"])
    p["end_min"] = time_to_minutes(p["end"])

start_time = time_to_minutes(start_time_str)

# Helper to attempt schedule for a given ordering
def schedule_for_order(order):
    curr_loc = start_location
    curr_time = start_time
    itinerary = []
    met = set()
    total_meet_time = 0

    for person in order:
        p = person
        travel = dist[curr_loc][p["location"]]
        arrival = curr_time + travel
        meet_start = max(arrival, p["start_min"])
        meet_end = meet_start + p["min_minutes"]
        if meet_end <= p["end_min"]:
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            met.add(p["name"])
            total_meet_time += p["min_minutes"]
            curr_loc = p["location"]
            curr_time = meet_end
        else:
            # cannot meet this person in this order; skip them
            continue

    return itinerary, met, total_meet_time

# Search over permutations to maximize number of people met; tie-breaker: total meeting time; then earliest finish time
best_itinerary = []
best_met_count = -1
best_total_meet = -1
best_end_time = float('inf')

people = participants[:]

for order in itertools.permutations(people):
    itinerary, met, total_meet_time = schedule_for_order(order)
    met_count = len(met)
    end_time = start_time if not itinerary else time_to_minutes(itinerary[-1]["end_time"])
    # Evaluate
    better = False
    if met_count > best_met_count:
        better = True
    elif met_count == best_met_count:
        if total_meet_time > best_total_meet:
            better = True
        elif total_meet_time == best_total_meet:
            if end_time < best_end_time:
                better = True
    if better:
        best_itinerary = itinerary
        best_met_count = met_count
        best_total_meet = total_meet_time
        best_end_time = end_time

# Output JSON
output = {"itinerary": best_itinerary}
print(json.dumps(output, ensure_ascii=False))