import itertools
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) - directed
travel = {
    "Mission District": {
        "The Castro": 7,
        "Nob Hill": 12,
        "Presidio": 25,
        "Marina District": 19,
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "Chinatown": 16,
        "Richmond District": 20,
    },
    "The Castro": {
        "Mission District": 7,
        "Nob Hill": 16,
        "Presidio": 20,
        "Marina District": 21,
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Chinatown": 22,
        "Richmond District": 16,
    },
    "Nob Hill": {
        "Mission District": 13,
        "The Castro": 17,
        "Presidio": 17,
        "Marina District": 11,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Chinatown": 6,
        "Richmond District": 14,
    },
    "Presidio": {
        "Mission District": 26,
        "The Castro": 21,
        "Nob Hill": 18,
        "Marina District": 11,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7,
    },
    "Marina District": {
        "Mission District": 20,
        "The Castro": 22,
        "Nob Hill": 12,
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Chinatown": 15,
        "Richmond District": 11,
    },
    "Pacific Heights": {
        "Mission District": 15,
        "The Castro": 16,
        "Nob Hill": 8,
        "Presidio": 11,
        "Marina District": 6,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Richmond District": 12,
    },
    "Golden Gate Park": {
        "Mission District": 17,
        "The Castro": 13,
        "Nob Hill": 20,
        "Presidio": 11,
        "Marina District": 16,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Richmond District": 7,
    },
    "Chinatown": {
        "Mission District": 17,
        "The Castro": 22,
        "Nob Hill": 9,
        "Presidio": 19,
        "Marina District": 12,
        "Pacific Heights": 10,
        "Golden Gate Park": 23,
        "Richmond District": 20,
    },
    "Richmond District": {
        "Mission District": 20,
        "The Castro": 16,
        "Nob Hill": 17,
        "Presidio": 7,
        "Marina District": 9,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Chinatown": 20,
    },
}

# People constraints
people = {
    "Lisa": {
        "location": "The Castro",
        "start": minutes(19, 15),
        "end": minutes(21, 15),
        "duration": 120,
    },
    "Daniel": {
        "location": "Nob Hill",
        "start": minutes(8, 15),
        "end": minutes(11, 0),
        "duration": 15,
    },
    "Elizabeth": {
        "location": "Presidio",
        "start": minutes(21, 15),
        "end": minutes(22, 15),
        "duration": 45,
    },
    "Steven": {
        "location": "Marina District",
        "start": minutes(16, 30),
        "end": minutes(20, 45),
        "duration": 90,
    },
    "Timothy": {
        "location": "Pacific Heights",
        "start": minutes(12, 0),
        "end": minutes(18, 0),
        "duration": 90,
    },
    "Ashley": {
        "location": "Golden Gate Park",
        "start": minutes(20, 45),
        "end": minutes(21, 45),
        "duration": 60,
    },
    "Kevin": {
        "location": "Chinatown",
        "start": minutes(12, 0),
        "end": minutes(19, 0),
        "duration": 30,
    },
    "Betty": {
        "location": "Richmond District",
        "start": minutes(13, 15),
        "end": minutes(15, 45),
        "duration": 30,
    },
}

start_location = "Mission District"
start_time = minutes(9, 0)

names = list(people.keys())

def simulate(order):
    cur_loc = start_location
    cur_time = start_time
    itinerary = []
    total_wait = 0
    total_travel = 0

    for name in order:
        p = people[name]
        # travel time; if not found, treat as impossible
        tr = travel.get(cur_loc, {}).get(p["location"], None)
        if tr is None:
            continue  # skip if no known route
        arrival = cur_time + tr
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["duration"]
        if end_meet <= p["end"]:
            # feasible; commit travel and meeting
            total_travel += tr
            total_wait += max(0, start_meet - arrival)
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": fmt_time(start_meet),
                "end_time": fmt_time(end_meet),
            })
            cur_time = end_meet
            cur_loc = p["location"]
        else:
            # not feasible; skip this person
            continue

    return itinerary, total_wait, total_travel

best_itin = []
best_count = -1
best_finish = float('inf')
best_wait = float('inf')
best_travel = float('inf')

# Explore all permutations; greedy schedule per permutation, skipping infeasible meetings
for order in itertools.permutations(names):
    itin, wait_time, travel_time = simulate(order)
    count = len(itin)
    finish_time = start_time if count == 0 else minutes(*map(int, itin[-1]["end_time"].split(":")))
    # Primary: maximize number met; then earliest finish; then minimal waiting; then minimal travel
    if (count > best_count or
        (count == best_count and finish_time < best_finish) or
        (count == best_count and finish_time == best_finish and wait_time < best_wait) or
        (count == best_count and finish_time == best_finish and wait_time == best_wait and travel_time < best_travel)):
        best_itin = itin
        best_count = count
        best_finish = finish_time
        best_wait = wait_time
        best_travel = travel_time

result = {
    "itinerary": best_itin
}

print(json.dumps(result, ensure_ascii=False))