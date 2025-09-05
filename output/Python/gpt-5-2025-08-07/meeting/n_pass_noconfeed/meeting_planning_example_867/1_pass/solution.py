import itertools
import json

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times (minutes) between locations
dist = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Golden Gate Park"): 7,

    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Golden Gate Park"): 17,

    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Union Square", "Golden Gate Park"): 22,

    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Golden Gate Park"): 15,

    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Golden Gate Park"): 22,

    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,

    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Golden Gate Park"): 18,

    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Golden Gate Park"): 9,

    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Golden Gate Park"): 11,

    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Sunset District"): 10,
}

# People constraints (minutes since midnight)
people = [
    {"name": "Elizabeth", "location": "Mission District", "start": 10*60+30, "end": 20*60, "dur": 90},
    {"name": "David", "location": "Union Square", "start": 15*60+15, "end": 19*60, "dur": 45},
    {"name": "Sandra", "location": "Pacific Heights", "start": 7*60, "end": 20*60, "dur": 120},
    {"name": "Thomas", "location": "Bayview", "start": 19*60+30, "end": 20*60+30, "dur": 30},
    {"name": "Robert", "location": "Fisherman's Wharf", "start": 10*60, "end": 15*60, "dur": 15},
    {"name": "Kenneth", "location": "Marina District", "start": 10*60+45, "end": 13*60, "dur": 45},
    {"name": "Melissa", "location": "Richmond District", "start": 18*60+15, "end": 20*60, "dur": 15},
    {"name": "Kimberly", "location": "Sunset District", "start": 10*60+15, "end": 18*60+15, "dur": 105},
    {"name": "Amanda", "location": "Golden Gate Park", "start": 7*60+45, "end": 18*60+45, "dur": 15},
]

start_location = "Haight-Ashbury"
start_time = 9 * 60  # 9:00

best_itinerary = []
best_count = -1
best_finish = float('inf')
best_travel = float('inf')
best_wait = float('inf')

for order in itertools.permutations(people):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    travel_total = 0
    wait_total = 0
    met_count = 0

    for p in order:
        travel_time = dist.get((current_loc, p["location"]))
        if travel_time is None:
            continue  # If no path defined, skip
        arrival = current_time + travel_time
        start_mt = max(arrival, p["start"])
        end_mt = start_mt + p["dur"]
        if end_mt <= p["end"]:
            # Commit travel and meeting
            travel_total += travel_time
            wait_total += max(0, p["start"] - arrival)
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_str(start_mt),
                "end_time": minutes_to_str(end_mt),
            })
            current_loc = p["location"]
            current_time = end_mt
            met_count += 1
        else:
            # Skip this person; do not move
            continue

    finish_time = current_time

    score = (met_count, -finish_time, -travel_total, -wait_total)
    best_score = (best_count, -best_finish, -best_travel, -best_wait)
    if score > best_score:
        best_itinerary = itinerary
        best_count = met_count
        best_finish = finish_time
        best_travel = travel_total
        best_wait = wait_total

output = {
    "itinerary": best_itinerary
}
print(json.dumps(output, ensure_ascii=False))