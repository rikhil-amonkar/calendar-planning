import itertools
import json

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Chinatown": {
        "Embarcadero": 5, "Pacific Heights": 10, "Russian Hill": 7, "Haight-Ashbury": 19,
        "Golden Gate Park": 23, "Fisherman's Wharf": 8, "Sunset District": 29, "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7, "Pacific Heights": 11, "Russian Hill": 8, "Haight-Ashbury": 21,
        "Golden Gate Park": 25, "Fisherman's Wharf": 6, "Sunset District": 30, "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11, "Embarcadero": 10, "Russian Hill": 7, "Haight-Ashbury": 11,
        "Golden Gate Park": 15, "Fisherman's Wharf": 13, "Sunset District": 21, "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9, "Embarcadero": 8, "Pacific Heights": 7, "Haight-Ashbury": 17,
        "Golden Gate Park": 21, "Fisherman's Wharf": 7, "Sunset District": 23, "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19, "Embarcadero": 20, "Pacific Heights": 12, "Russian Hill": 17,
        "Golden Gate Park": 7, "Fisherman's Wharf": 23, "Sunset District": 15, "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23, "Embarcadero": 25, "Pacific Heights": 16, "Russian Hill": 19,
        "Haight-Ashbury": 7, "Fisherman's Wharf": 24, "Sunset District": 10, "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12, "Embarcadero": 8, "Pacific Heights": 12, "Russian Hill": 7,
        "Haight-Ashbury": 22, "Golden Gate Park": 25, "Sunset District": 27, "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30, "Embarcadero": 30, "Pacific Heights": 21, "Russian Hill": 24,
        "Haight-Ashbury": 15, "Golden Gate Park": 11, "Fisherman's Wharf": 29, "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22, "Embarcadero": 22, "Pacific Heights": 16, "Russian Hill": 18,
        "Haight-Ashbury": 6, "Golden Gate Park": 11, "Fisherman's Wharf": 24, "Sunset District": 17
    }
}

# Meeting constraints
friends = [
    {
        "name": "Richard",
        "location": "Embarcadero",
        "start": minutes(15, 15),
        "end": minutes(18, 45),
        "min_duration": 90
    },
    {
        "name": "Mark",
        "location": "Pacific Heights",
        "start": minutes(15, 0),
        "end": minutes(17, 0),
        "min_duration": 45
    },
    {
        "name": "Matthew",
        "location": "Russian Hill",
        "start": minutes(17, 30),
        "end": minutes(21, 0),
        "min_duration": 90
    },
    {
        "name": "Rebecca",
        "location": "Haight-Ashbury",
        "start": minutes(14, 45),
        "end": minutes(18, 0),
        "min_duration": 60
    },
    {
        "name": "Melissa",
        "location": "Golden Gate Park",
        "start": minutes(13, 45),
        "end": minutes(17, 30),
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Fisherman's Wharf",
        "start": minutes(14, 45),
        "end": minutes(20, 15),
        "min_duration": 15
    },
    {
        "name": "Emily",
        "location": "Sunset District",
        "start": minutes(15, 45),
        "end": minutes(17, 0),
        "min_duration": 45
    },
    {
        "name": "George",
        "location": "The Castro",
        "start": minutes(14, 0),
        "end": minutes(16, 15),
        "min_duration": 75
    }
]

start_location = "Chinatown"
start_time = minutes(9, 0)

def simulate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_wait = 0
    total_travel = 0
    for person in order:
        loc = person["location"]
        if current_loc not in travel or loc not in travel[current_loc]:
            # Cannot travel; skip
            continue
        t_travel = travel[current_loc][loc]
        arrival = current_time + t_travel
        start = max(arrival, person["start"])
        end = start + person["min_duration"]
        if end <= person["end"]:
            # Meeting feasible; take it
            wait = max(0, person["start"] - arrival)
            total_wait += wait
            total_travel += t_travel
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person["name"],
                "start_time": minutes_to_str(start),
                "end_time": minutes_to_str(end)
            })
            current_time = end
            current_loc = loc
        else:
            # Skip this person
            continue
    finish_time = current_time
    return {
        "count": len(itinerary),
        "finish_time": finish_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "itinerary": itinerary
    }

# Explore all permutations of friends; for each, greedily schedule feasible meetings in that order
best = None
for order in itertools.permutations(friends, len(friends)):
    res = simulate_order(order)
    if best is None:
        best = res
    else:
        # Compare: maximize count, then minimize finish_time, then minimize total_wait, then minimize total_travel
        if (res["count"] > best["count"] or
            (res["count"] == best["count"] and res["finish_time"] < best["finish_time"]) or
            (res["count"] == best["count"] and res["finish_time"] == best["finish_time"] and res["total_wait"] < best["total_wait"]) or
            (res["count"] == best["count"] and res["finish_time"] == best["finish_time"] and res["total_wait"] == best["total_wait"] and res["total_travel"] < best["total_travel"])):
            best = res

# Output JSON with the best itinerary
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False))