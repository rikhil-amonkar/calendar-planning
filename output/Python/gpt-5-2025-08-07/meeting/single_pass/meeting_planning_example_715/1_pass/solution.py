import json
from itertools import permutations

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes), directed
travel = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9
    }
}

# Meeting constraints
people = {
    "Amanda": {
        "location": "Marina District",
        "start": to_minutes(14, 45),
        "end": to_minutes(19, 30),
        "min_duration": 105
    },
    "Melissa": {
        "location": "The Castro",
        "start": to_minutes(9, 30),
        "end": to_minutes(17, 0),
        "min_duration": 30
    },
    "Jeffrey": {
        "location": "Fisherman's Wharf",
        "start": to_minutes(12, 45),
        "end": to_minutes(18, 45),
        "min_duration": 120
    },
    "Matthew": {
        "location": "Bayview",
        "start": to_minutes(10, 15),
        "end": to_minutes(13, 15),
        "min_duration": 30
    },
    "Nancy": {
        "location": "Pacific Heights",
        "start": to_minutes(17, 0),
        "end": to_minutes(21, 30),
        "min_duration": 105
    },
    "Karen": {
        "location": "Mission District",
        "start": to_minutes(17, 30),
        "end": to_minutes(20, 30),
        "min_duration": 105
    },
    "Robert": {
        "location": "Alamo Square",
        "start": to_minutes(11, 15),
        "end": to_minutes(17, 30),
        "min_duration": 120
    },
    "Joseph": {
        "location": "Golden Gate Park",
        "start": to_minutes(8, 30),
        "end": to_minutes(21, 15),
        "min_duration": 105
    }
}

start_location = "Presidio"
start_time = to_minutes(9, 0)

# Verify travel matrix has all required directed edges
locations = set(travel.keys())
for a in travel:
    for b in locations - {a}:
        assert b in travel[a], f"Missing travel time from {a} to {b}"

# Depth-first search over all feasible sequences of meetings
best_solution = {
    "itinerary": [],
    "count": 0,
    "end_time": start_time,
    "total_travel": 0
}

def better(sol_a, sol_b):
    # Return True if sol_a is better than sol_b
    if sol_a["count"] != sol_b["count"]:
        return sol_a["count"] > sol_b["count"]
    if sol_a["end_time"] != sol_b["end_time"]:
        return sol_a["end_time"] < sol_b["end_time"]
    if sol_a["total_travel"] != sol_b["total_travel"]:
        return sol_a["total_travel"] < sol_b["total_travel"]
    # If still tied, arbitrary but stable preference by lexicographic itinerary
    a_names = [item["person"] for item in sol_a["itinerary"]]
    b_names = [item["person"] for item in sol_b["itinerary"]]
    return a_names < b_names

def search(current_loc, current_time, remaining_names, itinerary, total_travel):
    global best_solution

    # Consider updating best with current partial plan
    current_solution = {
        "itinerary": itinerary,
        "count": len(itinerary),
        "end_time": current_time,
        "total_travel": total_travel
    }
    if better(current_solution, best_solution):
        best_solution = current_solution

    # Try to extend with each remaining person if feasible
    for name in list(remaining_names):
        info = people[name]
        loc = info["location"]
        travel_time = travel[current_loc][loc]
        arrival = current_time + travel_time
        start = max(arrival, info["start"])
        end = start + info["min_duration"]
        if end <= info["end"]:
            # feasible meeting
            meeting = {
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            }
            new_remaining = remaining_names - {name}
            search(loc, end, new_remaining, itinerary + [meeting], total_travel + travel_time)
        # else skip implicitly by not choosing this person now

# Kick off search
all_names = set(people.keys())
search(start_location, start_time, all_names, [], 0)

# Prepare JSON output
output = {
    "itinerary": best_solution["itinerary"]
}

print(json.dumps(output, indent=2))