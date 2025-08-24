import json
from copy import deepcopy

def to_min(h, m):
    return h * 60 + m

def min_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
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

# People constraints
people = [
    {
        "name": "Amanda",
        "location": "Marina District",
        "start": to_min(14, 45),
        "end": to_min(19, 30),
        "min_duration": 105
    },
    {
        "name": "Melissa",
        "location": "The Castro",
        "start": to_min(9, 30),
        "end": to_min(17, 0),
        "min_duration": 30
    },
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "start": to_min(12, 45),
        "end": to_min(18, 45),
        "min_duration": 120
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "start": to_min(10, 15),
        "end": to_min(13, 15),
        "min_duration": 30
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": to_min(17, 0),
        "end": to_min(21, 30),
        "min_duration": 105
    },
    {
        "name": "Karen",
        "location": "Mission District",
        "start": to_min(17, 30),
        "end": to_min(20, 30),
        "min_duration": 105
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "start": to_min(11, 15),
        "end": to_min(17, 30),
        "min_duration": 120
    },
    {
        "name": "Joseph",
        "location": "Golden Gate Park",
        "start": to_min(8, 30),
        "end": to_min(21, 15),
        "min_duration": 105
    }
]

# Index people by name for quick access
people_by_name = {p["name"]: p for p in people}

# Start conditions
start_location = "Presidio"
start_time = to_min(9, 0)

best_solution = {
    "count": -1,
    "total_meeting": 0,
    "total_travel": float('inf'),
    "finish_time": float('inf'),
    "itinerary": []
}

def evaluate_and_update(itinerary, total_meeting, total_travel):
    global best_solution
    count = len(itinerary)
    finish_time = itinerary[-1]["end"] if itinerary else start_time
    better = False
    if count > best_solution["count"]:
        better = True
    elif count == best_solution["count"]:
        if total_meeting > best_solution["total_meeting"]:
            better = True
        elif total_meeting == best_solution["total_meeting"]:
            if total_travel < best_solution["total_travel"]:
                better = True
            elif total_travel == best_solution["total_travel"]:
                if finish_time < best_solution["finish_time"]:
                    better = True
    if better:
        best_solution = {
            "count": count,
            "total_meeting": total_meeting,
            "total_travel": total_travel,
            "finish_time": finish_time,
            "itinerary": deepcopy(itinerary)
        }

def dfs(curr_loc, curr_time, remaining_names, itinerary, total_meeting, total_travel):
    # Update best with current partial plan
    evaluate_and_update(itinerary, total_meeting, total_travel)

    # Prune if even meeting everyone else can't beat current best
    potential_max = len(itinerary) + len(remaining_names)
    if potential_max < best_solution["count"]:
        return

    # Try each remaining person next
    for name in sorted(remaining_names):
        p = people_by_name[name]
        # Travel time from current location to person's location
        if curr_loc not in travel or p["location"] not in travel[curr_loc]:
            continue  # no path defined
        t_travel = travel[curr_loc][p["location"]]
        arrival = curr_time + t_travel
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet <= p["end"]:
            new_it = itinerary + [{
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start": start_meet,
                "end": end_meet
            }]
            new_remaining = set(remaining_names)
            new_remaining.remove(name)
            dfs(p["location"], end_meet, new_remaining, new_it, total_meeting + p["min_duration"], total_travel + t_travel)

# Run search
all_names = set(p["name"] for p in people)
dfs(start_location, start_time, all_names, [], 0, 0)

# Prepare output JSON
output_itinerary = []
for item in best_solution["itinerary"]:
    output_itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": min_to_str(item["start"]),
        "end_time": min_to_str(item["end"])
    })

result = {"itinerary": output_itinerary}

print(json.dumps(result, ensure_ascii=False))