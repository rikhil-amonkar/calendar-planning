import itertools
import json

def minutes(h, m):
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input parameters
start_location = "Presidio"
start_time = minutes(9, 0)

# Travel times (directed, in minutes)
travel = {
    "Presidio": {
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Chinatown": 21,
        "North Beach": 18,
        "Mission District": 26
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Bayview": 23,
        "Chinatown": 23,
        "North Beach": 24,
        "Mission District": 17
    },
    "Bayview": {
        "Presidio": 31,
        "Golden Gate Park": 22,
        "Chinatown": 18,
        "North Beach": 21,
        "Mission District": 13
    },
    "Chinatown": {
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "North Beach": 3,
        "Mission District": 18
    },
    "North Beach": {
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 22,
        "Chinatown": 6,
        "Mission District": 18
    },
    "Mission District": {
        "Presidio": 25,
        "Golden Gate Park": 17,
        "Bayview": 15,
        "Chinatown": 16,
        "North Beach": 17
    }
}

# Friends and constraints
people = [
    {
        "name": "Jessica",
        "location": "Golden Gate Park",
        "available_start": minutes(13, 45),
        "available_end": minutes(15, 0),
        "min_duration": 30
    },
    {
        "name": "Ashley",
        "location": "Bayview",
        "available_start": minutes(17, 15),
        "available_end": minutes(20, 0),
        "min_duration": 105
    },
    {
        "name": "Ronald",
        "location": "Chinatown",
        "available_start": minutes(7, 15),
        "available_end": minutes(14, 45),
        "min_duration": 90
    },
    {
        "name": "William",
        "location": "North Beach",
        "available_start": minutes(13, 15),
        "available_end": minutes(20, 15),
        "min_duration": 15
    },
    {
        "name": "Daniel",
        "location": "Mission District",
        "available_start": minutes(7, 0),
        "available_end": minutes(11, 15),
        "min_duration": 105
    }
]

def schedule_for_order(order):
    current_time = start_time
    current_location = start_location
    itinerary = []
    total_meet_minutes = 0
    total_travel = 0

    for person in order:
        from_loc = current_location
        to_loc = person["location"]
        # Check travel time exists
        if from_loc not in travel or to_loc not in travel[from_loc]:
            return None
        ttime = travel[from_loc][to_loc]
        total_travel += ttime
        arrival = current_time + ttime
        start = max(arrival, person["available_start"])
        end = start + person["min_duration"]
        if end > person["available_end"]:
            return None
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start": start,
            "end": end
        })
        total_meet_minutes += person["min_duration"]
        current_time = end
        current_location = to_loc

    return {
        "itinerary": itinerary,
        "finish_time": current_time,
        "total_meet_minutes": total_meet_minutes,
        "total_travel": total_travel
    }

best_plan = None
best_count = -1

# Search over subsets by descending size to maximize number of friends met
n = len(people)
for size in range(n, 0, -1):
    best_for_size = None
    # combinations of people of this size
    for subset in itertools.combinations(people, size):
        # try all orders
        for order in itertools.permutations(subset):
            plan = schedule_for_order(order)
            if plan is None:
                continue
            # Score: maximize total people (constant here), then maximize total meeting time (sum of mins), then minimize finish time, then minimize total travel
            score = (
                len(order),
                plan["total_meet_minutes"],
                -plan["finish_time"],
                -plan["total_travel"]
            )
            if best_for_size is None or score > best_for_size["score"]:
                best_for_size = {
                    "plan": plan,
                    "score": score
                }
    if best_for_size is not None:
        best_plan = best_for_size["plan"]
        best_count = size
        break

# Prepare JSON output
output = {"itinerary": []}
if best_plan:
    for item in best_plan["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"])
        })

print(json.dumps(output))