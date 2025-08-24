# SOLUTION:
import json
import itertools

# Time helper functions
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters

start_location = "Union Square"
start_time = to_minutes(9, 0)

travel = {
    "Union Square": {
        "Golden Gate Park": 22,
        "Pacific Heights": 15,
        "Presidio": 24,
        "Chinatown": 7,
        "The Castro": 19
    },
    "Golden Gate Park": {
        "Union Square": 22,
        "Pacific Heights": 16,
        "Presidio": 11,
        "Chinatown": 23,
        "The Castro": 13
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Presidio": 11,
        "Chinatown": 11,
        "The Castro": 16
    },
    "Presidio": {
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Pacific Heights": 11,
        "Chinatown": 21,
        "The Castro": 21
    },
    "Chinatown": {
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Pacific Heights": 10,
        "Presidio": 19,
        "The Castro": 22
    },
    "The Castro": {
        "Union Square": 19,
        "Golden Gate Park": 11,
        "Pacific Heights": 16,
        "Presidio": 20,
        "Chinatown": 20
    }
}

friends = {
    "Andrew": {
        "location": "Golden Gate Park",
        "start": to_minutes(11, 45),
        "end": to_minutes(14, 30),
        "min": 75
    },
    "Sarah": {
        "location": "Pacific Heights",
        "start": to_minutes(16, 15),
        "end": to_minutes(18, 45),
        "min": 15
    },
    "Nancy": {
        "location": "Presidio",
        "start": to_minutes(17, 30),
        "end": to_minutes(19, 15),
        "min": 60
    },
    "Rebecca": {
        "location": "Chinatown",
        "start": to_minutes(9, 45),
        "end": to_minutes(21, 30),
        "min": 90
    },
    "Robert": {
        "location": "The Castro",
        "start": to_minutes(8, 30),
        "end": to_minutes(14, 15),
        "min": 30
    }
}

# Simulation function: tries to meet everyone in the given order
def simulate(order):
    current_loc = start_location
    current_time_local = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        info = friends[person]
        loc = info["location"]

        # Travel time between locations
        try:
            ttime = travel[current_loc][loc]
        except KeyError:
            return None  # Missing travel time, treat as infeasible

        arrival = current_time_local + ttime
        start_mt = max(arrival, info["start"])
        end_mt = start_mt + info["min"]

        if end_mt <= info["end"]:
            # Record meeting
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": fmt_time(start_mt),
                "end_time": fmt_time(end_mt)
            })
            total_travel += ttime
            total_wait += max(0, start_mt - arrival)
            current_loc = loc
            current_time_local = end_mt
        else:
            return None  # Cannot meet this person in this order

    return {
        "itinerary": itinerary,
        "finish_time": current_time_local,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "total_meeting_time": sum(friends[p]["min"] for p in order),
        "met_count": len(order),
        "order": order
    }

# Optimization: maximize number of friends met; tie-breakers as described
friend_names = list(friends.keys())

best_plan = None

# Try from meeting all friends down to fewer
for k in range(len(friend_names), 0, -1):
    for combo in itertools.combinations(friend_names, k):
        for perm in itertools.permutations(combo):
            result = simulate(perm)
            if result is None:
                continue
            # Evaluate with lexicographic score:
            # (met_count, total_meeting_time, -finish_time, -total_wait, -total_travel)
            score = (
                result["met_count"],
                result["total_meeting_time"],
                -result["finish_time"],
                -result["total_wait"],
                -result["total_travel"]
            )
            if best_plan is None or score > best_plan["score"]:
                best_plan = {
                    "score": score,
                    "result": result
                }
    if best_plan is not None and best_plan["result"]["met_count"] == k:
        break  # Found optimal number of meetings; no need to try fewer

output = {
    "itinerary": best_plan["result"]["itinerary"] if best_plan else []
}

print(json.dumps(output, ensure_ascii=False))