import itertools
import json

def time_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (directed) in minutes
travel = {
    "Haight-Ashbury": {
        "Mission District": 11,
        "Bayview": 18,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Fisherman's Wharf": 23,
    },
    "Mission District": {
        "Haight-Ashbury": 12,
        "Bayview": 15,
        "Pacific Heights": 16,
        "Russian Hill": 15,
        "Fisherman's Wharf": 22,
    },
    "Bayview": {
        "Haight-Ashbury": 19,
        "Mission District": 13,
        "Pacific Heights": 23,
        "Russian Hill": 23,
        "Fisherman's Wharf": 25,
    },
    "Pacific Heights": {
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Bayview": 22,
        "Russian Hill": 7,
        "Fisherman's Wharf": 13,
    },
    "Russian Hill": {
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Bayview": 23,
        "Pacific Heights": 7,
        "Fisherman's Wharf": 7,
    },
    "Fisherman's Wharf": {
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Russian Hill": 7,
    },
}

# Friends constraints
friends = {
    "Stephanie": {
        "location": "Mission District",
        "window_start": 8 * 60 + 15,   # 8:15
        "window_end": 13 * 60 + 45,    # 13:45
        "min_duration": 90
    },
    "Sandra": {
        "location": "Bayview",
        "window_start": 13 * 60,       # 13:00
        "window_end": 19 * 60 + 30,    # 19:30
        "min_duration": 15
    },
    "Richard": {
        "location": "Pacific Heights",
        "window_start": 7 * 60 + 15,   # 7:15
        "window_end": 10 * 60 + 15,    # 10:15
        "min_duration": 75
    },
    "Brian": {
        "location": "Russian Hill",
        "window_start": 12 * 60 + 15,  # 12:15
        "window_end": 16 * 60,         # 16:00
        "min_duration": 120
    },
    "Jason": {
        "location": "Fisherman's Wharf",
        "window_start": 8 * 60 + 30,   # 8:30
        "window_end": 17 * 60 + 45,    # 17:45
        "min_duration": 60
    }
}

start_location = "Haight-Ashbury"
start_time = 9 * 60  # 9:00

def schedule_for_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        loc = friends[person]["location"]
        t_travel = travel[current_loc][loc]
        arrival = current_time + t_travel
        ws = friends[person]["window_start"]
        we = friends[person]["window_end"]
        dur = friends[person]["min_duration"]

        start_meet = max(arrival, ws)
        end_meet = start_meet + dur

        if end_meet > we:
            return None  # infeasible

        wait = max(0, start_meet - arrival)
        total_wait += wait
        total_travel += t_travel

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": time_to_str(start_meet),
            "end_time": time_to_str(end_meet)
        })

        current_loc = loc
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "end_time": current_time,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "met_count": len(order)
    }

people = list(friends.keys())

best_plan = None

# Try subsets by decreasing size to maximize number of friends met
for k in range(len(people), 0, -1):
    found_for_k = []
    for subset in itertools.permutations(people, k):
        plan = schedule_for_order(subset)
        if plan is not None:
            found_for_k.append(plan)
    if found_for_k:
        # Select best plan: earliest end_time, then minimal total_travel, then minimal total_wait
        found_for_k.sort(key=lambda p: (p["end_time"], p["total_travel"], p["total_wait"]))
        best_plan = found_for_k[0]
        break

# If no plan at all, itinerary is empty
output = {"itinerary": best_plan["itinerary"] if best_plan else []}
print(json.dumps(output, ensure_ascii=False))