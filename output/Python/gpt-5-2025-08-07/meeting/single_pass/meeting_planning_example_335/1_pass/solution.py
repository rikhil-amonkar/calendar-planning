# SOLUTION:
import itertools
import json

def minutes_to_str(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

# Input variables: travel times (in minutes) between locations (directed)
travel = {
    "Pacific Heights": {
        "North Beach": 9,
        "Financial District": 13,
        "Alamo Square": 10,
        "Mission District": 15,
    },
    "North Beach": {
        "Pacific Heights": 8,
        "Financial District": 8,
        "Alamo Square": 16,
        "Mission District": 18,
    },
    "Financial District": {
        "Pacific Heights": 13,
        "North Beach": 7,
        "Alamo Square": 17,
        "Mission District": 17,
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "North Beach": 15,
        "Financial District": 17,
        "Mission District": 10,
    },
    "Mission District": {
        "Pacific Heights": 16,
        "North Beach": 17,
        "Financial District": 17,
        "Alamo Square": 11,
    },
}

# Start conditions
start_location = "Pacific Heights"
start_time = 9 * 60  # 9:00

# Friends constraints
friends = [
    {
        "name": "Helen",
        "location": "North Beach",
        "window_start": 9 * 60,
        "window_end": 17 * 60,
        "min_duration": 15,
    },
    {
        "name": "Betty",
        "location": "Financial District",
        "window_start": 19 * 60,
        "window_end": 21 * 60 + 45,  # 21:45
        "min_duration": 90,
    },
    {
        "name": "Amanda",
        "location": "Alamo Square",
        "window_start": 19 * 60 + 45,  # 19:45
        "window_end": 21 * 60,  # 21:00
        "min_duration": 60,
    },
    {
        "name": "Kevin",
        "location": "Mission District",
        "window_start": 10 * 60 + 45,  # 10:45
        "window_end": 14 * 60 + 45,  # 14:45
        "min_duration": 45,
    },
]

def simulate_schedule(order, start_loc, start_t, travel_times):
    itinerary = []
    t = start_t
    loc = start_loc
    total_wait = 0
    total_travel = 0

    for person in order:
        to_loc = person["location"]
        if loc not in travel_times or to_loc not in travel_times[loc]:
            return None  # Missing travel time data
        travel_time = travel_times[loc][to_loc]
        total_travel += travel_time
        arrival = t + travel_time
        start_meet = max(arrival, person["window_start"])
        wait = max(0, start_meet - arrival)
        total_wait += wait
        end_meet = start_meet + person["min_duration"]
        if end_meet > person["window_end"]:
            return None  # Not feasible within window
        itinerary.append({
            "action": "meet",
            "location": to_loc,
            "person": person["name"],
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
        })
        t = end_meet
        loc = to_loc

    return {
        "itinerary": itinerary,
        "end_time": t,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "met_count": len(order),
    }

# Search for optimal schedule:
# Objective: maximize number of friends met; tie-breakers: minimize total waiting, then earliest end time, then total travel
best_solution = None

for r in range(len(friends), 0, -1):
    feasible_candidates = []
    for subset in itertools.combinations(friends, r):
        for perm in itertools.permutations(subset):
            result = simulate_schedule(perm, start_location, start_time, travel)
            if result is not None:
                feasible_candidates.append(result)
    if feasible_candidates:
        # Choose best among this cardinality
        feasible_candidates.sort(key=lambda s: (s["total_wait"], s["end_time"], s["total_travel"]))
        best_solution = feasible_candidates[0]
        break

output = {"itinerary": best_solution["itinerary"] if best_solution else []}
print(json.dumps(output, ensure_ascii=False, indent=2))