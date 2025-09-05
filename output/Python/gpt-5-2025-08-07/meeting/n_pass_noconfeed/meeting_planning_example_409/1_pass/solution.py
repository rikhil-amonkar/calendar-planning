# SOLUTION:
import itertools
import json

def parse_time(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def minutes_to_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints)
start_location = "Fisherman's Wharf"
start_time_str = "9:00"

friends = [
    {"name": "Thomas", "location": "Bayview", "start": "15:30", "end": "18:30", "min_duration": 120},
    {"name": "Stephanie", "location": "Golden Gate Park", "start": "18:30", "end": "21:45", "min_duration": 30},
    {"name": "Laura", "location": "Nob Hill", "start": "8:45", "end": "16:15", "min_duration": 30},
    {"name": "Betty", "location": "Marina District", "start": "18:45", "end": "21:45", "min_duration": 45},
    {"name": "Patricia", "location": "Embarcadero", "start": "17:30", "end": "22:00", "min_duration": 45},
]

# Convert friend time strings to minutes
for f in friends:
    f["start_min"] = parse_time(f["start"])
    f["end_min"] = parse_time(f["end"])

start_time_min = parse_time(start_time_str)

# Directed travel times in minutes between locations
travel = {
    "Fisherman's Wharf": {
        "Bayview": 26, "Golden Gate Park": 25, "Nob Hill": 11, "Marina District": 9, "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25, "Golden Gate Park": 22, "Nob Hill": 20, "Marina District": 25, "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24, "Bayview": 23, "Nob Hill": 20, "Marina District": 16, "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11, "Bayview": 19, "Golden Gate Park": 17, "Marina District": 11, "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10, "Bayview": 27, "Golden Gate Park": 18, "Nob Hill": 12, "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6, "Bayview": 21, "Golden Gate Park": 25, "Nob Hill": 10, "Marina District": 12
    },
}

def simulate_order(order):
    current_loc = start_location
    current_time = start_time_min
    itinerary = []
    total_wait = 0
    total_travel = 0

    for friend in order:
        # Travel to friend's location
        if current_loc not in travel or friend["location"] not in travel[current_loc]:
            return None  # Missing travel path (should not happen with provided data)
        t_travel = travel[current_loc][friend["location"]]
        arrival = current_time + t_travel
        total_travel += t_travel

        # Start time is max(arrival, window start)
        start_meet = max(arrival, friend["start_min"])
        wait = max(0, start_meet - arrival)
        total_wait += wait

        end_meet = start_meet + friend["min_duration"]

        # Check feasibility within window
        if end_meet > friend["end_min"]:
            return None

        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_str(start_meet),
            "end_time": minutes_to_str(end_meet),
        })

        # Update state
        current_time = end_meet
        current_loc = friend["location"]

    # Return detailed result
    return {
        "itinerary": itinerary,
        "met_count": len(itinerary),
        "finish_time": current_time,
        "total_wait": total_wait,
        "total_travel": total_travel,
    }

# Evaluate all permutations to find the optimal meeting plan
best = None

for order in itertools.permutations(friends, len(friends)):
    result = simulate_order(order)
    if result is None:
        continue

    if best is None:
        best = result
    else:
        # Primary objective: maximize number of meetings
        if result["met_count"] > best["met_count"]:
            best = result
        elif result["met_count"] == best["met_count"]:
            # Secondary: minimize finish time (earliest finish)
            if result["finish_time"] < best["finish_time"]:
                best = result
            elif result["finish_time"] == best["finish_time"]:
                # Tertiary: minimize total waiting time
                if result["total_wait"] < best["total_wait"]:
                    best = result
                elif result["total_wait"] == best["total_wait"]:
                    # Quaternary: minimize total travel time
                    if result["total_travel"] < best["total_travel"]:
                        best = result

# If for some reason no full permutation works (shouldn't happen), try smaller subsets
if best is None:
    for r in range(len(friends), 0, -1):
        found = False
        for subset in itertools.combinations(friends, r):
            for order in itertools.permutations(subset, len(subset)):
                result = simulate_order(order)
                if result is None:
                    continue
                if best is None:
                    best = result
                else:
                    if result["met_count"] > best["met_count"]:
                        best = result
                    elif result["met_count"] == best["met_count"]:
                        if result["finish_time"] < best["finish_time"]:
                            best = result
                        elif result["finish_time"] == best["finish_time"]:
                            if result["total_wait"] < best["total_wait"]:
                                best = result
                            elif result["total_wait"] == best["total_wait"]:
                                if result["total_travel"] < best["total_travel"]:
                                    best = result
                found = True
            if found:
                break
        if best is not None:
            break

# Output the itinerary as JSON
output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))