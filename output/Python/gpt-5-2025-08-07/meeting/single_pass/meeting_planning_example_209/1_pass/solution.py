import itertools
import json

# Input variables (meeting constraints and travel times)

# Locations
SUNSET = "Sunset District"
CHINATOWN = "Chinatown"
RUSSIAN_HILL = "Russian Hill"
NORTH_BEACH = "North Beach"

# Travel times in minutes (directed)
travel = {
    SUNSET: {CHINATOWN: 30, RUSSIAN_HILL: 24, NORTH_BEACH: 29},
    CHINATOWN: {SUNSET: 29, RUSSIAN_HILL: 7, NORTH_BEACH: 3},
    RUSSIAN_HILL: {SUNSET: 23, CHINATOWN: 9, NORTH_BEACH: 5},
    NORTH_BEACH: {SUNSET: 27, CHINATOWN: 6, RUSSIAN_HILL: 4},
}

# Helper to convert H:MM to minutes (24h)
def hm_to_min(h, m):
    return h * 60 + m

# Helper to format minutes to H:MM (24h, no leading zero on hour)
def min_to_hm(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Start location/time
start_location = SUNSET
start_time = hm_to_min(9, 0)  # 9:00

# Friends constraints: name, location, availability window [start, end], required minimum duration
friends = [
    {
        "name": "Anthony",
        "location": CHINATOWN,
        "avail_start": hm_to_min(13, 15),  # 13:15
        "avail_end": hm_to_min(14, 30),    # 14:30
        "min_duration": 60,
    },
    {
        "name": "Rebecca",
        "location": RUSSIAN_HILL,
        "avail_start": hm_to_min(19, 30),  # 19:30
        "avail_end": hm_to_min(21, 15),    # 21:15
        "min_duration": 105,
    },
    {
        "name": "Melissa",
        "location": NORTH_BEACH,
        "avail_start": hm_to_min(8, 15),   # 8:15
        "avail_end": hm_to_min(13, 30),    # 13:30
        "min_duration": 105,
    },
]

def evaluate_order(order):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        # Travel to friend's location
        t_travel = travel[current_loc][person["location"]]
        arrival = current_time + t_travel
        total_travel += t_travel

        # Determine feasible meeting start and end times
        start_meet = max(arrival, person["avail_start"])
        end_meet = start_meet + person["min_duration"]

        # Check feasibility within availability window
        if end_meet > person["avail_end"]:
            return None  # infeasible

        # Accumulate wait (if any)
        if start_meet > arrival:
            total_wait += (start_meet - arrival)

        # Record the meeting
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time": min_to_hm(start_meet),
            "end_time": min_to_hm(end_meet),
        })

        # Update current state
        current_time = end_meet
        current_loc = person["location"]

    finish_time = current_time
    # Objective metrics
    num_met = len(order)
    return {
        "feasible": True,
        "num_met": num_met,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "finish_time": finish_time,
        "itinerary": itinerary,
    }

def optimize_schedule(friends):
    best = None
    # Explore all subsets (largest to smallest), and all permutations within each subset
    for r in range(len(friends), 0, -1):
        found_at_this_size = []
        for subset in itertools.combinations(friends, r):
            for perm in itertools.permutations(subset):
                result = evaluate_order(perm)
                if result:
                    found_at_this_size.append(result)
        if found_at_this_size:
            # Choose best among those with r meetings:
            # Criteria: maximize num_met, then minimize wait, then travel, then finish time
            best = min(
                found_at_this_size,
                key=lambda x: (-x["num_met"], x["total_wait"], x["total_travel"], x["finish_time"])
            )
            break
    # If none feasible (shouldn't happen), return empty itinerary
    if not best:
        return {"itinerary": []}
    return {"itinerary": best["itinerary"]}

def main():
    result = optimize_schedule(friends)
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()