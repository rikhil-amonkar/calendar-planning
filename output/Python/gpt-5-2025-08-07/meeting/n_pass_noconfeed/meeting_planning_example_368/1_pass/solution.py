"""SOLUTION:"""
import itertools
import json
import re

# Helper functions
def parse_ampm(s):
    m = re.match(r'^\s*(\d{1,2}):(\d{2})\s*([AP]M)\s*$', s, re.IGNORECASE)
    if not m:
        raise ValueError(f"Invalid time format: {s}")
    h = int(m.group(1))
    minute = int(m.group(2))
    ampm = m.group(3).upper()
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + minute

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Bayview"
arrival_time_str = "9:00AM"

friends = [
    {
        "name": "Joseph",
        "location": "Russian Hill",
        "window_start": "8:30AM",
        "window_end": "7:15PM",
        "min_duration_min": 60,
    },
    {
        "name": "Nancy",
        "location": "Alamo Square",
        "window_start": "11:00AM",
        "window_end": "4:00PM",
        "min_duration_min": 90,
    },
    {
        "name": "Jason",
        "location": "North Beach",
        "window_start": "4:45PM",
        "window_end": "9:45PM",
        "min_duration_min": 15,
    },
    {
        "name": "Jeffrey",
        "location": "Financial District",
        "window_start": "10:30AM",
        "window_end": "3:45PM",
        "min_duration_min": 45,
    },
]

# Travel times in minutes
travel = {
    "Bayview": {
        "Russian Hill": 23,
        "Alamo Square": 16,
        "North Beach": 21,
        "Financial District": 19,
    },
    "Russian Hill": {
        "Bayview": 23,
        "Alamo Square": 15,
        "North Beach": 5,
        "Financial District": 11,
    },
    "Alamo Square": {
        "Bayview": 16,
        "Russian Hill": 13,
        "North Beach": 15,
        "Financial District": 17,
    },
    "North Beach": {
        "Bayview": 22,
        "Russian Hill": 4,
        "Alamo Square": 16,
        "Financial District": 8,
    },
    "Financial District": {
        "Bayview": 19,
        "Russian Hill": 10,
        "Alamo Square": 17,
        "North Beach": 7,
    },
}

# Convert times to minutes
start_time = parse_ampm(arrival_time_str)
for f in friends:
    f["start_min"] = parse_ampm(f["window_start"])
    f["end_min"] = parse_ampm(f["window_end"])

# Simulation function for a given visiting order
def simulate(order):
    time = start_time
    location = start_location
    itinerary = []
    total_wait = 0
    total_travel = 0

    for friend in order:
        loc_to = friend["location"]
        if location not in travel or loc_to not in travel[location]:
            return None  # invalid route
        t_travel = travel[location][loc_to]
        total_travel += t_travel
        arrival = time + t_travel

        # If arriving before window start, we can wait (at current or destination equivalently)
        if arrival < friend["start_min"]:
            wait = friend["start_min"] - arrival
            total_wait += wait
            arrival = friend["start_min"]

        # Check feasibility with minimum required duration
        if arrival + friend["min_duration_min"] > friend["end_min"]:
            return None  # cannot fit the meeting

        start_meet = max(arrival, friend["start_min"])
        end_meet = start_meet + friend["min_duration_min"]

        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        time = end_meet
        location = friend["location"]

    # Return complete plan details
    return {
        "itinerary": itinerary,
        "finish_time": time,
        "total_wait": total_wait,
        "total_travel": total_travel,
        "met_count": len(order),
    }

# Explore all permutations of all subsets to maximize number of friends met,
# then choose earliest finish time, then minimal waiting, then minimal travel.
best_plan = None

# Generate all subsets and permutations
n = len(friends)
for r in range(n, 0, -1):  # prioritize larger subsets first
    for subset in itertools.permutations(friends, r):
        plan = simulate(subset)
        if plan is None:
            continue
        if best_plan is None:
            best_plan = plan
        else:
            # Compare based on goals: max met_count, earliest finish, minimal wait, minimal travel
            a = best_plan
            b = plan
            if (b["met_count"] > a["met_count"] or
               (b["met_count"] == a["met_count"] and b["finish_time"] < a["finish_time"]) or
               (b["met_count"] == a["met_count"] and b["finish_time"] == a["finish_time"] and b["total_wait"] < a["total_wait"]) or
               (b["met_count"] == a["met_count"] and b["finish_time"] == a["finish_time"] and b["total_wait"] == a["total_wait"] and b["total_travel"] < a["total_travel"])):
                best_plan = b
    if best_plan and best_plan["met_count"] == r:
        # Found at least one feasible plan for this r; since we're iterating from largest r down,
        # we can stop if this is the maximum possible (can't meet more than r).
        # But ensure we considered all permutations of this r to get optimal tie-breakers.
        # The loops above already considered all permutations for this r.
        break

# If no plan met anyone (unlikely with given constraints), output empty itinerary
result = {"itinerary": best_plan["itinerary"] if best_plan else []}

print(json.dumps(result))