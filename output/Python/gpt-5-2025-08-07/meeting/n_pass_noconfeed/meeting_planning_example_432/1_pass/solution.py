import json
import itertools

def parse_time(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters: Locations, travel times (directed, in minutes)
locations = [
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Bayview",
    "Mission District",
    "Embarcadero",
    "Financial District",
]

T = {loc: {} for loc in locations}
# Golden Gate Park
T["Golden Gate Park"]["Fisherman's Wharf"] = 24
T["Golden Gate Park"]["Bayview"] = 23
T["Golden Gate Park"]["Mission District"] = 17
T["Golden Gate Park"]["Embarcadero"] = 25
T["Golden Gate Park"]["Financial District"] = 26

# Fisherman's Wharf
T["Fisherman's Wharf"]["Golden Gate Park"] = 25
T["Fisherman's Wharf"]["Bayview"] = 26
T["Fisherman's Wharf"]["Mission District"] = 22
T["Fisherman's Wharf"]["Embarcadero"] = 8
T["Fisherman's Wharf"]["Financial District"] = 11

# Bayview
T["Bayview"]["Golden Gate Park"] = 22
T["Bayview"]["Fisherman's Wharf"] = 25
T["Bayview"]["Mission District"] = 13
T["Bayview"]["Embarcadero"] = 19
T["Bayview"]["Financial District"] = 19

# Mission District
T["Mission District"]["Golden Gate Park"] = 17
T["Mission District"]["Fisherman's Wharf"] = 22
T["Mission District"]["Bayview"] = 15
T["Mission District"]["Embarcadero"] = 19
T["Mission District"]["Financial District"] = 17

# Embarcadero
T["Embarcadero"]["Golden Gate Park"] = 25
T["Embarcadero"]["Fisherman's Wharf"] = 6
T["Embarcadero"]["Bayview"] = 21
T["Embarcadero"]["Mission District"] = 20
T["Embarcadero"]["Financial District"] = 5

# Financial District
T["Financial District"]["Golden Gate Park"] = 23
T["Financial District"]["Fisherman's Wharf"] = 10
T["Financial District"]["Bayview"] = 19
T["Financial District"]["Mission District"] = 17
T["Financial District"]["Embarcadero"] = 4

# Constraints: availability windows and minimum meeting durations
friends = [
    {
        "person": "Joseph",
        "location": "Fisherman's Wharf",
        "avail_start": parse_time("8:00"),
        "avail_end": parse_time("17:30"),
        "min_duration": 90,
    },
    {
        "person": "Jeffrey",
        "location": "Bayview",
        "avail_start": parse_time("17:30"),
        "avail_end": parse_time("21:30"),
        "min_duration": 60,
    },
    {
        "person": "Kevin",
        "location": "Mission District",
        "avail_start": parse_time("11:15"),
        "avail_end": parse_time("15:15"),
        "min_duration": 30,
    },
    {
        "person": "David",
        "location": "Embarcadero",
        "avail_start": parse_time("8:15"),
        "avail_end": parse_time("9:00"),
        "min_duration": 30,
    },
    {
        "person": "Barbara",
        "location": "Financial District",
        "avail_start": parse_time("10:30"),
        "avail_end": parse_time("16:30"),
        "min_duration": 15,
    },
]

start_location = "Golden Gate Park"
start_time = parse_time("9:00")

def evaluate_sequence(seq):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_wait = 0

    for friend in seq:
        loc = friend["location"]
        # Travel time from current location to friend's location
        if current_loc not in T or loc not in T[current_loc]:
            return None  # Missing travel path
        travel_time = T[current_loc][loc]
        arrival = current_time + travel_time
        start = max(arrival, friend["avail_start"])
        end = start + friend["min_duration"]

        if end > friend["avail_end"]:
            return None  # Cannot meet within window

        total_travel += travel_time
        total_wait += max(0, start - arrival)

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": friend["person"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end),
            "_start_min": start,
            "_end_min": end
        })

        current_loc = loc
        current_time = end

    # Return feasible plan with metrics
    last_end = itinerary[-1]["_end_min"] if itinerary else start_time
    return {
        "itinerary": itinerary,
        "num_meetings": len(itinerary),
        "end_time": last_end,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

# Explore all subsets and permutations to find optimal plan
best_plan = None
best_key = None

# Generate all subsets (sizes 1..len(friends)) and their permutations
for k in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, k):
        plan = evaluate_sequence(perm)
        if plan is None:
            continue
        # Optimization goals:
        # 1) Maximize number of meetings
        # 2) Minimize end time of last meeting
        # 3) Minimize total travel time
        # 4) Minimize total waiting time
        key = (-plan["num_meetings"], plan["end_time"], plan["total_travel"], plan["total_wait"])
        if best_key is None or key < best_key:
            best_key = key
            best_plan = plan

# Prepare JSON output
output = {"itinerary": []}
if best_plan:
    # Clean itinerary entries (remove helper fields)
    for item in best_plan["itinerary"]:
        output["itinerary"].append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"]
        })

print(json.dumps(output, ensure_ascii=False))