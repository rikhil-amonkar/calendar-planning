import json
import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables
start_location = "Russian Hill"
start_time_str = "9:00"
start_time = time_to_minutes(start_time_str)

# Travel times (in minutes)
travel = {
    "Russian Hill": {
        "Presidio": 14, "Chinatown": 9, "Pacific Heights": 7, "Richmond District": 14,
        "Fisherman's Wharf": 7, "Golden Gate Park": 21, "Bayview": 23
    },
    "Presidio": {
        "Russian Hill": 14, "Chinatown": 21, "Pacific Heights": 11, "Richmond District": 7,
        "Fisherman's Wharf": 19, "Golden Gate Park": 12, "Bayview": 31
    },
    "Chinatown": {
        "Russian Hill": 7, "Presidio": 19, "Pacific Heights": 10, "Richmond District": 20,
        "Fisherman's Wharf": 8, "Golden Gate Park": 23, "Bayview": 22
    },
    "Pacific Heights": {
        "Russian Hill": 7, "Presidio": 11, "Chinatown": 11, "Richmond District": 12,
        "Fisherman's Wharf": 13, "Golden Gate Park": 15, "Bayview": 22
    },
    "Richmond District": {
        "Russian Hill": 13, "Presidio": 7, "Chinatown": 20, "Pacific Heights": 10,
        "Fisherman's Wharf": 18, "Golden Gate Park": 9, "Bayview": 26
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7, "Presidio": 17, "Chinatown": 12, "Pacific Heights": 12,
        "Richmond District": 18, "Golden Gate Park": 25, "Bayview": 26
    },
    "Golden Gate Park": {
        "Russian Hill": 19, "Presidio": 11, "Chinatown": 23, "Pacific Heights": 16,
        "Richmond District": 7, "Fisherman's Wharf": 24, "Bayview": 23
    },
    "Bayview": {
        "Russian Hill": 23, "Presidio": 31, "Chinatown": 18, "Pacific Heights": 23,
        "Richmond District": 25, "Fisherman's Wharf": 25, "Golden Gate Park": 22
    }
}

# People constraints
people = [
    {
        "name": "Matthew",
        "location": "Presidio",
        "start": time_to_minutes("11:00"),
        "end": time_to_minutes("21:00"),
        "min_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "start": time_to_minutes("9:15"),
        "end": time_to_minutes("18:45"),
        "min_duration": 90
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": time_to_minutes("14:15"),
        "end": time_to_minutes("17:00"),
        "min_duration": 15
    },
    {
        "name": "Helen",
        "location": "Richmond District",
        "start": time_to_minutes("19:45"),
        "end": time_to_minutes("22:00"),
        "min_duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": time_to_minutes("21:15"),
        "end": time_to_minutes("22:15"),
        "min_duration": 60
    },
    {
        "name": "Kimberly",
        "location": "Golden Gate Park",
        "start": time_to_minutes("13:00"),
        "end": time_to_minutes("16:30"),
        "min_duration": 120
    },
    {
        "name": "Kenneth",
        "location": "Bayview",
        "start": time_to_minutes("14:30"),
        "end": time_to_minutes("18:00"),
        "min_duration": 60
    }
]

# Build a mapping for quick access
name_to_person = {p["name"]: p for p in people}
names = [p["name"] for p in people]

def simulate_schedule(order):
    current_time = start_time
    current_loc = start_location
    itinerary = []
    total_travel = 0
    total_wait = 0

    for name in order:
        p = name_to_person[name]
        # travel time from current location to person's location
        if current_loc not in travel or p["location"] not in travel[current_loc]:
            return None  # invalid travel mapping
        t_travel = travel[current_loc][p["location"]]
        arrive_time = current_time + t_travel
        start_meet = max(arrive_time, p["start"])
        wait = max(0, start_meet - arrive_time)
        end_meet = start_meet + p["min_duration"]

        if end_meet > p["end"]:
            return None  # cannot meet within window

        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(end_meet)
        })

        # update state
        total_travel += t_travel
        total_wait += wait
        current_time = end_meet
        current_loc = p["location"]

    final_end = current_time
    return {
        "itinerary": itinerary,
        "final_end": final_end,
        "total_travel": total_travel,
        "total_wait": total_wait
    }

best_plan = None
best_score = None  # tuple for comparison

# Explore all subsets and permutations
for k in range(len(names), -1, -1):  # start from largest to smallest to allow early pruning
    found_for_k = False
    for order in itertools.permutations(names, k):
        result = simulate_schedule(order)
        if result is None:
            continue
        # Score: maximize number met, then earliest final end, then minimal total travel, then minimal total wait
        score = (k, -result["final_end"], -(-result["total_travel"]), -(-result["total_wait"]))
        if best_score is None or score > best_score:
            best_score = score
            best_plan = result
            found_for_k = True
    if found_for_k:
        # since we iterate k from high to low, first k with feasible plan is maximal count
        # but we still explored all permutations of this k to optimize tie-breakers
        pass

# Output JSON
output = {"itinerary": best_plan["itinerary"] if best_plan else []}
print(json.dumps(output, ensure_ascii=False))