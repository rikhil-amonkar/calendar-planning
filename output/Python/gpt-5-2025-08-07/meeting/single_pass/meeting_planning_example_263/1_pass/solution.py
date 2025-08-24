import json
import itertools

def parse_time(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        time_part = s[:-2]
        h, m = map(int, time_part.split(":"))
        if ampm == "AM":
            if h == 12:
                h = 0
        else:
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        h, m = map(int, s.split(":"))
        return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Bayview"
start_time_str = "9:00AM"

people = {
    "Betty": {
        "location": "Embarcadero",
        "available_start": parse_time("7:45PM"),
        "available_end": parse_time("9:45PM"),
        "min_duration": 15
    },
    "Karen": {
        "location": "Fisherman's Wharf",
        "available_start": parse_time("8:45AM"),
        "available_end": parse_time("3:00PM"),
        "min_duration": 30
    },
    "Anthony": {
        "location": "Financial District",
        "available_start": parse_time("9:15AM"),
        "available_end": parse_time("9:30PM"),
        "min_duration": 105
    },
}

# Travel times in minutes
travel = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Financial District"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Financial District"): 5,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Fisherman's Wharf"): 10,
}

def travel_time(a, b):
    return travel[(a, b)]

def simulate_order(order):
    current_loc = start_location
    current_time = parse_time(start_time_str)
    itinerary = []
    total_wait = 0
    total_travel = 0

    for name in order:
        loc = people[name]["location"]
        avail_start = people[name]["available_start"]
        avail_end = people[name]["available_end"]
        min_dur = people[name]["min_duration"]

        # travel to person's location
        t_travel = travel_time(current_loc, loc)
        arrival = current_time + t_travel
        total_travel += t_travel

        # wait until available
        start_meet = max(arrival, avail_start)
        wait = max(0, start_meet - arrival)
        total_wait += wait

        end_meet = start_meet + min_dur

        # check feasibility within availability window
        if end_meet > avail_end:
            return None  # infeasible

        # add meeting
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        # update state
        current_loc = loc
        current_time = end_meet

    last_end = current_time
    return {
        "itinerary": itinerary,
        "count": len(order),
        "end_time": last_end,
        "total_wait": total_wait,
        "total_travel": total_travel
    }

def better(a, b):
    # Return True if a is better than b
    if b is None:
        return True
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["end_time"] != b["end_time"]:
        return a["end_time"] < b["end_time"]
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    # Tie-breaker: lexicographically smaller itinerary string
    a_str = json.dumps(a["itinerary"], sort_keys=True)
    b_str = json.dumps(b["itinerary"], sort_keys=True)
    return a_str < b_str

names = list(people.keys())
best = None

# Try all subsets by size (maximize number of meetings)
for r in range(len(names), 0, -1):
    for subset in itertools.combinations(names, r):
        for perm in itertools.permutations(subset):
            plan = simulate_order(perm)
            if plan and better(plan, best):
                best = plan
    if best and best["count"] == r:
        # Found best possible for this r; since we go from max r downwards, we can break if feasible
        break

output = {"itinerary": best["itinerary"] if best else []}

print("SOLUTION:")
print(json.dumps(output, ensure_ascii=False, indent=2))