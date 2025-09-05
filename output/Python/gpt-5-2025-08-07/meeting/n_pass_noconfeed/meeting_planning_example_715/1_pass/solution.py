import json

# Helper functions
def parse_time_12h(tstr):
    # Expects format like '9:00AM' or '2:45PM'
    tstr = tstr.strip().upper()
    if tstr.endswith('AM'):
        ampm = 'AM'
        t = tstr[:-2]
    elif tstr.endswith('PM'):
        ampm = 'PM'
        t = tstr[:-2]
    else:
        raise ValueError(f"Time must end with AM or PM: {tstr}")
    h, m = t.split(':')
    h = int(h)
    m = int(m)
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times (directed, in minutes)
travel = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9
    }
}

# Input variables (availability windows and minimum meeting durations)
arrival_location = "Presidio"
arrival_time = parse_time_12h("9:00AM")

people = [
    {
        "name": "Amanda",
        "location": "Marina District",
        "start": parse_time_12h("2:45PM"),
        "end": parse_time_12h("7:30PM"),
        "min": 105
    },
    {
        "name": "Melissa",
        "location": "The Castro",
        "start": parse_time_12h("9:30AM"),
        "end": parse_time_12h("5:00PM"),
        "min": 30
    },
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "start": parse_time_12h("12:45PM"),
        "end": parse_time_12h("6:45PM"),
        "min": 120
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "start": parse_time_12h("10:15AM"),
        "end": parse_time_12h("1:15PM"),
        "min": 30
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": parse_time_12h("5:00PM"),
        "end": parse_time_12h("9:30PM"),
        "min": 105
    },
    {
        "name": "Karen",
        "location": "Mission District",
        "start": parse_time_12h("5:30PM"),
        "end": parse_time_12h("8:30PM"),
        "min": 105
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "start": parse_time_12h("11:15AM"),
        "end": parse_time_12h("5:30PM"),
        "min": 120
    },
    {
        "name": "Joseph",
        "location": "Golden Gate Park",
        "start": parse_time_12h("8:30AM"),
        "end": parse_time_12h("9:15PM"),
        "min": 105
    }
]

# Build a quick lookup for remaining max bound (simple upper bound = count of remaining)
def better_solution(a, b):
    # a and b are dicts with keys: count, end_time, travel, wait, itinerary
    if a is None:
        return True
    if b is None:
        return False
    # Maximize count
    if b["count"] != a["count"]:
        return b["count"] > a["count"]
    # Minimize end time
    if b["end_time"] != a["end_time"]:
        return b["end_time"] < a["end_time"]
    # Minimize total travel
    if b["travel"] != a["travel"]:
        return b["travel"] < a["travel"]
    # Minimize total waiting
    if b["wait"] != a["wait"]:
        return b["wait"] < a["wait"]
    return False

best = None

def dfs(current_loc, current_time, remaining, itinerary, total_travel, total_wait):
    global best

    # Evaluate current partial solution (stopping option)
    current_solution = {
        "count": len(itinerary),
        "end_time": current_time,
        "travel": total_travel,
        "wait": total_wait,
        "itinerary": itinerary
    }
    if better_solution(best, current_solution):
        best = current_solution

    # Simple upper bound pruning: even if we met everyone remaining, can we beat best?
    if best is not None:
        if len(itinerary) + len(remaining) < best["count"]:
            return

    # Try each remaining person as next meeting
    for idx, person in enumerate(remaining):
        # Travel time
        if current_loc not in travel or person["location"] not in travel[current_loc]:
            continue  # No route defined; skip
        t = travel[current_loc][person["location"]]
        arrival = current_time + t
        start = max(arrival, person["start"])
        end = start + person["min"]
        if end <= person["end"]:
            wait_time = max(0, person["start"] - arrival) if arrival < person["start"] else 0
            new_meet = {
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": fmt_time(start),
                "end_time": fmt_time(end)
            }
            new_remaining = remaining[:idx] + remaining[idx+1:]
            dfs(
                person["location"],
                end,
                new_remaining,
                itinerary + [new_meet],
                total_travel + t,
                total_wait + wait_time
            )

# Start search
dfs(arrival_location, arrival_time, people, [], 0, 0)

# Prepare output JSON
output = {
    "itinerary": best["itinerary"] if best else []
}

print(json.dumps(output, ensure_ascii=False))