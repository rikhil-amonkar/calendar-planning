import itertools
import json

def parse_time_12h(t):
    # t like '1:45PM' or '9:00AM'
    t = t.strip().upper()
    if t.endswith('AM'):
        ampm = 'AM'
        tcore = t[:-2].strip()
    elif t.endswith('PM'):
        ampm = 'PM'
        tcore = t[:-2].strip()
    else:
        raise ValueError(f"Time must end with AM/PM: {t}")
    if ':' in tcore:
        h_str, m_str = tcore.split(':')
    else:
        h_str, m_str = tcore, '00'
    h = int(h_str)
    m = int(m_str)
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_hhmm(tmin):
    h = (tmin // 60) % 24
    m = tmin % 60
    return f"{h}:{m:02d}"

# Input variables (constraints)
start_location = "Presidio"
arrival_time_str = "9:00AM"

friends = [
    {"name": "Jessica", "location": "Golden Gate Park", "start": "1:45PM", "end": "3:00PM", "min_minutes": 30},
    {"name": "Ashley", "location": "Bayview", "start": "5:15PM", "end": "8:00PM", "min_minutes": 105},
    {"name": "Ronald", "location": "Chinatown", "start": "7:15AM", "end": "2:45PM", "min_minutes": 90},
    {"name": "William", "location": "North Beach", "start": "1:15PM", "end": "8:15PM", "min_minutes": 15},
    {"name": "Daniel", "location": "Mission District", "start": "7:00AM", "end": "11:15AM", "min_minutes": 105},
]

# Convert friend windows to minutes
for f in friends:
    f["start_min"] = parse_time_12h(f["start"])
    f["end_min"] = parse_time_12h(f["end"])

start_time_min = parse_time_12h(arrival_time_str)

# Travel times matrix (minutes), as provided (asymmetric allowed)
travel = {
    "Presidio": {
        "Golden Gate Park": 12,
        "Bayview": 31,
        "Chinatown": 21,
        "North Beach": 18,
        "Mission District": 26,
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Bayview": 23,
        "Chinatown": 23,
        "North Beach": 24,
        "Mission District": 17,
    },
    "Bayview": {
        "Presidio": 31,
        "Golden Gate Park": 22,
        "Chinatown": 18,
        "North Beach": 21,
        "Mission District": 13,
    },
    "Chinatown": {
        "Presidio": 19,
        "Golden Gate Park": 23,
        "Bayview": 22,
        "North Beach": 3,
        "Mission District": 18,
    },
    "North Beach": {
        "Presidio": 17,
        "Golden Gate Park": 22,
        "Bayview": 22,
        "Chinatown": 6,
        "Mission District": 18,
    },
    "Mission District": {
        "Presidio": 25,
        "Golden Gate Park": 17,
        "Bayview": 15,
        "Chinatown": 16,
        "North Beach": 17,
    },
}

# Add zero travel to same location
locations = set(travel.keys())
for a in list(locations):
    travel[a][a] = 0

def get_travel_time(a, b):
    if a in travel and b in travel[a]:
        return travel[a][b]
    # If missing, assume very large/unreachable to avoid using it
    return 10**9

def build_schedule(order):
    # order: list of friend dicts
    loc = start_location
    t = start_time_min
    itinerary = []
    total_travel = 0
    total_wait = 0

    for f in order:
        tr = get_travel_time(loc, f["location"])
        if tr >= 10**9:
            return None  # invalid path
        arrive = t + tr
        meet_start = max(arrive, f["start_min"])
        meet_end = meet_start + f["min_minutes"]
        # feasibility check
        if meet_end > f["end_min"]:
            return None
        # update accumulators
        total_travel += tr
        wait = max(0, meet_start - arrive)
        total_wait += wait
        # append itinerary entry
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time": minutes_to_hhmm(meet_start),
            "end_time": minutes_to_hhmm(meet_end),
            "_start_min": meet_start,  # internal for tie-breaks
            "_end_min": meet_end,
        })
        # advance
        t = meet_end
        loc = f["location"]

    return {
        "itinerary": itinerary,
        "finish_time": t,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "count": len(order),
    }

def optimize_schedule(friends):
    best = None
    n = len(friends)
    # Try largest number of meetings down to 1
    for k in range(n, 0, -1):
        feasible_schedules = []
        for order in itertools.permutations(friends, k):
            sched = build_schedule(order)
            if sched is not None:
                feasible_schedules.append(sched)
        if feasible_schedules:
            # Choose best by:
            # 1) earliest finish_time
            # 2) minimal total_wait
            # 3) minimal total_travel
            # 4) lexicographically smallest person order (for determinism)
            def keyfun(s):
                persons = [i["person"] for i in s["itinerary"]]
                return (s["finish_time"], s["total_wait"], s["total_travel"], persons)
            best = min(feasible_schedules, key=keyfun)
            break
    return best

best_schedule = optimize_schedule(friends)

# Prepare output: remove internal fields
output_itinerary = []
if best_schedule:
    for item in best_schedule["itinerary"]:
        output_itinerary.append({
            "action": item["action"],
            "location": item["location"],
            "person": item["person"],
            "start_time": item["start_time"],
            "end_time": item["end_time"],
        })

result = {
    "itinerary": output_itinerary
}

print(json.dumps(result, ensure_ascii=False))