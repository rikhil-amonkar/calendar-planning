import json
from itertools import combinations, permutations

def parse_ampm(s):
    s = s.strip().upper()
    parts = s.replace("AM"," AM").replace("PM"," PM").split()
    if len(parts) == 2:
        time_part, ampm = parts
    else:
        # already like 'H:MMAM'
        ampm = s[-2:]
        time_part = s[:-2].strip()
    h, m = map(int, time_part.split(":"))
    if ampm == "AM":
        if h == 12:
            h = 0
    elif ampm == "PM":
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Input variables
start_location = "Bayview"
start_time = parse_ampm("9:00AM")

travel = {
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Richmond District", "Bayview"): 26,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

def ttime(a, b):
    if a == b:
        return 0
    return travel[(a, b)]

friends = [
    {
        "name": "Jessica",
        "location": "Embarcadero",
        "start": parse_ampm("4:45PM"),
        "end": parse_ampm("7:00PM"),
        "min": 30
    },
    {
        "name": "Sandra",
        "location": "Richmond District",
        "start": parse_ampm("6:30PM"),
        "end": parse_ampm("9:45PM"),
        "min": 120
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "start": parse_ampm("4:00PM"),
        "end": parse_ampm("4:45PM"),
        "min": 30
    }
]

def compute_latest_arrivals(order):
    n = len(order)
    latest = [None] * n
    # last friend
    last = order[-1]
    la = last["end"] - last["min"]
    if la < last["start"]:
        return None
    latest[-1] = la
    # backwards for previous
    for i in range(n - 2, -1, -1):
        cur = order[i]
        nxt = order[i + 1]
        depart_by = latest[i + 1] - ttime(cur["location"], nxt["location"])
        latest_start_bound = min(depart_by - cur["min"], cur["end"] - cur["min"])
        if latest_start_bound < cur["start"]:
            return None
        latest[i] = latest_start_bound
    return latest

def schedule_order(order):
    latest = compute_latest_arrivals(order)
    if latest is None:
        return None
    itinerary = []
    loc = start_location
    current_time = start_time
    total_duration = 0
    total_wait = 0
    for i, f in enumerate(order):
        travel_time = ttime(loc, f["location"])
        arrival = current_time + travel_time
        earliest_start = max(arrival, f["start"])
        # allowed end upper bound
        if i < len(order) - 1:
            next_friend = order[i + 1]
            depart_by = latest[i + 1] - ttime(f["location"], next_friend["location"])
            allowed_end_ub = min(f["end"], depart_by)
        else:
            allowed_end_ub = f["end"]
        # feasibility check considering we can delay start up to allowed_end_ub - min
        if earliest_start > allowed_end_ub - f["min"]:
            return None
        # choose start and end to maximize meeting time while keeping feasibility
        start_mt = earliest_start
        end_mt = allowed_end_ub
        # waiting (can't avoid between meetings; for first, we can leave later to avoid waiting)
        wait = max(0, start_mt - arrival)
        if i == 0:
            wait = 0
        total_wait += wait
        duration = end_mt - start_mt
        total_duration += duration
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start": start_mt,
            "end": end_mt
        })
        loc = f["location"]
        current_time = end_mt
    return {
        "itinerary": itinerary,
        "total_duration": total_duration,
        "total_wait": total_wait,
        "end_time": current_time,
        "met_count": len(order)
    }

def evaluate():
    best = None
    # Primary objective: max met_count
    # Secondary: max total_duration
    # Tertiary: min total_wait
    # Quaternary: min end_time
    n = len(friends)
    for k in range(n, 0, -1):
        for subset in combinations(friends, k):
            for order in permutations(subset):
                res = schedule_order(order)
                if res is None:
                    continue
                score = (
                    res["met_count"],
                    res["total_duration"],
                    -res["total_wait"],
                    -res["end_time"]
                )
                if best is None or score > best["score"]:
                    best = {"score": score, "res": res}
    return best["res"] if best else None

best_plan = evaluate()

output = {"itinerary": []}
if best_plan:
    for item in best_plan["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": minutes_to_str(item["start"]),
            "end_time": minutes_to_str(item["end"])
        })

print(json.dumps(output))