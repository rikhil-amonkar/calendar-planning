import itertools, json

def to_minutes(t):
    # t like '9:00', '11:45', '21:30'
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(m):
    return f"{m//60}:{m%60:02d}"

# Input data
start_location = "Union Square"
arrival_time = to_minutes("9:00")

# Travel times (minutes)
travel = {
    "Union Square": {
        "Golden Gate Park": 22,
        "Pacific Heights": 15,
        "Presidio": 24,
        "Chinatown": 7,
        "The Castro": 19,
    },
    "Golden Gate Park": {
        "Union Square": 22,
        "Pacific Heights": 16,
        "Presidio": 11,
        "Chinatown": 23,
        "The Castro": 13,
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Presidio": 11,
        "Chinatown": 11,
        "The Castro": 16,
    },
    "Presidio": {
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Pacific Heights": 11,
        "Chinatown": 21,
        "The Castro": 21,
    },
    "Chinatown": {
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Pacific Heights": 10,
        "Presidio": 19,
        "The Castro": 22,
    },
    "The Castro": {
        "Union Square": 19,
        "Golden Gate Park": 11,
        "Pacific Heights": 16,
        "Presidio": 20,
        "Chinatown": 20,
    },
}

# Friends constraints
people = {
    "Andrew": {
        "location": "Golden Gate Park",
        "start": to_minutes("11:45"),
        "end": to_minutes("14:30"),
        "min": 75,
    },
    "Sarah": {
        "location": "Pacific Heights",
        "start": to_minutes("16:15"),
        "end": to_minutes("18:45"),
        "min": 15,
    },
    "Nancy": {
        "location": "Presidio",
        "start": to_minutes("17:30"),
        "end": to_minutes("19:15"),
        "min": 60,
    },
    "Rebecca": {
        "location": "Chinatown",
        "start": to_minutes("9:45"),
        "end": to_minutes("21:30"),
        "min": 90,
    },
    "Robert": {
        "location": "The Castro",
        "start": to_minutes("8:30"),
        "end": to_minutes("14:15"),
        "min": 30,
    },
}

names = ["Andrew", "Sarah", "Nancy", "Rebecca", "Robert"]

def evaluate_order(order):
    # Build minimal feasible schedule for this order
    curr_loc = start_location
    curr_time = arrival_time
    schedule = []
    total_travel = 0

    for person in order:
        loc = people[person]["location"]
        # travel time
        t = travel[curr_loc][loc]
        total_travel += t
        arrival = curr_time + t
        start = max(arrival, people[person]["start"])
        end = start + people[person]["min"]
        if end > people[person]["end"]:
            return None  # infeasible
        schedule.append({
            "person": person,
            "location": loc,
            "start": start,
            "end": end
        })
        curr_loc = loc
        curr_time = end

    # Greedy extensions to fill waiting gaps without harming feasibility of next meetings
    for i in range(len(schedule) - 1):
        a = schedule[i]
        b = schedule[i + 1]
        loc_a = people[a["person"]]["location"]
        loc_b = people[b["person"]]["location"]
        t_ab = travel[loc_a][loc_b]
        # If leaving at a["end"], arrival at b is:
        arrival_next = a["end"] + t_ab
        earliest_b = max(arrival_next, people[b["person"]]["start"])
        slack = earliest_b - arrival_next
        # Extend meeting a by up to slack, bounded by their availability
        max_ext_a = people[a["person"]]["end"] - a["end"]
        ext = min(slack, max_ext_a)
        if ext > 0:
            a["end"] += ext
            # start/end of b remain feasible as planned (arrival becomes earliest_b)

    # Extend final meeting to end of availability to maximize total meeting time
    if schedule:
        last = schedule[-1]
        last["end"] = min(people[last["person"]]["end"], last["end"])

    # Compute score components
    total_meeting = sum(item["end"] - item["start"] for item in schedule)
    finish_time = schedule[-1]["end"] if schedule else arrival_time

    return {
        "schedule": schedule,
        "score": (len(schedule), total_meeting, -total_travel, -finish_time),
        "total_travel": total_travel,
    }

best = None

# Enumerate all subsets and permutations to find optimal
for r in range(len(names), 0, -1):
    for order in itertools.permutations(names, r):
        res = evaluate_order(order)
        if res is None:
            continue
        if best is None or res["score"] > best["score"]:
            best = res

# Prepare output
itinerary = []
if best:
    for item in best["schedule"]:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"]),
        })

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))