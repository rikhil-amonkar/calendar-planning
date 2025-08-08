import itertools
import json

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
travel = {
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Pacific Heights"): 13,
    ("Financial District", "North Beach"): 7,

    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 24,

    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "North Beach"): 3,

    ("Union Square", "Financial District"): 9,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "North Beach"): 10,

    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,

    ("Pacific Heights", "Financial District"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "North Beach"): 9,

    ("North Beach", "Financial District"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Pacific Heights"): 8,
}

# Meeting constraints
start_location = "Financial District"
arrival_time = minutes(9, 0)

friends = [
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "start": minutes(11, 0),
        "end": minutes(15, 0),
        "min_duration": 105,
    },
    {
        "name": "Karen",
        "location": "Chinatown",
        "start": minutes(13, 45),
        "end": minutes(16, 30),
        "min_duration": 15,
    },
    {
        "name": "Brian",
        "location": "Union Square",
        "start": minutes(15, 0),
        "end": minutes(17, 15),
        "min_duration": 30,
    },
    {
        "name": "Rebecca",
        "location": "Fisherman's Wharf",
        "start": minutes(8, 0),
        "end": minutes(11, 15),
        "min_duration": 30,
    },
    {
        "name": "Joseph",
        "location": "Pacific Heights",
        "start": minutes(8, 15),
        "end": minutes(9, 30),
        "min_duration": 60,
    },
    {
        "name": "Steven",
        "location": "North Beach",
        "start": minutes(14, 30),
        "end": minutes(20, 45),
        "min_duration": 120,
    },
]

def schedule_for_order(order):
    current_loc = start_location
    current_time = arrival_time
    itinerary = []
    total_wait = 0

    for f in order:
        tkey = (current_loc, f["location"])
        if tkey not in travel:
            return None  # missing travel time
        arrive = current_time + travel[tkey]
        start = max(arrive, f["start"])
        end = start + f["min_duration"]
        if end > f["end"]:
            return None  # infeasible
        wait = max(0, start - arrive)
        total_wait += wait
        itinerary.append({
            "action": "meet",
            "location": f["location"],
            "person": f["name"],
            "start_time_min": start,
            "end_time_min": end,
        })
        current_loc = f["location"]
        current_time = end

    return {
        "itinerary": itinerary,
        "wait": total_wait,
        "finish": current_time,
        "count": len(order),
        "order_names": [f["name"] for f in order],
    }

def optimize_schedule(friends):
    best = None
    n = len(friends)
    # evaluate all partial permutations
    for k in range(1, n + 1):
        for perm in itertools.permutations(friends, k):
            sched = schedule_for_order(perm)
            if sched is None:
                continue
            if best is None:
                best = sched
            else:
                # Primary: maximize number of friends met
                if sched["count"] > best["count"]:
                    best = sched
                elif sched["count"] == best["count"]:
                    # Secondary: minimize total waiting time
                    if sched["wait"] < best["wait"]:
                        best = sched
                    elif sched["wait"] == best["wait"]:
                        # Tertiary: earliest finishing time
                        if sched["finish"] < best["finish"]:
                            best = sched
                        elif sched["finish"] == best["finish"]:
                            # Quaternary: lexicographically smallest order of names
                            if sched["order_names"] < best["order_names"]:
                                best = sched
    return best

best_schedule = optimize_schedule(friends)

output = {"itinerary": []}
if best_schedule:
    for item in best_schedule["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start_time_min"]),
            "end_time": fmt_time(item["end_time_min"]),
        })

print(json.dumps(output, ensure_ascii=False))