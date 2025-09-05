# SOLUTION:
import json
from math import inf

def parse_time_12h(t):
    # Expects formats like '9:00AM', '2:15PM'
    t = t.strip().upper()
    ampm = t[-2:]
    h, m = t[:-2].split(':')
    h = int(h)
    m = int(m)
    if ampm == 'AM':
        if h == 12:
            h = 0
    elif ampm == 'PM':
        if h != 12:
            h += 12
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (constraints and travel times)
locations = [
    "Chinatown",
    "Mission District",
    "Alamo Square",
    "Pacific Heights",
    "Union Square",
    "Golden Gate Park",
    "Sunset District",
    "Presidio",
]

# Directed travel times in minutes
travel = {
    "Chinatown": {
        "Chinatown": 0,
        "Mission District": 18,
        "Alamo Square": 17,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Golden Gate Park": 23,
        "Sunset District": 29,
        "Presidio": 19,
    },
    "Mission District": {
        "Chinatown": 16,
        "Mission District": 0,
        "Alamo Square": 11,
        "Pacific Heights": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Sunset District": 24,
        "Presidio": 25,
    },
    "Alamo Square": {
        "Chinatown": 16,
        "Mission District": 10,
        "Alamo Square": 0,
        "Pacific Heights": 10,
        "Union Square": 14,
        "Golden Gate Park": 9,
        "Sunset District": 16,
        "Presidio": 18,
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Mission District": 15,
        "Alamo Square": 10,
        "Pacific Heights": 0,
        "Union Square": 12,
        "Golden Gate Park": 15,
        "Sunset District": 21,
        "Presidio": 11,
    },
    "Union Square": {
        "Chinatown": 7,
        "Mission District": 14,
        "Alamo Square": 15,
        "Pacific Heights": 15,
        "Union Square": 0,
        "Golden Gate Park": 22,
        "Sunset District": 26,
        "Presidio": 24,
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Mission District": 17,
        "Alamo Square": 10,
        "Pacific Heights": 16,
        "Union Square": 22,
        "Golden Gate Park": 0,
        "Sunset District": 10,
        "Presidio": 11,
    },
    "Sunset District": {
        "Chinatown": 30,
        "Mission District": 24,
        "Alamo Square": 17,
        "Pacific Heights": 21,
        "Union Square": 30,
        "Golden Gate Park": 11,
        "Sunset District": 0,
        "Presidio": 16,
    },
    "Presidio": {
        "Chinatown": 21,
        "Mission District": 26,
        "Alamo Square": 18,
        "Pacific Heights": 11,
        "Union Square": 22,
        "Golden Gate Park": 12,
        "Sunset District": 15,
        "Presidio": 0,
    },
}

# Friends' availability and required minimum meeting durations
friends = [
    {
        "name": "David",
        "location": "Mission District",
        "start": parse_time_12h("8:00AM"),
        "end": parse_time_12h("7:45PM"),
        "duration": 45,
    },
    {
        "name": "Kenneth",
        "location": "Alamo Square",
        "start": parse_time_12h("2:00PM"),
        "end": parse_time_12h("7:45PM"),
        "duration": 120,
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "start": parse_time_12h("5:00PM"),
        "end": parse_time_12h("8:00PM"),
        "duration": 15,
    },
    {
        "name": "Charles",
        "location": "Union Square",
        "start": parse_time_12h("9:45PM"),
        "end": parse_time_12h("10:45PM"),
        "duration": 60,
    },
    {
        "name": "Deborah",
        "location": "Golden Gate Park",
        "start": parse_time_12h("7:00AM"),
        "end": parse_time_12h("6:15PM"),
        "duration": 90,
    },
    {
        "name": "Karen",
        "location": "Sunset District",
        "start": parse_time_12h("5:45PM"),
        "end": parse_time_12h("9:15PM"),
        "duration": 15,
    },
    {
        "name": "Carol",
        "location": "Presidio",
        "start": parse_time_12h("8:15AM"),
        "end": parse_time_12h("9:15AM"),
        "duration": 30,
    },
]

start_location = "Chinatown"
start_time = parse_time_12h("9:00AM")

# DFS search to maximize the number of friends met; tie-break with end time, then waiting, then travel
best_solution = {
    "count": -1,
    "end_time": inf,
    "wait": inf,
    "travel": inf,
    "itinerary": [],
}

def dfs(current_loc, current_time, visited_mask, itinerary, total_wait, total_travel):
    global best_solution

    # Update best solution at every node (even partial)
    count = len(itinerary)
    end_time = current_time

    def better(sol_a, sol_b):
        # True if sol_a is better than sol_b
        if sol_a["count"] != sol_b["count"]:
            return sol_a["count"] > sol_b["count"]
        if sol_a["end_time"] != sol_b["end_time"]:
            return sol_a["end_time"] < sol_b["end_time"]
        if sol_a["wait"] != sol_b["wait"]:
            return sol_a["wait"] < sol_b["wait"]
        if sol_a["travel"] != sol_b["travel"]:
            return sol_a["travel"] < sol_b["travel"]
        return False

    current_solution = {
        "count": count,
        "end_time": end_time,
        "wait": total_wait,
        "travel": total_travel,
        "itinerary": itinerary[:],
    }
    if better(current_solution, best_solution):
        best_solution = current_solution

    # Upper bound prune: if even meeting all remaining cannot beat best, stop
    remaining = len(friends) - bin(visited_mask).count("1")
    if count + remaining < best_solution["count"]:
        return

    # Try to meet each unvisited friend next
    for i, f in enumerate(friends):
        if (visited_mask >> i) & 1:
            continue
        # Travel time to friend's location
        if current_loc not in travel or f["location"] not in travel[current_loc]:
            continue  # safety
        t_travel = travel[current_loc][f["location"]]
        arrival = current_time + t_travel
        start_meet = max(arrival, f["start"])
        finish_meet = start_meet + f["duration"]
        if finish_meet <= f["end"]:
            wait_here = max(0, f["start"] - arrival)
            new_itinerary = itinerary + [{
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": start_meet,
                "end_time": finish_meet,
            }]
            dfs(
                f["location"],
                finish_meet,
                visited_mask | (1 << i),
                new_itinerary,
                total_wait + wait_here,
                total_travel + t_travel
            )
        else:
            # Not feasible to meet this friend next; skip
            continue

# Run search
dfs(start_location, start_time, 0, [], 0, 0)

# Prepare JSON output
output_itinerary = []
for item in best_solution["itinerary"]:
    output_itinerary.append({
        "action": item["action"],
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start_time"]),
        "end_time": fmt_time(item["end_time"]),
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False))