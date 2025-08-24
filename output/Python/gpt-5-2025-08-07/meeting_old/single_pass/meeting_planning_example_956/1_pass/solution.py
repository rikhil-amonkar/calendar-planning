import json

# Helper functions
def t2m(s):
    h, m = map(int, s.split(":"))
    return h * 60 + m

def m2t(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Build directed travel time matrix
locs = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park",
]

dist = {a: {} for a in locs}
def set_dist(a, b, minutes):
    dist[a][b] = minutes

# Fill distances as given
set_dist("The Castro", "Alamo Square", 8)
set_dist("The Castro", "Richmond District", 16)
set_dist("The Castro", "Financial District", 21)
set_dist("The Castro", "Union Square", 19)
set_dist("The Castro", "Fisherman's Wharf", 24)
set_dist("The Castro", "Marina District", 21)
set_dist("The Castro", "Haight-Ashbury", 6)
set_dist("The Castro", "Mission District", 7)
set_dist("The Castro", "Pacific Heights", 16)
set_dist("The Castro", "Golden Gate Park", 11)

set_dist("Alamo Square", "The Castro", 8)
set_dist("Alamo Square", "Richmond District", 11)
set_dist("Alamo Square", "Financial District", 17)
set_dist("Alamo Square", "Union Square", 14)
set_dist("Alamo Square", "Fisherman's Wharf", 19)
set_dist("Alamo Square", "Marina District", 15)
set_dist("Alamo Square", "Haight-Ashbury", 5)
set_dist("Alamo Square", "Mission District", 10)
set_dist("Alamo Square", "Pacific Heights", 10)
set_dist("Alamo Square", "Golden Gate Park", 9)

set_dist("Richmond District", "The Castro", 16)
set_dist("Richmond District", "Alamo Square", 13)
set_dist("Richmond District", "Financial District", 22)
set_dist("Richmond District", "Union Square", 21)
set_dist("Richmond District", "Fisherman's Wharf", 18)
set_dist("Richmond District", "Marina District", 9)
set_dist("Richmond District", "Haight-Ashbury", 10)
set_dist("Richmond District", "Mission District", 20)
set_dist("Richmond District", "Pacific Heights", 10)
set_dist("Richmond District", "Golden Gate Park", 9)

set_dist("Financial District", "The Castro", 20)
set_dist("Financial District", "Alamo Square", 17)
set_dist("Financial District", "Richmond District", 21)
set_dist("Financial District", "Union Square", 9)
set_dist("Financial District", "Fisherman's Wharf", 10)
set_dist("Financial District", "Marina District", 15)
set_dist("Financial District", "Haight-Ashbury", 19)
set_dist("Financial District", "Mission District", 17)
set_dist("Financial District", "Pacific Heights", 13)
set_dist("Financial District", "Golden Gate Park", 23)

set_dist("Union Square", "The Castro", 17)
set_dist("Union Square", "Alamo Square", 15)
set_dist("Union Square", "Richmond District", 20)
set_dist("Union Square", "Financial District", 9)
set_dist("Union Square", "Fisherman's Wharf", 15)
set_dist("Union Square", "Marina District", 18)
set_dist("Union Square", "Haight-Ashbury", 18)
set_dist("Union Square", "Mission District", 14)
set_dist("Union Square", "Pacific Heights", 15)
set_dist("Union Square", "Golden Gate Park", 22)

set_dist("Fisherman's Wharf", "The Castro", 27)
set_dist("Fisherman's Wharf", "Alamo Square", 21)
set_dist("Fisherman's Wharf", "Richmond District", 18)
set_dist("Fisherman's Wharf", "Financial District", 11)
set_dist("Fisherman's Wharf", "Union Square", 13)
set_dist("Fisherman's Wharf", "Marina District", 9)
set_dist("Fisherman's Wharf", "Haight-Ashbury", 22)
set_dist("Fisherman's Wharf", "Mission District", 22)
set_dist("Fisherman's Wharf", "Pacific Heights", 12)
set_dist("Fisherman's Wharf", "Golden Gate Park", 25)

set_dist("Marina District", "The Castro", 22)
set_dist("Marina District", "Alamo Square", 15)
set_dist("Marina District", "Richmond District", 11)
set_dist("Marina District", "Financial District", 17)
set_dist("Marina District", "Union Square", 16)
set_dist("Marina District", "Fisherman's Wharf", 10)
set_dist("Marina District", "Haight-Ashbury", 16)
set_dist("Marina District", "Mission District", 20)
set_dist("Marina District", "Pacific Heights", 7)
set_dist("Marina District", "Golden Gate Park", 18)

set_dist("Haight-Ashbury", "The Castro", 6)
set_dist("Haight-Ashbury", "Alamo Square", 5)
set_dist("Haight-Ashbury", "Richmond District", 10)
set_dist("Haight-Ashbury", "Financial District", 21)
set_dist("Haight-Ashbury", "Union Square", 19)
set_dist("Haight-Ashbury", "Fisherman's Wharf", 23)
set_dist("Haight-Ashbury", "Marina District", 17)
set_dist("Haight-Ashbury", "Mission District", 11)
set_dist("Haight-Ashbury", "Pacific Heights", 12)
set_dist("Haight-Ashbury", "Golden Gate Park", 7)

set_dist("Mission District", "The Castro", 7)
set_dist("Mission District", "Alamo Square", 11)
set_dist("Mission District", "Richmond District", 20)
set_dist("Mission District", "Financial District", 15)
set_dist("Mission District", "Union Square", 15)
set_dist("Mission District", "Fisherman's Wharf", 22)
set_dist("Mission District", "Marina District", 19)
set_dist("Mission District", "Haight-Ashbury", 12)
set_dist("Mission District", "Pacific Heights", 16)
set_dist("Mission District", "Golden Gate Park", 17)

set_dist("Pacific Heights", "The Castro", 16)
set_dist("Pacific Heights", "Alamo Square", 10)
set_dist("Pacific Heights", "Richmond District", 12)
set_dist("Pacific Heights", "Financial District", 13)
set_dist("Pacific Heights", "Union Square", 12)
set_dist("Pacific Heights", "Fisherman's Wharf", 13)
set_dist("Pacific Heights", "Marina District", 6)
set_dist("Pacific Heights", "Haight-Ashbury", 11)
set_dist("Pacific Heights", "Mission District", 15)
set_dist("Pacific Heights", "Golden Gate Park", 15)

set_dist("Golden Gate Park", "The Castro", 13)
set_dist("Golden Gate Park", "Alamo Square", 9)
set_dist("Golden Gate Park", "Richmond District", 7)
set_dist("Golden Gate Park", "Financial District", 26)
set_dist("Golden Gate Park", "Union Square", 22)
set_dist("Golden Gate Park", "Fisherman's Wharf", 24)
set_dist("Golden Gate Park", "Marina District", 16)
set_dist("Golden Gate Park", "Haight-Ashbury", 7)
set_dist("Golden Gate Park", "Mission District", 17)
set_dist("Golden Gate Park", "Pacific Heights", 16)

# People constraints
people = [
    {"name": "William", "location": "Alamo Square", "start": t2m("15:15"), "end": t2m("17:15"), "min": 60},
    {"name": "Joshua", "location": "Richmond District", "start": t2m("7:00"), "end": t2m("20:00"), "min": 15},
    {"name": "Joseph", "location": "Financial District", "start": t2m("11:15"), "end": t2m("13:30"), "min": 15},
    {"name": "David", "location": "Union Square", "start": t2m("16:45"), "end": t2m("19:15"), "min": 45},
    {"name": "Brian", "location": "Fisherman's Wharf", "start": t2m("13:45"), "end": t2m("20:45"), "min": 105},
    {"name": "Karen", "location": "Marina District", "start": t2m("11:30"), "end": t2m("18:30"), "min": 15},
    {"name": "Anthony", "location": "Haight-Ashbury", "start": t2m("7:15"), "end": t2m("10:30"), "min": 30},
    {"name": "Matthew", "location": "Mission District", "start": t2m("17:15"), "end": t2m("19:15"), "min": 120},
    {"name": "Helen", "location": "Pacific Heights", "start": t2m("8:00"), "end": t2m("12:00"), "min": 75},
    {"name": "Jeffrey", "location": "Golden Gate Park", "start": t2m("19:00"), "end": t2m("21:30"), "min": 60},
]

# Index people by name for convenience
people_by_name = {p["name"]: p for p in people}

start_location = "The Castro"
start_time = t2m("9:00")

# DFS to find optimal itinerary
best = {
    "count": 0,
    "end_time": float("inf"),
    "travel": float("inf"),
    "itinerary": [],
}

# Precompute a simple optimistic bound: number of remaining people
def dfs(current_loc, current_time, remaining_names, itinerary, travel_so_far):
    global best
    # Prune if even meeting everyone remaining doesn't beat best
    potential = len(itinerary) + len(remaining_names)
    if potential < best["count"]:
        return

    # Update best if at leaf (or even mid if better count so far with potential equals current met)
    if len(itinerary) > best["count"]:
        best["count"] = len(itinerary)
        best["end_time"] = current_time
        best["travel"] = travel_so_far
        best["itinerary"] = list(itinerary)
    elif len(itinerary) == best["count"]:
        # tie-breakers: earlier finish, then less travel
        if current_time < best["end_time"] or (current_time == best["end_time"] and travel_so_far < best["travel"]):
            best["end_time"] = current_time
            best["travel"] = travel_so_far
            best["itinerary"] = list(itinerary)

    if not remaining_names:
        return

    # Build candidate feasible next meetings
    candidates = []
    for name in list(remaining_names):
        p = people_by_name[name]
        travel = 0 if current_loc == p["location"] else dist[current_loc][p["location"]]
        arrival = current_time + travel
        start = max(arrival, p["start"])
        end = start + p["min"]
        if end <= p["end"]:
            candidates.append((end, start, travel, name))

    # Sort by earliest finishing first (heuristic)
    candidates.sort()

    for end, start, travel, name in candidates:
        p = people_by_name[name]
        # proceed
        itinerary.append({
            "action": "meet",
            "location": p["location"],
            "person": p["name"],
            "start_time": start,
            "end_time": end,
        })
        remaining_names.remove(name)
        dfs(p["location"], end, remaining_names, itinerary, travel_so_far + travel)
        remaining_names.add(name)
        itinerary.pop()

# Run search
remaining = set(p["name"] for p in people)
dfs(start_location, start_time, remaining, [], 0)

# Convert times to strings and build output
output_itinerary = []
for item in best["itinerary"]:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": m2t(item["start_time"]),
        "end_time": m2t(item["end_time"]),
    })

result = {"itinerary": output_itinerary}

print(json.dumps(result))