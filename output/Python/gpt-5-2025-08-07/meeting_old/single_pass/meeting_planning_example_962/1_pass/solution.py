import json

# Meeting planner to compute optimal schedule based on constraints and travel times

# Helper functions
def parse_ampm(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        time_part = s[:-2]
    else:
        # assume 24-hour input like '9:00' or '13:30'
        parts = s.split(":")
        h = int(parts[0])
        m = int(parts[1])
        return h * 60 + m
    time_part = time_part.strip()
    parts = time_part.split(":")
    h = int(parts[0])
    m = int(parts[1])
    if ampm == "AM":
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

# Build directed travel time matrix
locations = [
    "The Castro",
    "Marina District",
    "Presidio",
    "North Beach",
    "Embarcadero",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Richmond District",
    "Alamo Square",
    "Financial District",
    "Sunset District",
]

dist = {loc: {} for loc in locations}

def set_row(frm, mapping):
    for to, mins in mapping.items():
        dist[frm][to] = mins

set_row("The Castro", {
    "Marina District": 21,
    "Presidio": 20,
    "North Beach": 20,
    "Embarcadero": 22,
    "Haight-Ashbury": 6,
    "Golden Gate Park": 11,
    "Richmond District": 16,
    "Alamo Square": 8,
    "Financial District": 21,
    "Sunset District": 17,
})
set_row("Marina District", {
    "The Castro": 22,
    "Presidio": 10,
    "North Beach": 11,
    "Embarcadero": 14,
    "Haight-Ashbury": 16,
    "Golden Gate Park": 18,
    "Richmond District": 11,
    "Alamo Square": 15,
    "Financial District": 17,
    "Sunset District": 19,
})
set_row("Presidio", {
    "The Castro": 21,
    "Marina District": 11,
    "North Beach": 18,
    "Embarcadero": 20,
    "Haight-Ashbury": 15,
    "Golden Gate Park": 12,
    "Richmond District": 7,
    "Alamo Square": 19,
    "Financial District": 23,
    "Sunset District": 15,
})
set_row("North Beach", {
    "The Castro": 23,
    "Marina District": 9,
    "Presidio": 17,
    "Embarcadero": 6,
    "Haight-Ashbury": 18,
    "Golden Gate Park": 22,
    "Richmond District": 18,
    "Alamo Square": 16,
    "Financial District": 8,
    "Sunset District": 27,
})
set_row("Embarcadero", {
    "The Castro": 25,
    "Marina District": 12,
    "Presidio": 20,
    "North Beach": 5,
    "Haight-Ashbury": 21,
    "Golden Gate Park": 25,
    "Richmond District": 21,
    "Alamo Square": 19,
    "Financial District": 5,
    "Sunset District": 30,
})
set_row("Haight-Ashbury", {
    "The Castro": 6,
    "Marina District": 17,
    "Presidio": 15,
    "North Beach": 19,
    "Embarcadero": 20,
    "Golden Gate Park": 7,
    "Richmond District": 10,
    "Alamo Square": 5,
    "Financial District": 21,
    "Sunset District": 15,
})
set_row("Golden Gate Park", {
    "The Castro": 13,
    "Marina District": 16,
    "Presidio": 11,
    "North Beach": 23,
    "Embarcadero": 25,
    "Haight-Ashbury": 7,
    "Richmond District": 7,
    "Alamo Square": 9,
    "Financial District": 26,
    "Sunset District": 10,
})
set_row("Richmond District", {
    "The Castro": 16,
    "Marina District": 9,
    "Presidio": 7,
    "North Beach": 17,
    "Embarcadero": 19,
    "Haight-Ashbury": 10,
    "Golden Gate Park": 9,
    "Alamo Square": 13,
    "Financial District": 22,
    "Sunset District": 11,
})
set_row("Alamo Square", {
    "The Castro": 8,
    "Marina District": 15,
    "Presidio": 17,
    "North Beach": 15,
    "Embarcadero": 16,
    "Haight-Ashbury": 5,
    "Golden Gate Park": 9,
    "Richmond District": 11,
    "Financial District": 17,
    "Sunset District": 16,
})
set_row("Financial District", {
    "The Castro": 20,
    "Marina District": 15,
    "Presidio": 22,
    "North Beach": 7,
    "Embarcadero": 4,
    "Haight-Ashbury": 19,
    "Golden Gate Park": 23,
    "Richmond District": 21,
    "Alamo Square": 17,
    "Sunset District": 30,
})
set_row("Sunset District", {
    "The Castro": 17,
    "Marina District": 21,
    "Presidio": 16,
    "North Beach": 28,
    "Embarcadero": 30,
    "Haight-Ashbury": 15,
    "Golden Gate Park": 11,
    "Richmond District": 12,
    "Alamo Square": 17,
    "Financial District": 30,
})

# Input constraints (people, locations, windows, minimum durations)
people = [
    {"name": "Elizabeth", "location": "Marina District", "start": parse_ampm("7:00PM"), "end": parse_ampm("8:45PM"), "min_duration": 105},
    {"name": "Joshua", "location": "Presidio", "start": parse_ampm("8:30AM"), "end": parse_ampm("1:15PM"), "min_duration": 105},
    {"name": "Timothy", "location": "North Beach", "start": parse_ampm("7:45PM"), "end": parse_ampm("10:00PM"), "min_duration": 90},
    {"name": "David", "location": "Embarcadero", "start": parse_ampm("10:45AM"), "end": parse_ampm("12:30PM"), "min_duration": 30},
    {"name": "Kimberly", "location": "Haight-Ashbury", "start": parse_ampm("4:45PM"), "end": parse_ampm("9:30PM"), "min_duration": 75},
    {"name": "Lisa", "location": "Golden Gate Park", "start": parse_ampm("5:30PM"), "end": parse_ampm("9:45PM"), "min_duration": 45},
    {"name": "Ronald", "location": "Richmond District", "start": parse_ampm("8:00AM"), "end": parse_ampm("9:30AM"), "min_duration": 90},
    {"name": "Stephanie", "location": "Alamo Square", "start": parse_ampm("3:30PM"), "end": parse_ampm("4:30PM"), "min_duration": 30},
    {"name": "Helen", "location": "Financial District", "start": parse_ampm("5:30PM"), "end": parse_ampm("6:30PM"), "min_duration": 45},
    {"name": "Laura", "location": "Sunset District", "start": parse_ampm("5:45PM"), "end": parse_ampm("9:15PM"), "min_duration": 90},
]

start_location = "The Castro"
start_time = parse_ampm("9:00AM")

# Validate travel times cover all required pairs
def travel_time(frm, to):
    if frm == to:
        return 0
    if frm not in dist or to not in dist[frm]:
        raise KeyError(f"Missing travel time from {frm} to {to}")
    return dist[frm][to]

# Search for optimal schedule (maximize number of meetings, tie-break by total meeting minutes, then minimal travel)
best = {
    "count": 0,
    "total_meet": 0,
    "total_travel": float('inf'),
    "itinerary": []
}

# Pre-calc a simple optimistic bound (number of people whose window still open at time t)
def optimistic_remaining_count(remaining, t):
    cnt = 0
    for p in remaining:
        # You must be able to start no later than end - min_duration
        latest_start = p["end"] - p["min_duration"]
        if t <= p["end"] and t <= latest_start + 240:  # loose bound
            cnt += 1
    return cnt

def dfs(current_loc, current_time, remaining, itinerary, total_travel, total_meet):
    global best
    # Update best if current is better
    if (len(itinerary) > best["count"] or
        (len(itinerary) == best["count"] and total_meet > best["total_meet"]) or
        (len(itinerary) == best["count"] and total_meet == best["total_meet"] and total_travel < best["total_travel"])):
        best = {
            "count": len(itinerary),
            "total_meet": total_meet,
            "total_travel": total_travel,
            "itinerary": list(itinerary)
        }

    # Prune if even optimistically we can't beat current best
    potential = len(itinerary) + optimistic_remaining_count(remaining, current_time)
    if potential < best["count"]:
        return

    for i, p in enumerate(remaining):
        # Travel to person
        try:
            ttime = travel_time(current_loc, p["location"])
        except KeyError:
            continue
        arrive = current_time + ttime
        # Determine meeting start and end with minimum duration
        start_meet = max(arrive, p["start"])
        end_meet = start_meet + p["min_duration"]
        # Feasibility check
        if end_meet <= p["end"]:
            entry = {
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": minutes_to_str(start_meet),
                "end_time": minutes_to_str(end_meet)
            }
            itinerary.append(entry)
            next_remaining = remaining[:i] + remaining[i+1:]
            dfs(p["location"], end_meet, next_remaining, itinerary, total_travel + ttime, total_meet + p["min_duration"])
            itinerary.pop()

# Sort people by window end to encourage early pruning
people_sorted = sorted(people, key=lambda x: x["end"])
dfs(start_location, start_time, people_sorted, [], 0, 0)

# Output as JSON
output = {
    "itinerary": best["itinerary"]
}
print(json.dumps(output, ensure_ascii=False))