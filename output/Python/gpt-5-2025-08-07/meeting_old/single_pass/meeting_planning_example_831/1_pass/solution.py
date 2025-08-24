import json

def parse_ampm(s):
    s = s.strip().upper()
    am = s.endswith('AM')
    pm = s.endswith('PM')
    time_part = s[:-2]
    h, m = map(int, time_part.split(':'))
    if h == 12:
        h = 0
    if pm:
        h += 12
    return h * 60 + m

def m2s(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes) as given
travel = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Friends constraints
friends = [
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "start": parse_ampm("10:15AM"),
        "end": parse_ampm("1:00PM"),
        "min_duration": 90
    },
    {
        "name": "Ronald",
        "location": "Alamo Square",
        "start": parse_ampm("7:45AM"),
        "end": parse_ampm("2:45PM"),
        "min_duration": 120
    },
    {
        "name": "Jason",
        "location": "Financial District",
        "start": parse_ampm("10:45AM"),
        "end": parse_ampm("4:00PM"),
        "min_duration": 105
    },
    {
        "name": "Melissa",
        "location": "Union Square",
        "start": parse_ampm("5:45PM"),
        "end": parse_ampm("6:15PM"),
        "min_duration": 15
    },
    {
        "name": "Elizabeth",
        "location": "Sunset District",
        "start": parse_ampm("2:45PM"),
        "end": parse_ampm("5:30PM"),
        "min_duration": 105
    },
    {
        "name": "Margaret",
        "location": "Embarcadero",
        "start": parse_ampm("1:15PM"),
        "end": parse_ampm("7:00PM"),
        "min_duration": 90
    },
    {
        "name": "George",
        "location": "Golden Gate Park",
        "start": parse_ampm("7:00PM"),
        "end": parse_ampm("10:00PM"),
        "min_duration": 75
    },
    {
        "name": "Richard",
        "location": "Chinatown",
        "start": parse_ampm("9:30AM"),
        "end": parse_ampm("9:00PM"),
        "min_duration": 15
    },
    {
        "name": "Laura",
        "location": "Richmond District",
        "start": parse_ampm("9:45AM"),
        "end": parse_ampm("6:00PM"),
        "min_duration": 60
    }
]

start_location = "Presidio"
start_time = parse_ampm("9:00AM")

# Helper for comparison of solutions
def better_solution(a, b):
    # a and b are dicts with keys: count, end_time, travel, path
    if a is None:
        return False
    if b is None:
        return True
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    if a["end_time"] != b["end_time"]:
        return a["end_time"] < b["end_time"]
    # minimize total travel time
    if a["travel"] != b["travel"]:
        return a["travel"] < b["travel"]
    # as final tie-breaker, lexicographically smallest sequence of names
    names_a = [m["person"] for m in a["path"]]
    names_b = [m["person"] for m in b["path"]]
    return names_a < names_b

best = None

# For efficiency, precompute an order of friends to try (earliest window end first)
order_indices = list(range(len(friends)))
order_indices.sort(key=lambda i: friends[i]["end"])

def search(curr_loc, curr_time, remaining_indices, path, travel_sum):
    global best
    # Update best with current path
    current_solution = {
        "count": len(path),
        "end_time": curr_time,
        "travel": travel_sum,
        "path": path
    }
    if better_solution(current_solution, best):
        best = current_solution

    # Try next friends
    # Heuristic: iterate remaining by earliest feasible end and proximity
    for i in sorted(remaining_indices, key=lambda idx: (friends[idx]["end"], travel.get(curr_loc, {}).get(friends[idx]["location"], 1e9))):
        p = friends[i]
        # If no travel path, skip
        if curr_loc not in travel or p["location"] not in travel[curr_loc]:
            continue
        drive = travel[curr_loc][p["location"]]
        arrival = curr_time + drive
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["min_duration"]
        if end_meet <= p["end"]:
            # feasible
            new_path = path + [{
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time": m2s(start_meet),
                "end_time": m2s(end_meet)
            }]
            new_remaining = [x for x in remaining_indices if x != i]
            search(p["location"], end_meet, new_remaining, new_path, travel_sum + drive)
        # else not feasible, skip

# Start search
search(start_location, start_time, list(range(len(friends))), [], 0)

# Output result
result = {
    "itinerary": best["path"] if best else []
}
print(json.dumps(result))