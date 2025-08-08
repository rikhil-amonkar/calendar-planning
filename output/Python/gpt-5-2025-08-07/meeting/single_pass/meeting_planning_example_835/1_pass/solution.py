import json

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h*60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between locations (directed)
dist = {
    "Pacific Heights": {
        "Golden Gate Park": 15,
        "The Castro": 16,
        "Bayview": 22,
        "Marina District": 6,
        "Union Square": 12,
        "Sunset District": 21,
        "Alamo Square": 10,
        "Financial District": 13,
        "Mission District": 15
    },
    "Golden Gate Park": {
        "Pacific Heights": 16,
        "The Castro": 13,
        "Bayview": 23,
        "Marina District": 16,
        "Union Square": 22,
        "Sunset District": 10,
        "Alamo Square": 9,
        "Financial District": 26,
        "Mission District": 17
    },
    "The Castro": {
        "Pacific Heights": 16,
        "Golden Gate Park": 11,
        "Bayview": 19,
        "Marina District": 21,
        "Union Square": 19,
        "Sunset District": 17,
        "Alamo Square": 8,
        "Financial District": 21,
        "Mission District": 7
    },
    "Bayview": {
        "Pacific Heights": 23,
        "Golden Gate Park": 22,
        "The Castro": 19,
        "Marina District": 27,
        "Union Square": 18,
        "Sunset District": 23,
        "Alamo Square": 16,
        "Financial District": 19,
        "Mission District": 13
    },
    "Marina District": {
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "The Castro": 22,
        "Bayview": 27,
        "Union Square": 16,
        "Sunset District": 19,
        "Alamo Square": 15,
        "Financial District": 17,
        "Mission District": 20
    },
    "Union Square": {
        "Pacific Heights": 15,
        "Golden Gate Park": 22,
        "The Castro": 17,
        "Bayview": 15,
        "Marina District": 18,
        "Sunset District": 27,
        "Alamo Square": 15,
        "Financial District": 9,
        "Mission District": 14
    },
    "Sunset District": {
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "The Castro": 17,
        "Bayview": 22,
        "Marina District": 21,
        "Union Square": 30,
        "Alamo Square": 17,
        "Financial District": 30,
        "Mission District": 25
    },
    "Alamo Square": {
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "The Castro": 8,
        "Bayview": 16,
        "Marina District": 15,
        "Union Square": 14,
        "Sunset District": 16,
        "Financial District": 17,
        "Mission District": 10
    },
    "Financial District": {
        "Pacific Heights": 13,
        "Golden Gate Park": 23,
        "The Castro": 20,
        "Bayview": 19,
        "Marina District": 15,
        "Union Square": 9,
        "Sunset District": 30,
        "Alamo Square": 17,
        "Mission District": 17
    },
    "Mission District": {
        "Pacific Heights": 16,
        "Golden Gate Park": 17,
        "The Castro": 7,
        "Bayview": 14,
        "Marina District": 19,
        "Union Square": 15,
        "Sunset District": 24,
        "Alamo Square": 11,
        "Financial District": 15
    }
}

# Meeting constraints
people = {
    "Helen": {
        "location": "Golden Gate Park",
        "start": time_to_minutes("9:30"),
        "end": time_to_minutes("12:15"),
        "min_duration": 45
    },
    "Steven": {
        "location": "The Castro",
        "start": time_to_minutes("20:15"),
        "end": time_to_minutes("22:00"),
        "min_duration": 105
    },
    "Deborah": {
        "location": "Bayview",
        "start": time_to_minutes("8:30"),
        "end": time_to_minutes("12:00"),
        "min_duration": 30
    },
    "Matthew": {
        "location": "Marina District",
        "start": time_to_minutes("9:15"),
        "end": time_to_minutes("14:15"),
        "min_duration": 45
    },
    "Joseph": {
        "location": "Union Square",
        "start": time_to_minutes("14:15"),
        "end": time_to_minutes("18:45"),
        "min_duration": 120
    },
    "Ronald": {
        "location": "Sunset District",
        "start": time_to_minutes("16:00"),
        "end": time_to_minutes("20:45"),
        "min_duration": 60
    },
    "Robert": {
        "location": "Alamo Square",
        "start": time_to_minutes("18:30"),
        "end": time_to_minutes("21:15"),
        "min_duration": 120
    },
    "Rebecca": {
        "location": "Financial District",
        "start": time_to_minutes("14:45"),
        "end": time_to_minutes("16:15"),
        "min_duration": 30
    },
    "Elizabeth": {
        "location": "Mission District",
        "start": time_to_minutes("18:30"),
        "end": time_to_minutes("21:00"),
        "min_duration": 120
    }
}

start_location = "Pacific Heights"
start_time = time_to_minutes("9:00")

# DFS search for best schedule
names = list(people.keys())

best = {
    "count": -1,
    "total_minutes": -1,
    "finish_time": float("inf"),
    "travel_minutes": float("inf"),
    "itinerary": []
}

def get_travel(a, b):
    if a == b:
        return 0
    return dist.get(a, {}).get(b, 0)

def dfs(current_loc, current_time, remaining, itinerary, total_meeting_minutes, total_travel_minutes):
    global best
    # Update best if current itinerary is better (even if we can add more later, we also try deeper)
    current_count = len(itinerary)
    # Compare to best only at leaf or intermediate as a candidate
    def is_better(candidate, incumbent):
        # candidate: (count, total_meeting_minutes, finish_time, travel_minutes)
        if candidate[0] > incumbent[0]:
            return True
        if candidate[0] < incumbent[0]:
            return False
        if candidate[1] > incumbent[1]:
            return True
        if candidate[1] < incumbent[1]:
            return False
        if candidate[2] < incumbent[2]:
            return True
        if candidate[2] > incumbent[2]:
            return False
        if candidate[3] < incumbent[3]:
            return True
        return False

    if is_better((current_count, total_meeting_minutes, current_time, total_travel_minutes),
                 (best["count"], best["total_minutes"], best["finish_time"], best["travel_minutes"])):
        best = {
            "count": current_count,
            "total_minutes": total_meeting_minutes,
            "finish_time": current_time,
            "travel_minutes": total_travel_minutes,
            "itinerary": list(itinerary)
        }

    # Upper bound pruning: even if we meet everyone remaining, can we beat best?
    if current_count + len(remaining) < best["count"]:
        return

    # Try next meetings sorted by earlier window end to improve pruning
    for name in sorted(remaining, key=lambda n: people[n]["end"]):
        p = people[name]
        travel = get_travel(current_loc, p["location"])
        arrival = current_time + travel
        start = max(arrival, p["start"])
        end = start + p["min_duration"]
        if end <= p["end"]:
            # Feasible meeting
            item = {
                "action": "meet",
                "location": p["location"],
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            }
            itinerary.append(item)
            new_remaining = [r for r in remaining if r != name]
            dfs(p["location"], end, new_remaining, itinerary, total_meeting_minutes + p["min_duration"], total_travel_minutes + travel)
            itinerary.pop()

# Run search
dfs(start_location, start_time, names, [], 0, 0)

result = {
    "itinerary": best["itinerary"]
}

print(json.dumps(result, ensure_ascii=False))