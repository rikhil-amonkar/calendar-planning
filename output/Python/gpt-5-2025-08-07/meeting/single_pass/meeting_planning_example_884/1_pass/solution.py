import json
from itertools import permutations

def minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times (minutes) between locations
travel = {
    "Richmond District": {
        "Chinatown": 20, "Sunset District": 11, "Alamo Square": 13, "Financial District": 22,
        "North Beach": 17, "Embarcadero": 19, "Presidio": 7, "Golden Gate Park": 9, "Bayview": 27
    },
    "Chinatown": {
        "Richmond District": 20, "Sunset District": 29, "Alamo Square": 17, "Financial District": 5,
        "North Beach": 3, "Embarcadero": 5, "Presidio": 19, "Golden Gate Park": 23, "Bayview": 20
    },
    "Sunset District": {
        "Richmond District": 12, "Chinatown": 30, "Alamo Square": 17, "Financial District": 30,
        "North Beach": 28, "Embarcadero": 30, "Presidio": 16, "Golden Gate Park": 11, "Bayview": 22
    },
    "Alamo Square": {
        "Richmond District": 11, "Chinatown": 15, "Sunset District": 16, "Financial District": 17,
        "North Beach": 15, "Embarcadero": 16, "Presidio": 17, "Golden Gate Park": 9, "Bayview": 16
    },
    "Financial District": {
        "Richmond District": 21, "Chinatown": 5, "Sunset District": 30, "Alamo Square": 17,
        "North Beach": 7, "Embarcadero": 4, "Presidio": 22, "Golden Gate Park": 23, "Bayview": 19
    },
    "North Beach": {
        "Richmond District": 18, "Chinatown": 6, "Sunset District": 27, "Alamo Square": 16,
        "Financial District": 8, "Embarcadero": 6, "Presidio": 17, "Golden Gate Park": 22, "Bayview": 25
    },
    "Embarcadero": {
        "Richmond District": 21, "Chinatown": 7, "Sunset District": 30, "Alamo Square": 19,
        "Financial District": 5, "North Beach": 5, "Presidio": 20, "Golden Gate Park": 25, "Bayview": 21
    },
    "Presidio": {
        "Richmond District": 7, "Chinatown": 21, "Sunset District": 15, "Alamo Square": 19,
        "Financial District": 23, "North Beach": 18, "Embarcadero": 20, "Golden Gate Park": 12, "Bayview": 31
    },
    "Golden Gate Park": {
        "Richmond District": 7, "Chinatown": 23, "Sunset District": 10, "Alamo Square": 9,
        "Financial District": 26, "North Beach": 23, "Embarcadero": 25, "Presidio": 11, "Bayview": 23
    },
    "Bayview": {
        "Richmond District": 25, "Chinatown": 19, "Sunset District": 23, "Alamo Square": 16,
        "Financial District": 19, "North Beach": 22, "Embarcadero": 19, "Presidio": 32, "Golden Gate Park": 22
    }
}

# Meeting constraints
people = [
    {"person": "Robert",  "location": "Chinatown",          "start": minutes("7:45"),  "end": minutes("17:30"), "duration": 120},
    {"person": "David",   "location": "Sunset District",    "start": minutes("12:30"), "end": minutes("19:45"), "duration": 45},
    {"person": "Matthew", "location": "Alamo Square",       "start": minutes("8:45"),  "end": minutes("13:45"), "duration": 90},
    {"person": "Jessica", "location": "Financial District", "start": minutes("9:30"),  "end": minutes("18:45"), "duration": 45},
    {"person": "Melissa", "location": "North Beach",        "start": minutes("7:15"),  "end": minutes("16:45"), "duration": 45},
    {"person": "Mark",    "location": "Embarcadero",        "start": minutes("15:15"), "end": minutes("17:00"), "duration": 45},
    {"person": "Deborah", "location": "Presidio",           "start": minutes("19:00"), "end": minutes("19:45"), "duration": 45},
    {"person": "Karen",   "location": "Golden Gate Park",   "start": minutes("19:30"), "end": minutes("22:00"), "duration": 120},
    {"person": "Laura",   "location": "Bayview",            "start": minutes("21:15"), "end": minutes("22:15"), "duration": 15},
]

start_location = "Richmond District"
start_time = minutes("9:00")

def build_schedule(order):
    itinerary = []
    current_loc = start_location
    current_time = start_time
    total_travel = 0
    total_wait = 0

    for p in order:
        ttime = travel[current_loc][p["location"]]
        arrival = current_time + ttime
        start_meet = max(arrival, p["start"])
        end_meet = start_meet + p["duration"]
        if end_meet <= p["end"]:
            # feasible
            if start_meet > arrival:
                total_wait += start_meet - arrival
            total_travel += ttime
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["person"],
                "start_time": fmt(start_meet),
                "end_time": fmt(end_meet)
            })
            current_loc = p["location"]
            current_time = end_meet
        else:
            # skip this person as infeasible in this order
            continue

    return itinerary, total_travel, total_wait, current_time

# Search over permutations to maximize number of meetings; tie-break by minimal waiting, then minimal travel, then earliest finish
best = {
    "itinerary": [],
    "count": -1,
    "wait": float('inf'),
    "travel": float('inf'),
    "finish": float('inf'),
    "order": None
}

for order in permutations(people):
    itin, t_travel, t_wait, finish = build_schedule(order)
    count = len(itin)
    # Primary objective: maximize number of people met
    better = False
    if count > best["count"]:
        better = True
    elif count == best["count"]:
        if t_wait < best["wait"]:
            better = True
        elif t_wait == best["wait"]:
            if t_travel < best["travel"]:
                better = True
            elif t_travel == best["travel"]:
                if finish < best["finish"]:
                    better = True

    if better:
        best = {
            "itinerary": itin,
            "count": count,
            "wait": t_wait,
            "travel": t_travel,
            "finish": finish,
            "order": order
        }

output = {"itinerary": best["itinerary"]}
print(json.dumps(output, ensure_ascii=False))