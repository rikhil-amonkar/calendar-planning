# SOLUTION:
import json
from itertools import permutations, combinations

def parse_time(s):
    s = s.strip().upper()
    if s.endswith("AM") or s.endswith("PM"):
        ampm = s[-2:]
        h, m = s[:-2].split(":")
        h = int(h)
        m = int(m)
        if ampm == "AM":
            if h == 12:
                h = 0
        else:  # PM
            if h != 12:
                h += 12
        return h * 60 + m
    else:
        # assume H:MM 24-hour
        h, m = s.split(":")
        return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
locations = [
    "Embarcadero",
    "Golden Gate Park",
    "Haight-Ashbury",
    "Bayview",
    "Presidio",
    "Financial District",
]

travel = {loc: {} for loc in locations}

# Embarcadero
travel["Embarcadero"]["Golden Gate Park"] = 25
travel["Embarcadero"]["Haight-Ashbury"] = 21
travel["Embarcadero"]["Bayview"] = 21
travel["Embarcadero"]["Presidio"] = 20
travel["Embarcadero"]["Financial District"] = 5

# Golden Gate Park
travel["Golden Gate Park"]["Embarcadero"] = 25
travel["Golden Gate Park"]["Haight-Ashbury"] = 7
travel["Golden Gate Park"]["Bayview"] = 23
travel["Golden Gate Park"]["Presidio"] = 11
travel["Golden Gate Park"]["Financial District"] = 26

# Haight-Ashbury
travel["Haight-Ashbury"]["Embarcadero"] = 20
travel["Haight-Ashbury"]["Golden Gate Park"] = 7
travel["Haight-Ashbury"]["Bayview"] = 18
travel["Haight-Ashbury"]["Presidio"] = 15
travel["Haight-Ashbury"]["Financial District"] = 21

# Bayview
travel["Bayview"]["Embarcadero"] = 19
travel["Bayview"]["Golden Gate Park"] = 22
travel["Bayview"]["Haight-Ashbury"] = 19
travel["Bayview"]["Presidio"] = 31
travel["Bayview"]["Financial District"] = 19

# Presidio
travel["Presidio"]["Embarcadero"] = 20
travel["Presidio"]["Golden Gate Park"] = 12
travel["Presidio"]["Haight-Ashbury"] = 15
travel["Presidio"]["Bayview"] = 31
travel["Presidio"]["Financial District"] = 23

# Financial District
travel["Financial District"]["Embarcadero"] = 4
travel["Financial District"]["Golden Gate Park"] = 23
travel["Financial District"]["Haight-Ashbury"] = 19
travel["Financial District"]["Bayview"] = 19
travel["Financial District"]["Presidio"] = 22

# Meeting constraints (times as strings for easy editing)
start_location = "Embarcadero"
start_time_str = "9:00AM"

people = [
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "available_start": "8:45AM",
        "available_end": "11:45AM",
        "min_minutes": 45,
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "available_start": "10:15AM",
        "available_end": "4:15PM",
        "min_minutes": 90,
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "available_start": "3:00PM",
        "available_end": "7:15PM",
        "min_minutes": 120,
    },
    {
        "name": "Stephanie",
        "location": "Presidio",
        "available_start": "10:00AM",
        "available_end": "5:15PM",
        "min_minutes": 120,
    },
    {
        "name": "Emily",
        "location": "Financial District",
        "available_start": "11:30AM",
        "available_end": "9:45PM",
        "min_minutes": 105,
    },
]

# Convert times to minutes
start_time = parse_time(start_time_str)
for p in people:
    p["avail_start_min"] = parse_time(p["available_start"])
    p["avail_end_min"] = parse_time(p["available_end"])

def simulate_order(order):
    curr_loc = start_location
    curr_time = start_time
    itinerary = []
    total_travel = 0
    for p in order:
        loc = p["location"]
        if curr_loc == loc:
            t_travel = 0
        else:
            t_travel = travel[curr_loc][loc]
        total_travel += t_travel
        arrival = curr_time + t_travel
        start_meet = max(arrival, p["avail_start_min"])
        end_meet = start_meet + p["min_minutes"]
        if end_meet > p["avail_end_min"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": p["name"],
            "start": start_meet,
            "end": end_meet
        })
        curr_loc = loc
        curr_time = end_meet
    return {
        "itinerary": itinerary,
        "finish_time": curr_time,
        "total_travel": total_travel
    }

# Search best schedule: maximize number met, then earliest finish, then least travel
best = None  # store dict with keys: count, finish_time, total_travel, itinerary
n = len(people)

for k in range(n, 0, -1):
    found_any = False
    for combo in combinations(people, k):
        for order in permutations(combo):
            result = simulate_order(order)
            if result is None:
                continue
            found_any = True
            count = k
            finish = result["finish_time"]
            t_travel = result["total_travel"]
            # Tie-breaking: earliest finish, then least travel
            candidate = {
                "count": count,
                "finish_time": finish,
                "total_travel": t_travel,
                "itinerary": result["itinerary"]
            }
            if best is None:
                best = candidate
            else:
                if (candidate["count"] > best["count"] or
                    (candidate["count"] == best["count"] and candidate["finish_time"] < best["finish_time"]) or
                    (candidate["count"] == best["count"] and candidate["finish_time"] == best["finish_time"] and candidate["total_travel"] < best["total_travel"])):
                    best = candidate
    if found_any:
        break  # we found at least one schedule for this k (maximized)

# Build JSON output
output_itinerary = []
if best:
    for item in best["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": fmt_time(item["start"]),
            "end_time": fmt_time(item["end"]),
        })

result_json = { "itinerary": output_itinerary }

print("SOLUTION:")
print(json.dumps(result_json, indent=2))