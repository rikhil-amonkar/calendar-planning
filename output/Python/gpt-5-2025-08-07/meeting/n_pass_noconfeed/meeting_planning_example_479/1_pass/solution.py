import itertools
import json

# Helper functions for time parsing/formatting
def parse_time(tstr):
    # Parse times like '8:45AM' or '3:00PM' into minutes since midnight
    tstr = tstr.strip().upper()
    if tstr.endswith("AM") or tstr.endswith("PM"):
        ampm = tstr[-2:]
        hm = tstr[:-2]
        h, m = hm.split(":")
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
        # already 24-hour 'H:MM'
        h, m = tstr.split(":")
        return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables (meeting constraints)
arrival_location = "Embarcadero"
arrival_time = parse_time("9:00AM")

friends = [
    {
        "name": "Mary",
        "location": "Golden Gate Park",
        "available_start": parse_time("8:45AM"),
        "available_end": parse_time("11:45AM"),
        "min_duration": 45
    },
    {
        "name": "Kevin",
        "location": "Haight-Ashbury",
        "available_start": parse_time("10:15AM"),
        "available_end": parse_time("4:15PM"),
        "min_duration": 90
    },
    {
        "name": "Deborah",
        "location": "Bayview",
        "available_start": parse_time("3:00PM"),
        "available_end": parse_time("7:15PM"),
        "min_duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Presidio",
        "available_start": parse_time("10:00AM"),
        "available_end": parse_time("5:15PM"),
        "min_duration": 120
    },
    {
        "name": "Emily",
        "location": "Financial District",
        "available_start": parse_time("11:30AM"),
        "available_end": parse_time("9:45PM"),
        "min_duration": 105
    },
]

# Directed travel times in minutes
travel = {
    "Embarcadero": {
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Bayview": 21,
        "Presidio": 20,
        "Financial District": 5
    },
    "Golden Gate Park": {
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Bayview": 23,
        "Presidio": 11,
        "Financial District": 26
    },
    "Haight-Ashbury": {
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Bayview": 18,
        "Presidio": 15,
        "Financial District": 21
    },
    "Bayview": {
        "Embarcadero": 19,
        "Golden Gate Park": 22,
        "Haight-Ashbury": 19,
        "Presidio": 31,
        "Financial District": 19
    },
    "Presidio": {
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Haight-Ashbury": 15,
        "Bayview": 31,
        "Financial District": 23
    },
    "Financial District": {
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Bayview": 19,
        "Presidio": 22
    }
}

# Utility to compute a schedule for a given ordered list of friends
def compute_schedule(order):
    itinerary = []
    current_loc = arrival_location
    current_time = arrival_time
    total_wait = 0
    total_travel = 0

    for person in order:
        loc = person["location"]
        if current_loc == loc:
            travel_time = 0
        else:
            if current_loc not in travel or loc not in travel[current_loc]:
                return None  # route not possible
            travel_time = travel[current_loc][loc]
        arrival = current_time + travel_time
        start = max(arrival, person["available_start"])
        end = start + person["min_duration"]

        if end > person["available_end"]:
            return None  # cannot fit required duration within availability

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": fmt_time(start),
            "end_time": fmt_time(end)
        })

        total_wait += max(0, start - arrival)
        total_travel += travel_time
        current_time = end
        current_loc = loc

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_wait": total_wait,
        "total_travel": total_travel
    }

# Search across all subsets and permutations to maximize number of friends met
best_plan = None

n = len(friends)
for k in range(n, 0, -1):  # start from trying to meet all, then fewer
    found_any = False
    for subset in itertools.combinations(friends, k):
        for perm in itertools.permutations(subset):
            plan = compute_schedule(perm)
            if plan is None:
                continue
            found_any = True
            if best_plan is None:
                best_plan = plan
            else:
                # Primary: maximize meetings (k is descending, so equal here)
                # Secondary: minimize finish time
                # Tertiary: minimize total wait + travel
                bp = best_plan
                better = False
                if plan["finish_time"] < bp["finish_time"]:
                    better = True
                elif plan["finish_time"] == bp["finish_time"]:
                    if (plan["total_wait"] + plan["total_travel"]) < (bp["total_wait"] + bp["total_travel"]):
                        better = True
                if better:
                    best_plan = plan
    if found_any:
        break  # we found at least one schedule meeting k friends; no need to try fewer

# Fallback if none found (shouldn't happen here)
if best_plan is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_plan["itinerary"]}

print(json.dumps(result, ensure_ascii=False))