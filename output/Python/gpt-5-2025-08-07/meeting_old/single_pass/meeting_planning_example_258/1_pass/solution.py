import itertools
import json

# Helper functions for time parsing and formatting
def parse_time_12h(s):
    s = s.strip().upper().replace(' ', '')
    if s.endswith('AM') or s.endswith('PM'):
        period = s[-2:]
        s = s[:-2]
    else:
        period = None
    hour_min = s.split(':')
    hour = int(hour_min[0])
    minute = int(hour_min[1]) if len(hour_min) > 1 else 0
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    return hour * 60 + minute

def format_time_24h(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input variables
start_location = "Embarcadero"
start_time_str = "9:00AM"

travel_times = {
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Richmond District"): 18,
}

people = [
    {
        "name": "Betty",
        "location": "Presidio",
        "available_start": "10:15AM",
        "available_end": "9:30PM",
        "min_duration_min": 45,
    },
    {
        "name": "David",
        "location": "Richmond District",
        "available_start": "1:00PM",
        "available_end": "8:15PM",
        "min_duration_min": 90,
    },
    {
        "name": "Barbara",
        "location": "Fisherman's Wharf",
        "available_start": "9:15AM",
        "available_end": "8:15PM",
        "min_duration_min": 120,
    },
]

# Preprocess times
start_time = parse_time_12h(start_time_str)
for p in people:
    p["avail_start_min"] = parse_time_12h(p["available_start"])
    p["avail_end_min"] = parse_time_12h(p["available_end"])

# Travel time lookup
def get_travel_time(a, b):
    if a == b:
        return 0
    return travel_times[(a, b)]

# Simulate a schedule for a given order of people
def simulate(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_wait = 0

    for person in order:
        travel = get_travel_time(current_loc, person["location"])
        arrival = current_time + travel
        start = max(arrival, person["avail_start_min"])
        wait = max(0, start - arrival)
        end = start + person["min_duration_min"]
        if end > person["avail_end_min"]:
            return None  # infeasible
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person["name"],
            "start_time_min": start,
            "end_time_min": end,
        })
        current_loc = person["location"]
        current_time = end
        total_wait += wait

    finish_time = current_time
    return {
        "itinerary": itinerary,
        "finish_time": finish_time,
        "total_wait": total_wait,
        "met_count": len(order)
    }

# Evaluate and choose the best schedule:
# Priority: maximize met_count, then minimize finish_time, then minimize total_wait
best = None

for k in range(len(people), 0, -1):
    found_for_k = []
    for order in itertools.permutations(people, k):
        result = simulate(order)
        if result is not None:
            found_for_k.append(result)
    if found_for_k:
        # Choose best among these
        found_for_k.sort(key=lambda r: (r["finish_time"], r["total_wait"]))
        best = found_for_k[0]
        break

# Prepare JSON output
output_itinerary = []
if best:
    for item in best["itinerary"]:
        output_itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": format_time_24h(item["start_time_min"]),
            "end_time": format_time_24h(item["end_time_min"]),
        })

result_json = {"itinerary": output_itinerary}

print(json.dumps(result_json, ensure_ascii=False))