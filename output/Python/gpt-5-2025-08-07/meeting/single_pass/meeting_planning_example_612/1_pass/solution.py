import itertools
import json

def time_to_min(t):
    # t like '9:00' or '13:30'
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Input variables (constraints)
start_location = "Alamo Square"
start_time_str = "9:00"

people = [
    {"name": "Emily", "location": "Russian Hill", "window_start": "12:15", "window_end": "14:15", "min_duration": 105},
    {"name": "Mark", "location": "Presidio", "window_start": "14:45", "window_end": "19:30", "min_duration": 60},
    {"name": "Deborah", "location": "Chinatown", "window_start": "7:30", "window_end": "15:30", "min_duration": 45},
    {"name": "Margaret", "location": "Sunset District", "window_start": "21:30", "window_end": "22:30", "min_duration": 60},
    {"name": "George", "location": "The Castro", "window_start": "7:30", "window_end": "14:15", "min_duration": 60},
    {"name": "Andrew", "location": "Embarcadero", "window_start": "20:15", "window_end": "22:00", "min_duration": 75},
    {"name": "Steven", "location": "Golden Gate Park", "window_start": "11:15", "window_end": "21:15", "min_duration": 105},
]

# Convert time strings to minutes
for p in people:
    p["start_min"] = time_to_min(p["window_start"])
    p["end_min"] = time_to_min(p["window_end"])

start_time = time_to_min(start_time_str)

# Travel times: minutes (directional as provided)
travel = {
    "Alamo Square": {
        "Russian Hill": 13, "Presidio": 18, "Chinatown": 16, "Sunset District": 16,
        "The Castro": 8, "Embarcadero": 17, "Golden Gate Park": 9
    },
    "Russian Hill": {
        "Alamo Square": 15, "Presidio": 14, "Chinatown": 9, "Sunset District": 23,
        "The Castro": 21, "Embarcadero": 8, "Golden Gate Park": 21
    },
    "Presidio": {
        "Alamo Square": 18, "Russian Hill": 14, "Chinatown": 21, "Sunset District": 15,
        "The Castro": 21, "Embarcadero": 20, "Golden Gate Park": 12
    },
    "Chinatown": {
        "Alamo Square": 17, "Russian Hill": 7, "Presidio": 19, "Sunset District": 29,
        "The Castro": 22, "Embarcadero": 5, "Golden Gate Park": 23
    },
    "Sunset District": {
        "Alamo Square": 17, "Russian Hill": 24, "Presidio": 16, "Chinatown": 30,
        "The Castro": 17, "Embarcadero": 31, "Golden Gate Park": 11
    },
    "The Castro": {
        "Alamo Square": 8, "Russian Hill": 18, "Presidio": 20, "Chinatown": 20,
        "Sunset District": 17, "Embarcadero": 22, "Golden Gate Park": 11
    },
    "Embarcadero": {
        "Alamo Square": 19, "Russian Hill": 8, "Presidio": 20, "Chinatown": 7,
        "Sunset District": 30, "The Castro": 25, "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "Alamo Square": 10, "Russian Hill": 19, "Presidio": 11, "Chinatown": 23,
        "Sunset District": 10, "The Castro": 13, "Embarcadero": 25
    }
}

def travel_time(frm, to):
    if frm == to:
        return 0
    return travel.get(frm, {}).get(to, None)

def schedule_for_order(order):
    itinerary = []
    cur_time = start_time
    cur_loc = start_location
    for p in order:
        t = travel_time(cur_loc, p["location"])
        if t is None:
            continue  # no route defined
        arrival = cur_time + t
        start = max(arrival, p["start_min"])
        end = start + p["min_duration"]
        if end <= p["end_min"]:
            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_time_min": start,
                "end_time_min": end
            })
            cur_time = end
            cur_loc = p["location"]
        else:
            # cannot meet this person in this order
            continue
    return itinerary

def evaluate_itinerary(itin):
    count = len(itin)
    total_meet = sum(item["end_time_min"] - item["start_time_min"] for item in itin)
    finish_time = itin[-1]["end_time_min"] if itin else start_time
    total_travel = 0
    loc = start_location
    time = start_time
    for item in itin:
        t = travel_time(loc, item["location"])
        total_travel += (t if t is not None else 0)
        loc = item["location"]
        time = item["end_time_min"]
    return (count, total_meet, -finish_time, -total_travel)

best_score = None
best_itinerary = None

for order in itertools.permutations(people):
    itin = schedule_for_order(order)
    score = evaluate_itinerary(itin)
    if (best_score is None) or (score > best_score):
        best_score = score
        best_itinerary = itin

# Format output
output_itinerary = []
for item in best_itinerary:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": min_to_time(item["start_time_min"]),
        "end_time": min_to_time(item["end_time_min"])
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False))