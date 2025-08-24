import itertools
import json

def parse_time(t):
    # t format 'H:MM'
    h, m = t.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (in minutes)
travel = {
    'Embarcadero': {
        'Richmond District': 21,
        'Union Square': 10,
        'Financial District': 5,
        'Pacific Heights': 11,
        'Nob Hill': 10,
        'Bayview': 21,
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Union Square': 21,
        'Financial District': 22,
        'Pacific Heights': 10,
        'Nob Hill': 17,
        'Bayview': 26,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Richmond District': 20,
        'Financial District': 9,
        'Pacific Heights': 15,
        'Nob Hill': 9,
        'Bayview': 15,
    },
    'Financial District': {
        'Embarcadero': 4,
        'Richmond District': 21,
        'Union Square': 9,
        'Pacific Heights': 13,
        'Nob Hill': 8,
        'Bayview': 19,
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Richmond District': 12,
        'Union Square': 12,
        'Financial District': 13,
        'Nob Hill': 8,
        'Bayview': 22,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Richmond District': 14,
        'Union Square': 7,
        'Financial District': 9,
        'Pacific Heights': 8,
        'Bayview': 19,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Richmond District': 25,
        'Union Square': 17,
        'Financial District': 19,
        'Pacific Heights': 23,
        'Nob Hill': 20,
    },
}

# Ensure zero self-travel
for a in list(travel.keys()):
    travel[a][a] = 0

# Meeting constraints as input variables
people = [
    {
        "name": "Kenneth",
        "location": "Richmond District",
        "available_start": "21:15",
        "available_end": "22:00",
        "min_duration": 30,
    },
    {
        "name": "Lisa",
        "location": "Union Square",
        "available_start": "9:00",
        "available_end": "16:30",
        "min_duration": 45,
    },
    {
        "name": "Joshua",
        "location": "Financial District",
        "available_start": "12:00",
        "available_end": "15:15",
        "min_duration": 15,
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "available_start": "8:00",
        "available_end": "11:30",
        "min_duration": 90,
    },
    {
        "name": "Andrew",
        "location": "Nob Hill",
        "available_start": "11:30",
        "available_end": "20:15",
        "min_duration": 60,
    },
    {
        "name": "John",
        "location": "Bayview",
        "available_start": "16:45",
        "available_end": "21:30",
        "min_duration": 75,
    },
]

# Convert times to minutes for processing
for p in people:
    p["start_min"] = parse_time(p["available_start"])
    p["end_min"] = parse_time(p["available_end"])

start_location = "Embarcadero"
start_time = parse_time("9:00")

def evaluate_schedule(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0

    for person in order:
        loc = person["location"]
        if current_loc not in travel or loc not in travel[current_loc]:
            return None  # Missing travel info
        t_travel = travel[current_loc][loc]
        total_travel += t_travel
        arrival = current_time + t_travel
        start_meet = max(arrival, person["start_min"])
        end_meet = start_meet + person["min_duration"]
        if end_meet > person["end_min"]:
            return None  # Cannot fit meeting within window
        wait = max(0, start_meet - arrival)
        total_wait += wait

        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": person["name"],
            "start_time": fmt_time(start_meet),
            "end_time": fmt_time(end_meet),
        })

        current_loc = loc
        current_time = end_meet

    return {
        "itinerary": itinerary,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "finish_time": current_time,
        "count": len(order),
    }

def better(a, b):
    # Returns True if a is better than b
    if b is None:
        return True
    # Primary: meet as many friends as possible
    if a["count"] != b["count"]:
        return a["count"] > b["count"]
    # Secondary: minimize total travel time
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    # Tertiary: minimize total waiting time
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    # Quaternary: earliest finish time
    return a["finish_time"] < b["finish_time"]

best = None

# Consider all subsets and permutations to find an optimal schedule
n = len(people)
for k in range(n, 0, -1):
    found_any = False
    for combo in itertools.combinations(people, k):
        for order in itertools.permutations(combo):
            result = evaluate_schedule(order)
            if result is not None:
                found_any = True
                if better(result, best):
                    best = result
    if found_any:
        break

output = {"itinerary": best["itinerary"] if best else []}
print(json.dumps(output, ensure_ascii=False))