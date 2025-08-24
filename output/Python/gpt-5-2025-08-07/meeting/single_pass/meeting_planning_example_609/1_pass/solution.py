import json
from itertools import permutations

def parse_time_24(s):
    # s like '9:00' or '19:45'
    h, m = s.split(':')
    return int(h) * 60 + int(m)

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (directed)
travel = {
    "Chinatown": {
        "Mission District": 18, "Alamo Square": 17, "Pacific Heights": 10,
        "Union Square": 7, "Golden Gate Park": 23, "Sunset District": 29, "Presidio": 19
    },
    "Mission District": {
        "Chinatown": 16, "Alamo Square": 11, "Pacific Heights": 16,
        "Union Square": 15, "Golden Gate Park": 17, "Sunset District": 24, "Presidio": 25
    },
    "Alamo Square": {
        "Chinatown": 16, "Mission District": 10, "Pacific Heights": 10,
        "Union Square": 14, "Golden Gate Park": 9, "Sunset District": 16, "Presidio": 18
    },
    "Pacific Heights": {
        "Chinatown": 11, "Mission District": 15, "Alamo Square": 10,
        "Union Square": 12, "Golden Gate Park": 15, "Sunset District": 21, "Presidio": 11
    },
    "Union Square": {
        "Chinatown": 7, "Mission District": 14, "Alamo Square": 15,
        "Pacific Heights": 15, "Golden Gate Park": 22, "Sunset District": 26, "Presidio": 24
    },
    "Golden Gate Park": {
        "Chinatown": 23, "Mission District": 17, "Alamo Square": 10,
        "Pacific Heights": 16, "Union Square": 22, "Sunset District": 10, "Presidio": 11
    },
    "Sunset District": {
        "Chinatown": 30, "Mission District": 24, "Alamo Square": 17,
        "Pacific Heights": 21, "Union Square": 30, "Golden Gate Park": 11, "Presidio": 16
    },
    "Presidio": {
        "Chinatown": 21, "Mission District": 26, "Alamo Square": 18,
        "Pacific Heights": 11, "Union Square": 22, "Golden Gate Park": 12, "Sunset District": 15
    }
}

def get_travel_time(a, b):
    if a == b:
        return 0
    return travel[a][b]

# Meeting constraints (24-hour strings)
people = [
    {
        "name": "David",
        "location": "Mission District",
        "start": parse_time_24("8:00"),
        "end": parse_time_24("19:45"),
        "min_duration": 45
    },
    {
        "name": "Kenneth",
        "location": "Alamo Square",
        "start": parse_time_24("14:00"),
        "end": parse_time_24("19:45"),
        "min_duration": 120
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "start": parse_time_24("17:00"),
        "end": parse_time_24("20:00"),
        "min_duration": 15
    },
    {
        "name": "Charles",
        "location": "Union Square",
        "start": parse_time_24("21:45"),
        "end": parse_time_24("22:45"),
        "min_duration": 60
    },
    {
        "name": "Deborah",
        "location": "Golden Gate Park",
        "start": parse_time_24("7:00"),
        "end": parse_time_24("18:15"),
        "min_duration": 90
    },
    {
        "name": "Karen",
        "location": "Sunset District",
        "start": parse_time_24("17:45"),
        "end": parse_time_24("21:15"),
        "min_duration": 15
    },
    {
        "name": "Carol",
        "location": "Presidio",
        "start": parse_time_24("8:15"),
        "end": parse_time_24("9:15"),
        "min_duration": 30
    }
]

start_location = "Chinatown"
start_time = parse_time_24("9:00")

def simulate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_wait = 0
    total_travel = 0

    for p in order:
        travel_time = get_travel_time(current_loc, p["location"])
        arrival = current_time + travel_time
        meeting_start = max(arrival, p["start"])
        meeting_end = meeting_start + p["min_duration"]

        # Can we meet within their availability?
        if meeting_end <= p["end"]:
            # Record travel and wait (if any)
            wait = max(0, meeting_start - arrival)
            total_wait += wait
            total_travel += travel_time

            itinerary.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start": meeting_start,
                "end": meeting_end
            })
            current_loc = p["location"]
            current_time = meeting_end
        else:
            # Skip if infeasible
            continue

    if itinerary:
        end_time = itinerary[-1]["end"]
    else:
        end_time = start_time

    # Primary: maximize count; Secondary: earliest end; Tertiary: minimize waiting; Quaternary: minimize travel
    score = (len(itinerary), -end_time, -total_wait, -total_travel)
    return score, itinerary

# Enumerate all permutations and pick the best
best_score = None
best_itinerary = None

for order in permutations(people):
    score, itinerary = simulate_order(order)
    if best_score is None or score > best_score:
        best_score = score
        best_itinerary = itinerary

# Format times for output
output_itinerary = []
for item in best_itinerary:
    output_itinerary.append({
        "action": "meet",
        "location": item["location"],
        "person": item["person"],
        "start_time": fmt_time(item["start"]),
        "end_time": fmt_time(item["end"])
    })

result = {"itinerary": output_itinerary}
print(json.dumps(result, ensure_ascii=False, indent=2))