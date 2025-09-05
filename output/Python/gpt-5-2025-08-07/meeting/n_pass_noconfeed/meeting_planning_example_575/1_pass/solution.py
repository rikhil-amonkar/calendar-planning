import itertools
import json

def parse_time_ampm(s):
    s = s.strip().upper()
    if s.endswith('AM') or s.endswith('PM'):
        ampm = s[-2:]
        time_part = s[:-2]
    else:
        # already 24-hour like '13:30'
        parts = time_part.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    h, m = map(int, time_part.split(':'))
    if ampm == 'AM':
        if h == 12:
            h = 0
    else:  # PM
        if h != 12:
            h += 12
    return h * 60 + m

def minutes_to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Input variables: locations, travel times, availability windows, minimum meeting durations
locations = [
    "The Castro",
    "Presidio",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
    "Russian Hill",
]

# Directed travel times (in minutes)
travel = {
    "The Castro": {
        "Presidio": 20,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Golden Gate Park": 11,
        "Russian Hill": 18,
    },
    "Presidio": {
        "The Castro": 21,
        "Sunset District": 15,
        "Haight-Ashbury": 15,
        "Mission District": 26,
        "Golden Gate Park": 12,
        "Russian Hill": 14,
    },
    "Sunset District": {
        "The Castro": 17,
        "Presidio": 16,
        "Haight-Ashbury": 15,
        "Mission District": 24,
        "Golden Gate Park": 11,
        "Russian Hill": 24,
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Presidio": 15,
        "Sunset District": 15,
        "Mission District": 11,
        "Golden Gate Park": 7,
        "Russian Hill": 17,
    },
    "Mission District": {
        "The Castro": 7,
        "Presidio": 25,
        "Sunset District": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17,
        "Russian Hill": 15,
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Presidio": 11,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Russian Hill": 19,
    },
    "Russian Hill": {
        "The Castro": 21,
        "Presidio": 14,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Golden Gate Park": 21,
    },
}

# People constraints
people = [
    {
        "name": "Rebecca",
        "location": "Presidio",
        "start": parse_time_ampm("6:15PM"),
        "end": parse_time_ampm("8:45PM"),
        "min_duration": 60,
    },
    {
        "name": "Linda",
        "location": "Sunset District",
        "start": parse_time_ampm("3:30PM"),
        "end": parse_time_ampm("7:45PM"),
        "min_duration": 30,
    },
    {
        "name": "Elizabeth",
        "location": "Haight-Ashbury",
        "start": parse_time_ampm("5:15PM"),
        "end": parse_time_ampm("7:30PM"),
        "min_duration": 105,
    },
    {
        "name": "William",
        "location": "Mission District",
        "start": parse_time_ampm("1:15PM"),
        "end": parse_time_ampm("7:30PM"),
        "min_duration": 30,
    },
    {
        "name": "Robert",
        "location": "Golden Gate Park",
        "start": parse_time_ampm("2:15PM"),
        "end": parse_time_ampm("9:30PM"),
        "min_duration": 45,
    },
    {
        "name": "Mark",
        "location": "Russian Hill",
        "start": parse_time_ampm("10:00AM"),
        "end": parse_time_ampm("9:15PM"),
        "min_duration": 75,
    },
]

start_location = "The Castro"
start_time = parse_time_ampm("9:00AM")

def get_travel_time(a, b):
    if a == b:
        return 0
    return travel.get(a, {}).get(b, None)

def simulate_order(order):
    current_loc = start_location
    current_time = start_time
    itinerary = []
    total_travel = 0
    total_wait = 0
    met = 0
    total_meet = 0

    for person in order:
        t = get_travel_time(current_loc, person["location"])
        if t is None:
            # Unknown travel; skip attempting this person
            continue
        arrival = current_time + t
        # If we arrive before their window, we can wait until window start
        start_mt = max(arrival, person["start"])
        end_mt = start_mt + person["min_duration"]
        if end_mt <= person["end"]:
            # Schedule meeting
            wait_here = max(0, start_mt - arrival)
            total_wait += wait_here
            total_travel += t
            itinerary.append({
                "action": "meet",
                "location": person["location"],
                "person": person["name"],
                "start_time": minutes_to_str(start_mt),
                "end_time": minutes_to_str(end_mt),
            })
            current_loc = person["location"]
            current_time = end_mt
            met += 1
            total_meet += person["min_duration"]
        else:
            # Cannot meet in this sequence; skip them
            continue

    return {
        "itinerary": itinerary,
        "met": met,
        "total_meet": total_meet,
        "total_travel": total_travel,
        "total_wait": total_wait,
        "end_time": current_time,
    }

def better(a, b):
    # Return True if a is better than b
    # Primary: more friends met
    if a["met"] != b["met"]:
        return a["met"] > b["met"]
    # Secondary: less waiting time
    if a["total_wait"] != b["total_wait"]:
        return a["total_wait"] < b["total_wait"]
    # Tertiary: earlier finish time
    if a["end_time"] != b["end_time"]:
        return a["end_time"] < b["end_time"]
    # Quaternary: less travel time
    if a["total_travel"] != b["total_travel"]:
        return a["total_travel"] < b["total_travel"]
    # Finally: greater total meeting time (should be same if met count same)
    if a["total_meet"] != b["total_meet"]:
        return a["total_meet"] > b["total_meet"]
    return False

best = None
for order in itertools.permutations(people):
    result = simulate_order(order)
    if best is None or better(result, best):
        best = result

# Prepare output JSON with only the itinerary
output = {
    "itinerary": best["itinerary"]
}

print(json.dumps(output, ensure_ascii=False, indent=2))