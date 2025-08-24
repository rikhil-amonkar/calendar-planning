import json
from copy import deepcopy

def parse_time(s):
    # s is like '9:00', '13:30'
    h, m = map(int, s.split(':'))
    return h * 60 + m

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times (minutes), directed
travel = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

# Meeting constraints
friends = [
    {
        "name": "Steven",
        "location": "North Beach",
        "start": "17:30",
        "end": "20:30",
        "min_duration": 15
    },
    {
        "name": "Sarah",
        "location": "Golden Gate Park",
        "start": "17:00",
        "end": "19:15",
        "min_duration": 75
    },
    {
        "name": "Brian",
        "location": "Embarcadero",
        "start": "14:15",
        "end": "16:00",
        "min_duration": 105
    },
    {
        "name": "Stephanie",
        "location": "Haight-Ashbury",
        "start": "10:15",
        "end": "12:15",
        "min_duration": 75
    },
    {
        "name": "Melissa",
        "location": "Richmond District",
        "start": "14:00",
        "end": "19:30",
        "min_duration": 30
    },
    {
        "name": "Nancy",
        "location": "Nob Hill",
        "start": "8:15",
        "end": "12:45",
        "min_duration": 90
    },
    {
        "name": "David",
        "location": "Marina District",
        "start": "11:15",
        "end": "13:15",
        "min_duration": 120
    },
    {
        "name": "James",
        "location": "Presidio",
        "start": "15:00",
        "end": "18:15",
        "min_duration": 120
    },
    {
        "name": "Elizabeth",
        "location": "Union Square",
        "start": "11:30",
        "end": "21:00",
        "min_duration": 60
    },
    {
        "name": "Robert",
        "location": "Financial District",
        "start": "13:15",
        "end": "15:15",
        "min_duration": 45
    }
]

# Convert times to minutes
for f in friends:
    f["start_min"] = parse_time(f["start"])
    f["end_min"] = parse_time(f["end"])

# Sort friends (optional heuristic) by window end then start
friends_sorted = sorted(friends, key=lambda x: (x["end_min"], x["start_min"]))

start_location = "The Castro"
start_time = parse_time("9:00")

best_schedule = []
best_count = 0

def feasible_next(current_loc, current_time, friend):
    if current_loc not in travel or friend["location"] not in travel[current_loc]:
        return None
    arrive = current_time + travel[current_loc][friend["location"]]
    start = max(arrive, friend["start_min"])
    end = start + friend["min_duration"]
    if end <= friend["end_min"]:
        return (start, end)
    return None

def search(current_loc, current_time, remaining, current_schedule):
    global best_schedule, best_count

    # Update best if improved
    if len(current_schedule) > best_count:
        best_count = len(current_schedule)
        best_schedule = deepcopy(current_schedule)

    # Simple optimistic bound pruning: if even meeting all remaining can't beat best, stop
    if len(current_schedule) + len(remaining) <= best_count:
        return

    # Explore next options
    for idx, fr in enumerate(remaining):
        feas = feasible_next(current_loc, current_time, fr)
        if feas is None:
            continue
        start, end = feas
        entry = {
            "action": "meet",
            "location": fr["location"],
            "person": fr["name"],
            "start_time_min": start,
            "end_time_min": end
        }
        next_remaining = remaining[:idx] + remaining[idx+1:]
        current_schedule.append(entry)
        search(fr["location"], end, next_remaining, current_schedule)
        current_schedule.pop()

# Start search
search(start_location, start_time, friends_sorted, [])

# Convert times to H:MM and prepare output
output = {"itinerary": []}
for e in best_schedule:
    output["itinerary"].append({
        "action": "meet",
        "location": e["location"],
        "person": e["person"],
        "start_time": format_time(e["start_time_min"]),
        "end_time": format_time(e["end_time_min"])
    })

print(json.dumps(output, ensure_ascii=False))