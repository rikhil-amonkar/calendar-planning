import json
from copy import deepcopy

friends = [
    {
        "name": "Charles",
        "location": "Bayview",
        "start": 690,
        "end": 870,
        "duration": 45
    },
    {
        "name": "Robert",
        "location": "Sunset District",
        "start": 1005,
        "end": 1260,
        "duration": 30
    },
    {
        "name": "Karen",
        "location": "Richmond District",
        "start": 1155,
        "end": 1290,
        "duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Nob Hill",
        "start": 975,
        "end": 1230,
        "duration": 90
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "start": 855,
        "end": 1185,
        "duration": 120
    },
    {
        "name": "Patricia",
        "location": "Haight-Ashbury",
        "start": 870,
        "end": 1230,
        "duration": 45
    },
    {
        "name": "Mark",
        "location": "North Beach",
        "start": 840,
        "end": 1110,
        "duration": 105
    },
    {
        "name": "Melissa",
        "location": "Russian Hill",
        "start": 780,
        "end": 1185,
        "duration": 30
    },
    {
        "name": "Laura",
        "location": "Embarcadero",
        "start": 465,
        "end": 795,
        "duration": 105
    }
]

travel_time = {
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Embarcadero"): 14,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Embarcadero"): 19,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Nob Hill"): 27,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Embarcadero"): 30,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Embarcadero"): 19,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Embarcadero"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Bayview"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Embarcadero"): 5,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Embarcadero"): 6,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Embarcadero"): 8,
    ("Embarcadero", "Marina District"): 12,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Russian Hill"): 8,
}

best_itinerary = []
best_count = 0
best_duration = 0

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def backtrack(current_location, current_time, met, itinerary):
    global best_itinerary, best_count, best_duration
    current_count = len(met)
    current_duration = sum(f["duration"] for f in met)
    
    if current_count > best_count or (current_count == best_count and current_duration > best_duration):
        best_count = current_count
        best_duration = current_duration
        best_itinerary = deepcopy(itinerary)
    
    for friend in friends:
        if any(f["name"] == friend["name"] for f in met):
            continue
        from_loc = current_location
        to_loc = friend["location"]
        tt = travel_time.get((from_loc, to_loc))
        if tt is None:
            continue
        arrival = current_time + tt
        start = max(arrival, friend["start"])
        end = start + friend["duration"]
        if end > friend["end"]:
            continue
        new_met = met.copy()
        new_met.append(friend)
        new_entry = {
            "action": "meet",
            "location": to_loc,
            "person": friend["name"],
            "start_time": start,
            "end_time": end
        }
        new_itinerary = itinerary.copy()
        new_itinerary.append(new_entry)
        backtrack(to_loc, end, new_met, new_itinerary)

backtrack("Marina District", 540, [], [])

formatted = []
for entry in best_itinerary:
    start = entry["start_time"]
    end = entry["end_time"]
    formatted.append({
        "action": "meet",
        "location": entry["location"],
        "person": entry["person"],
        "start_time": format_time(start).lstrip("0") if format_time(start).startswith("0") else format_time(start),
        "end_time": format_time(end).lstrip("0") if format_time(end).startswith("0") else format_time(end)
    })

print(json.dumps({"itinerary": formatted}, indent=2))