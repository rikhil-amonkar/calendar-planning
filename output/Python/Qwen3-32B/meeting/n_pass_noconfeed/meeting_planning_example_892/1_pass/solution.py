import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        "name": "Laura",
        "location": "Embarcadero",
        "available_start": 465,  # 7:45 AM
        "available_end": 795,    # 1:15 PM
        "required_duration": 105
    },
    {
        "name": "Charles",
        "location": "Bayview",
        "available_start": 690,  # 11:30 AM
        "available_end": 870,    # 2:30 PM
        "required_duration": 45
    },
    {
        "name": "Robert",
        "location": "Sunset District",
        "available_start": 1005, # 4:45 PM
        "available_end": 1260,   # 9:00 PM
        "required_duration": 30
    },
    {
        "name": "Karen",
        "location": "Richmond District",
        "available_start": 1155, # 7:15 PM
        "available_end": 1290,   # 9:30 PM
        "required_duration": 60
    },
    {
        "name": "Rebecca",
        "location": "Nob Hill",
        "available_start": 975,  # 4:15 PM
        "available_end": 1230,   # 8:30 PM
        "required_duration": 90
    },
    {
        "name": "Margaret",
        "location": "Chinatown",
        "available_start": 855,  # 2:15 PM
        "available_end": 1185,   # 7:45 PM
        "required_duration": 120
    },
    {
        "name": "Patricia",
        "location": "Haight-Ashbury",
        "available_start": 870,  # 2:30 PM
        "available_end": 1230,   # 8:30 PM
        "required_duration": 45
    },
    {
        "name": "Mark",
        "location": "North Beach",
        "available_start": 840,  # 2:00 PM
        "available_end": 1110,   # 6:30 PM
        "required_duration": 105
    },
    {
        "name": "Melissa",
        "location": "Russian Hill",
        "available_start": 780,  # 1:00 PM
        "available_end": 1185,   # 7:45 PM
        "required_duration": 30
    }
]

for friend in friends:
    friend["earliest_start"] = friend["available_start"]
    friend["latest_start"] = friend["available_end"] - friend["required_duration"]

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

best_schedule = None

for k in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, k):
        current_time = 540  # 9:00 AM
        current_location = "Marina District"
        valid = True
        for friend in perm:
            if (current_location, friend["location"]) not in travel_time:
                valid = False
                break
            travel_duration = travel_time[(current_location, friend["location"])]
            arrival_time = current_time + travel_duration
            earliest = friend["earliest_start"]
            latest = friend["latest_start"]
            start_time = max(arrival_time, earliest)
            if start_time > latest:
                valid = False
                break
            current_time = start_time + friend["required_duration"]
            current_location = friend["location"]
        if valid:
            best_schedule = perm
            break
    if best_schedule is not None:
        break

itinerary = []
current_time = 540
current_location = "Marina District"

for friend in best_schedule:
    travel_duration = travel_time[(current_location, friend["location"])]
    arrival_time = current_time + travel_duration
    earliest = friend["earliest_start"]
    latest = friend["latest_start"]
    start_time = max(arrival_time, earliest)
    end_time = start_time + friend["required_duration"]
    itinerary.append({
        "action": "meet",
        "location": friend["location"],
        "person": friend["name"],
        "start_time": to_time_str(start_time),
        "end_time": to_time_str(end_time)
    })
    current_time = end_time
    current_location = friend["location"]

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))