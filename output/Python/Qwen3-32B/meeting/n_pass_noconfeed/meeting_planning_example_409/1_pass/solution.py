import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Fisherman's Wharf": {
        "Bayview": 26,
        "Golden Gate Park": 25,
        "Nob Hill": 11,
        "Marina District": 9,
        "Embarcadero": 8
    },
    "Bayview": {
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22,
        "Nob Hill": 20,
        "Marina District": 25,
        "Embarcadero": 19
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Nob Hill": 20,
        "Marina District": 16,
        "Embarcadero": 25
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "Bayview": 19,
        "Golden Gate Park": 17,
        "Marina District": 11,
        "Embarcadero": 9
    },
    "Marina District": {
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Golden Gate Park": 18,
        "Nob Hill": 12,
        "Embarcadero": 14
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "Bayview": 21,
        "Golden Gate Park": 25,
        "Nob Hill": 10,
        "Marina District": 12
    }
}

friends = [
    {
        "name": "Laura",
        "location": "Nob Hill",
        "start": 8 * 60 + 45,  # 525
        "end": 16 * 60 + 15,   # 975
        "duration": 30
    },
    {
        "name": "Thomas",
        "location": "Bayview",
        "start": 15 * 60 + 30,  # 930
        "end": 18 * 60 + 30,    # 1110
        "duration": 120
    },
    {
        "name": "Stephanie",
        "location": "Golden Gate Park",
        "start": 18 * 60 + 30,  # 1110
        "end": 21 * 60 + 45,    # 1305
        "duration": 30
    },
    {
        "name": "Betty",
        "location": "Marina District",
        "start": 18 * 60 + 45,  # 1125
        "end": 21 * 60 + 45,    # 1305
        "duration": 45
    },
    {
        "name": "Patricia",
        "location": "Embarcadero",
        "start": 17 * 60 + 30,  # 1050
        "end": 22 * 60,         # 1320
        "duration": 45
    }
]

for k in range(5, 0, -1):
    for perm in itertools.permutations(friends, k):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = "Fisherman's Wharf"
        feasible = True
        itinerary = []
        for friend in perm:
            destination = friend["location"]
            if current_location not in travel_times or destination not in travel_times[current_location]:
                feasible = False
                break
            travel_time = travel_times[current_location][destination]
            arrival_time = current_time + travel_time
            friend_start = friend["start"]
            friend_end = friend["end"]
            meeting_start = max(arrival_time, friend_start)
            meeting_end = meeting_start + friend["duration"]
            if meeting_end > friend_end:
                feasible = False
                break
            itinerary.append({
                "action": "meet",
                "location": destination,
                "person": friend["name"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            })
            current_time = meeting_end
            current_location = destination
        if feasible:
            print(json.dumps({"itinerary": itinerary}))
            exit()

print(json.dumps({"itinerary": []}))