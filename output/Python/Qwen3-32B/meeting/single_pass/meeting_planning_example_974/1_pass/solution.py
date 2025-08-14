import itertools
import json

travel_times = {
    "Sunset District": {
        "Presidio": 16,
        "Nob Hill": 27,
        "Pacific Heights": 21,
        "Mission District": 25,
        "Marina District": 21,
        "North Beach": 28,
        "Russian Hill": 24,
        "Richmond District": 12,
        "Embarcadero": 30,
        "Alamo Square": 17,
    },
    "Presidio": {
        "Sunset District": 15,
        "Nob Hill": 18,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Marina District": 11,
        "North Beach": 18,
        "Russian Hill": 14,
        "Richmond District": 7,
        "Embarcadero": 20,
        "Alamo Square": 19,
    },
    "Nob Hill": {
        "Sunset District": 24,
        "Presidio": 17,
        "Pacific Heights": 8,
        "Mission District": 13,
        "Marina District": 11,
        "North Beach": 8,
        "Russian Hill": 5,
        "Richmond District": 14,
        "Embarcadero": 9,
        "Alamo Square": 11,
    },
    "Pacific Heights": {
        "Sunset District": 21,
        "Presidio": 11,
        "Nob Hill": 8,
        "Mission District": 15,
        "Marina District": 6,
        "North Beach": 9,
        "Russian Hill": 7,
        "Richmond District": 12,
        "Embarcadero": 10,
        "Alamo Square": 10,
    },
    "Mission District": {
        "Sunset District": 24,
        "Presidio": 25,
        "Nob Hill": 12,
        "Pacific Heights": 16,
        "Marina District": 19,
        "North Beach": 17,
        "Russian Hill": 15,
        "Richmond District": 20,
        "Embarcadero": 19,
        "Alamo Square": 11,
    },
    "Marina District": {
        "Sunset District": 19,
        "Presidio": 10,
        "Nob Hill": 12,
        "Pacific Heights": 7,
        "Mission District": 20,
        "North Beach": 11,
        "Russian Hill": 8,
        "Richmond District": 11,
        "Embarcadero": 14,
        "Alamo Square": 15,
    },
    "North Beach": {
        "Sunset District": 27,
        "Presidio": 17,
        "Nob Hill": 7,
        "Pacific Heights": 8,
        "Mission District": 18,
        "Marina District": 9,
        "Russian Hill": 4,
        "Richmond District": 18,
        "Embarcadero": 6,
        "Alamo Square": 16,
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Presidio": 14,
        "Nob Hill": 5,
        "Pacific Heights": 7,
        "Mission District": 16,
        "Marina District": 7,
        "North Beach": 5,
        "Richmond District": 14,
        "Embarcadero": 8,
        "Alamo Square": 15,
    },
    "Richmond District": {
        "Sunset District": 11,
        "Presidio": 7,
        "Nob Hill": 17,
        "Pacific Heights": 10,
        "Mission District": 20,
        "Marina District": 9,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19,
        "Alamo Square": 13,
    },
    "Embarcadero": {
        "Sunset District": 30,
        "Presidio": 20,
        "Nob Hill": 10,
        "Pacific Heights": 11,
        "Mission District": 20,
        "Marina District": 12,
        "North Beach": 5,
        "Russian Hill": 8,
        "Richmond District": 21,
        "Alamo Square": 19,
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Presidio": 17,
        "Nob Hill": 11,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Marina District": 15,
        "North Beach": 15,
        "Russian Hill": 13,
        "Richmond District": 11,
        "Embarcadero": 16,
    },
}

friends = [
    {
        "name": "Charles",
        "location": "Presidio",
        "start_time": 795,
        "end_time": 900,
        "required_duration": 105,
    },
    {
        "name": "Robert",
        "location": "Nob Hill",
        "start_time": 795,
        "end_time": 1050,
        "required_duration": 90,
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start_time": 885,
        "end_time": 1320,
        "required_duration": 105,
    },
    {
        "name": "Brian",
        "location": "Mission District",
        "start_time": 930,
        "end_time": 1320,
        "required_duration": 60,
    },
    {
        "name": "Kimberly",
        "location": "Marina District",
        "start_time": 1020,
        "end_time": 1185,
        "required_duration": 75,
    },
    {
        "name": "David",
        "location": "North Beach",
        "start_time": 885,
        "end_time": 990,
        "required_duration": 75,
    },
    {
        "name": "William",
        "location": "Russian Hill",
        "start_time": 750,
        "end_time": 1155,
        "required_duration": 120,
    },
    {
        "name": "Jeffrey",
        "location": "Richmond District",
        "start_time": 720,
        "end_time": 1155,
        "required_duration": 45,
    },
    {
        "name": "Karen",
        "location": "Embarcadero",
        "start_time": 855,
        "end_time": 1245,
        "required_duration": 60,
    },
    {
        "name": "Joshua",
        "location": "Alamo Square",
        "start_time": 1125,
        "end_time": 1320,
        "required_duration": 60,
    },
]

def is_valid(perm):
    current_time = 540  # 9:00 AM in minutes
    current_location = "Sunset District"
    for friend in perm:
        dest = friend["location"]
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, friend["start_time"])
        end_time = start_time + friend["required_duration"]
        if end_time > friend["end_time"]:
            return False
        current_time = end_time
        current_location = dest
    return True

best_itinerary = None

for k in range(10, 0, -1):
    for combination in itertools.combinations(friends, k):
        for perm in itertools.permutations(combination):
            if is_valid(perm):
                best_itinerary = perm
                result = []
                current_time = 540
                current_location = "Sunset District"
                for friend in best_itinerary:
                    dest = friend["location"]
                    travel_time = travel_times[current_location][dest]
                    arrival_time = current_time + travel_time
                    start_time = max(arrival_time, friend["start_time"])
                    end_time = start_time + friend["required_duration"]
                    start_hm = f"{start_time//60}:{start_time%60:02d}"
                    end_hm = f"{end_time//60}:{end_time%60:02d}"
                    result.append({
                        "action": "meet",
                        "location": dest,
                        "person": friend["name"],
                        "start_time": start_hm,
                        "end_time": end_hm
                    })
                    current_time = end_time
                    current_location = dest
                print(json.dumps({"itinerary": result}))
                exit()

print(json.dumps({"itinerary": []}))