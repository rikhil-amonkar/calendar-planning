import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

def build_schedule(perm, travel_times, start_time, start_location):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in perm:
        travel_duration = travel_times[current_location][friend['location']]
        current_time += travel_duration
        meeting_start = max(current_time, friend['start'])
        meeting_end = meeting_start + friend['min_duration']
        if meeting_end > friend['end']:
            return False, None
        itinerary.append({
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    return True, itinerary

travel_times = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24
    }
}

friends = [
    {'name': 'Rebecca', 'location': 'Bayview', 'start': 540, 'end': 765, 'min_duration': 90},
    {'name': 'Amanda', 'location': 'Pacific Heights', 'start': 1110, 'end': 1305, 'min_duration': 90},
    {'name': 'James', 'location': 'Alamo Square', 'start': 585, 'end': 1275, 'min_duration': 90},
    {'name': 'Sarah', 'location': "Fisherman's Wharf", 'start': 480, 'end': 1290, 'min_duration': 90},
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'start': 540, 'end': 1125, 'min_duration': 90}
]

start_time = 540
start_location = "The Castro"
n = len(friends)
found = False
result_itinerary = None

for num in range(n, 0, -1):
    for subset in itertools.combinations(friends, num):
        for perm in itertools.permutations(subset):
            feasible, itinerary = build_schedule(perm, travel_times, start_time, start_location)
            if feasible:
                found = True
                result_itinerary = itinerary
                break
        if found:
            break
    if found:
        break

if found:
    result = {"itinerary": []}
    for meet in result_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": meet['location'],
            "person": meet['person'],
            "start_time": meet['start_time'],
            "end_time": meet['end_time']
        })
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))