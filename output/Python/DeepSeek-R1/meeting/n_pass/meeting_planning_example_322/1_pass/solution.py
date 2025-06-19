# SOLUTION
import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

# Define travel times
travel_times = {
    "Sunset District": {
        "Russian Hill": 24,
        "Chinatown": 30,
        "Presidio": 16,
        "Fisherman's Wharf": 29
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Chinatown": 9,
        "Presidio": 14,
        "Fisherman's Wharf": 7
    },
    "Chinatown": {
        "Sunset District": 29,
        "Russian Hill": 7,
        "Presidio": 19,
        "Fisherman's Wharf": 8
    },
    "Presidio": {
        "Sunset District": 15,
        "Russian Hill": 14,
        "Chinatown": 21,
        "Fisherman's Wharf": 19
    },
    "Fisherman's Wharf": {
        "Sunset District": 27,
        "Russian Hill": 7,
        "Chinatown": 12,
        "Presidio": 17
    }
}

# Define friends with their constraints
michelle = {
    'name': 'Michelle',
    'location': 'Chinatown',
    'start_avail': 8 * 60 + 15,  # 8:15 AM
    'end_avail': 14 * 60,         # 2:00 PM
    'min_duration': 15
}
robert = {
    'name': 'Robert',
    'location': "Fisherman's Wharf",
    'start_avail': 9 * 60,        # 9:00 AM
    'end_avail': 13 * 60 + 45,    # 1:45 PM
    'min_duration': 30
}
george = {
    'name': 'George',
    'location': 'Presidio',
    'start_avail': 10 * 60 + 30,  # 10:30 AM
    'end_avail': 18 * 60 + 45,    # 6:45 PM
    'min_duration': 30
}
william = {
    'name': 'William',
    'location': 'Russian Hill',
    'start_avail': 18 * 60 + 30,  # 6:30 PM
    'end_avail': 20 * 60 + 45,    # 8:45 PM
    'min_duration': 105
}

day_friends = [michelle, robert, george]

def simulate(sequence):
    current_location = "Sunset District"
    current_time = 9 * 60  # 9:00 AM in minutes
    itinerary = []

    for friend in sequence:
        travel = travel_times[current_location][friend['location']]
        current_time += travel
        start_meeting = max(current_time, friend['start_avail'])
        end_meeting = start_meeting + friend['min_duration']
        
        if end_meeting > friend['end_avail']:
            return None
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        
        current_time = end_meeting
        current_location = friend['location']
    
    return itinerary

best_itinerary = None

# Try meeting all four friends
for perm in itertools.permutations(day_friends):
    seq = list(perm) + [william]
    it = simulate(seq)
    if it is not None:
        best_itinerary = it
        break

# Try meeting three day friends without William
if best_itinerary is None:
    for perm in itertools.permutations(day_friends):
        it = simulate(list(perm))
        if it is not None:
            best_itinerary = it
            break

# Try meeting two day friends and William
if best_itinerary is None:
    for subset in itertools.combinations(day_friends, 2):
        for perm in itertools.permutations(subset):
            seq = list(perm) + [william]
            it = simulate(seq)
            if it is not None:
                best_itinerary = it
                break
        if best_itinerary is not None:
            break

# Try meeting two day friends without William
if best_itinerary is None:
    for subset in itertools.combinations(day_friends, 2):
        for perm in itertools.permutations(subset):
            it = simulate(list(perm))
            if it is not None:
                best_itinerary = it
                break
        if best_itinerary is not None:
            break

# Try meeting one day friend and William
if best_itinerary is None:
    for friend in day_friends:
        seq = [friend, william]
        it = simulate(seq)
        if it is not None:
            best_itinerary = it
            break

# Try meeting one day friend without William
if best_itinerary is None:
    for friend in day_friends:
        it = simulate([friend])
        if it is not None:
            best_itinerary = it
            break

# Try meeting only William
if best_itinerary is None:
    it = simulate([william])
    if it is not None:
        best_itinerary = it

# If no meetings possible, return empty list
if best_itinerary is None:
    best_itinerary = []

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result))