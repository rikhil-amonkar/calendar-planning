import itertools
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Sarah',
        'location': 'NB',
        'available_start': 960,  # 4:00 PM
        'available_end': 1095,   # 6:15 PM
        'required_duration': 60
    },
    {
        'name': 'Jeffrey',
        'location': 'US',
        'available_start': 900,  # 3:00 PM
        'available_end': 1320,   # 10:00 PM
        'required_duration': 75
    },
    {
        'name': 'Brian',
        'location': 'AS',
        'available_start': 960,  # 4:00 PM
        'available_end': 1050,   # 5:30 PM
        'required_duration': 75
    }
]

# Define travel times between locations (in minutes)
travel_times = {
    'SD': {'NB': 29, 'US': 30, 'AS': 17},
    'NB': {'SD': 27, 'US': 7, 'AS': 16},
    'US': {'SD': 26, 'NB': 10, 'AS': 15},
    'AS': {'SD': 16, 'NB': 15, 'US': 14}
}

best_itinerary = []
best_length = 0
best_end_time = float('inf')

# Check permutations of length 3, then 2, then 1
for r in [3, 2, 1]:
    for perm in itertools.permutations(friends, r):
        current_time = 540  # 9:00 AM
        current_location = 'SD'
        itinerary = []
        valid = True

        for friend in perm:
            dest = friend['location']
            travel_time = travel_times[current_location].get(dest, float('inf'))
            arrival_time = current_time + travel_time

            start_time = max(arrival_time, friend['available_start'])
            end_time_meeting = start_time + friend['required_duration']

            if end_time_meeting > friend['available_end']:
                valid = False
                break

            itinerary.append({
                'action': 'meet',
                'location': dest,
                'person': friend['name'],
                'start_time': to_time_str(start_time),
                'end_time': to_time_str(end_time_meeting)
            })

            current_time = end_time_meeting
            current_location = dest

        if valid:
            current_length = len(itinerary)
            current_end_time = current_time
            if current_length > best_length:
                best_length = current_length
                best_itinerary = itinerary
                best_end_time = current_end_time
            elif current_length == best_length:
                if current_end_time < best_end_time:
                    best_itinerary = itinerary
                    best_end_time = current_end_time

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))