import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Sunset District': {
        'Chinatown': 30,
        'Russian Hill': 24,
        'North Beach': 29
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'North Beach': 3
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'North Beach': 5
    },
    'North Beach': {
        'Sunset District': 27,
        'Chinatown': 6,
        'Russian Hill': 4
    }
}

friends = [
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'available_start': 8 * 60 + 15,  # 495
        'available_end': 13 * 60 + 30,   # 810
        'required': 105
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': 13 * 60 + 15, # 795
        'available_end': 14 * 60 + 30,  # 870
        'required': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Russian Hill',
        'available_start': 19 * 60 + 30, # 1170
        'available_end': 21 * 60 + 15,  # 1275
        'required': 105
    }
]

best_itinerary = []
best_length = 0

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Sunset District'
    possible = True
    itinerary = []
    for friend in perm:
        next_location = friend['location']
        # Get travel time from current_location to next_location
        travel_time = travel_times[current_location][next_location]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required']
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        if earliest_start > latest_start:
            possible = False
            break
        # Schedule the meeting
        start = earliest_start
        end = start + required
        itinerary.append({
            'friend': friend,
            'start': start,
            'end': end
        })
        current_time = end
        current_location = next_location
    if possible:
        if len(itinerary) > best_length:
            best_length = len(itinerary)
            best_itinerary = itinerary

# Now, convert best_itinerary to the required JSON format
result = {
    "itinerary": []
}

for entry in best_itinerary:
    friend = entry['friend']
    start_time = minutes_to_time_str(entry['start'])
    end_time = minutes_to_time_str(entry['end'])
    result["itinerary"].append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

print(json.dumps(result, indent=2))