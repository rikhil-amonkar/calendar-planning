import itertools
import json

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Mission District'): 24,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Mission District'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Mission District'): 16,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Golden Gate Park'): 17
}

friends = [
    {
        'name': 'Charles',
        'location': 'Alamo Square',
        'available_start': 18 * 60,  # 1080
        'available_end': 20 * 60 + 45,  # 1245
        'required_duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Russian Hill',
        'available_start': 9 * 60,  # 540
        'available_end': 16 * 60,  # 960
        'required_duration': 30
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'available_start': 8 * 60,  # 480
        'available_end': 13 * 60 + 30,  # 810
        'required_duration': 15
    },
    {
        'name': 'Stephanie',
        'location': 'Mission District',
        'available_start': 20 * 60 + 30,  # 1230
        'available_end': 22 * 60,  # 1320
        'required_duration': 90
    }
]

best_itinerary = []
best_length = 0

# Generate all permutations for lengths from 4 down to 1
for r in range(4, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Sunset District'
        itinerary = []
        valid = True

        for friend in perm:
            # Calculate travel time
            travel_time = travel_times.get((current_location, friend['location']), float('inf'))
            arrival_time = current_time + travel_time

            # Check if meeting can be scheduled
            available_start = friend['available_start']
            available_end = friend['available_end']
            required = friend['required_duration']

            earliest_start = max(arrival_time, available_start)
            latest_start = available_end - required

            if earliest_start > latest_start:
                valid = False
                break

            # Schedule meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + required

            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(meeting_start),
                'end_time': minutes_to_time_str(meeting_end)
            })

            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']

        if valid:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == best_length:
                # In case of tie, pick the one with earliest end time?
                # For simplicity, we'll take the first found
                pass

# Output the result as JSON
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))