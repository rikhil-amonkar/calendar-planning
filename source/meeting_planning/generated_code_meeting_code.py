import itertools
import json

travel_times = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29,
        'Presidio': 19
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24,
        'Presidio': 25
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16,
        'Presidio': 18
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21,
        'Presidio': 11
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26,
        'Presidio': 24
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Presidio': 11
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11,
        'Presidio': 15
    },
    'Presidio': {
        'Chinatown': 21,
        'Mission District': 26,
        'Alamo Square': 18,
        'Pacific Heights': 11,
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Sunset District': 15
    }
}

friends = [
    {
        'name': 'David',
        'location': 'Mission District',
        'start': 480,  # 8:00 AM
        'end': 1155,   # 7:45 PM
        'duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Alamo Square',
        'start': 840,  # 2:00 PM
        'end': 1155,   # 7:45 PM
        'duration': 120
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'start': 1020, # 5:00 PM
        'end': 1200,   # 8:00 PM
        'duration': 15
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'start': 1260, # 9:45 PM
        'end': 1350,   # 10:45 PM
        'duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Golden Gate Park',
        'start': 420,  # 7:00 AM
        'end': 1115,   # 6:15 PM
        'duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'start': 1125, # 5:45 PM
        'end': 1290,   # 9:15 PM
        'duration': 15
    },
    {
        'name': 'Carol',
        'location': 'Presidio',
        'start': 495,  # 8:15 AM
        'end': 555,    # 9:15 AM
        'duration': 30
    }
]

def time_to_str(minutes):
    hour = minutes // 60
    min = minutes % 60
    suffix = 'AM' if hour < 12 else 'PM'
    hour = hour % 12
    if hour == 0:
        hour = 12
    return f"{hour}:{min:02}{suffix}"

def compute_schedule():
    best_schedule = None
    max_met = 0
    start_location = 'Chinatown'
    current_time = 540  # 9:00 AM

    for perm in itertools.permutations(friends):
        schedule = []
        current_time = 540
        current_location = start_location
        met_count = 0
        valid = True

        # Starting point
        schedule.append({
            'action': 'start',
            'location': current_location,
            'time': time_to_str(current_time)
        })

        for friend in perm:
            # Travel to friend's location
            travel_duration = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_duration

            schedule.append({
                'action': 'travel',
                'location': current_location,
                'duration': travel_duration,
                'time': time_to_str(current_time),
                'to': friend['location']
            })

            # Calculate wait time
            wait_start = arrival_time
            available_start = friend['start']
            wait_end = max(wait_start, available_start)
            wait_duration = wait_end - wait_start

            if wait_duration > 0:
                schedule.append({
                    'action': 'wait',
                    'location': friend['location'],
                    'time': time_to_str(wait_start)
                })

            # Check if meeting fits
            meeting_end = wait_end + friend['duration']
            if meeting_end > friend['end']:
                valid = False
                break

            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'duration': friend['duration'],
                'time': time_to_str(wait_end)
            })

            current_time = meeting_end
            current_location = friend['location']
            met_count += 1

        if valid and met_count > max_met:
            best_schedule = schedule
            max_met = met_count

    return best_schedule

schedule = compute_schedule()
print(json.dumps({'schedule': schedule}))