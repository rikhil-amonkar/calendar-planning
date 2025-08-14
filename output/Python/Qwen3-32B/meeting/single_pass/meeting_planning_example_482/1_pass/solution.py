import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define friends with their details
friends = [
    {
        'name': 'Stephanie',
        'location': 'Mission District',
        'available_start': '8:15',
        'available_end': '13:45',
        'min_duration': 90
    },
    {
        'name': 'Sandra',
        'location': 'Bayview',
        'available_start': '13:00',
        'available_end': '19:30',
        'min_duration': 15
    },
    {
        'name': 'Richard',
        'location': 'Pacific Heights',
        'available_start': '7:15',
        'available_end': '10:15',
        'min_duration': 75
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'available_start': '12:15',
        'available_end': '16:00',
        'min_duration': 120
    },
    {
        'name': 'Jason',
        'location': "Fisherman's Wharf",
        'available_start': '8:30',
        'available_end': '17:45',
        'min_duration': 60
    }
]

# Convert available times to minutes
for f in friends:
    f['available_start_minutes'] = time_str_to_minutes(f['available_start'])
    f['available_end_minutes'] = time_str_to_minutes(f['available_end'])

# Define travel times between locations
travel_times = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Bayview': 18,
        'Pacific Heights': 12,
        'Russian Hill': 17,
        "Fisherman's Wharf": 23
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Bayview': 15,
        'Pacific Heights': 16,
        'Russian Hill': 15,
        "Fisherman's Wharf": 22
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Pacific Heights': 23,
        'Russian Hill': 23,
        "Fisherman's Wharf": 25
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Bayview': 22,
        'Russian Hill': 7,
        "Fisherman's Wharf": 13
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Bayview': 23,
        'Pacific Heights': 7,
        "Fisherman's Wharf": 7
    },
    "Fisherman's Wharf": {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Russian Hill': 7
    }
}

best_schedule = []
max_friends = 0
start_time = 9 * 60  # 9:00 AM in minutes

# Generate all permutations of friends and check validity
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        current_time = start_time
        current_location = 'Haight-Ashbury'
        valid = True
        meetings = []
        for friend in perm:
            # Calculate arrival time at friend's location
            try:
                travel_time = travel_times[current_location][friend['location']]
            except KeyError:
                # This should not happen as all locations are covered
                valid = False
                break
            arrival_time = current_time + travel_time

            # Determine meeting start time
            start_time_meeting = max(arrival_time, friend['available_start_minutes'])

            # Check if there's enough time for the meeting
            end_time_meeting = start_time_meeting + friend['min_duration']
            if end_time_meeting > friend['available_end_minutes']:
                valid = False
                break

            # Update current time and location
            current_time = end_time_meeting
            current_location = friend['location']
            meetings.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(start_time_meeting),
                'end_time': minutes_to_time_str(end_time_meeting)
            })

        if valid:
            if len(meetings) > max_friends:
                max_friends = len(meetings)
                best_schedule = meetings

# Output the result as JSON
result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))