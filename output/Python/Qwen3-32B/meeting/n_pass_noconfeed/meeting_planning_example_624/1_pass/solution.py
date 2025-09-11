import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define the travel times
travel_time = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        'Chinatown': 23,
        'Alamo Square': 10,
        'North Beach': 24,
        'Russian Hill': 19,
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        "Fisherman's Wharf": 23,
        "The Castro": 6,
        'Chinatown': 19,
        'Alamo Square': 5,
        'North Beach': 19,
        'Russian Hill': 17,
    },
    "Fisherman's Wharf": {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 22,
        "The Castro": 26,
        'Chinatown': 12,
        'Alamo Square': 20,
        'North Beach': 6,
        'Russian Hill': 7,
    },
    "The Castro": {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 6,
        "Fisherman's Wharf": 24,
        'Chinatown': 20,
        'Alamo Square': 8,
        'North Beach': 20,
        'Russian Hill': 18,
    },
    'Chinatown': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        "Fisherman's Wharf": 8,
        "The Castro": 22,
        'Alamo Square': 17,
        'North Beach': 3,
        'Russian Hill': 7,
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Haight-Ashbury': 5,
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        'Chinatown': 16,
        'North Beach': 15,
        'Russian Hill': 13,
    },
    'North Beach': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Russian Hill': 4,
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Haight-Ashbury': 17,
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        'Chinatown': 9,
        'Alamo Square': 15,
        'North Beach': 5,
    },
}

# Define friends
friends = [
    {
        'name': 'Karen',
        'location': "The Castro",
        'available_start': 435,  # 7:15 AM
        'available_end': 840,    # 2:00 PM
        'required_duration': 75,
        'latest_start': 840 - 75,
    },
    {
        'name': 'Deborah',
        'location': "Alamo Square",
        'available_start': 720,  # 12:00 PM
        'available_end': 900,    # 3:00 PM
        'required_duration': 105,
        'latest_start': 900 - 105,
    },
    {
        'name': 'Laura',
        'location': "Fisherman's Wharf",
        'available_start': 705,  # 11:45 AM
        'available_end': 1290,   # 9:30 PM
        'required_duration': 60,
        'latest_start': 1290 - 60,
    },
    {
        'name': 'Elizabeth',
        'location': "Chinatown",
        'available_start': 735,  # 12:15 PM
        'available_end': 1290,   # 9:30 PM
        'required_duration': 75,
        'latest_start': 1290 - 75,
    },
    {
        'name': 'Jason',
        'location': "North Beach",
        'available_start': 885,  # 2:45 PM
        'available_end': 1140,   # 7:00 PM
        'required_duration': 90,
        'latest_start': 1140 - 90,
    },
    {
        'name': 'Steven',
        'location': "Russian Hill",
        'available_start': 885,  # 2:45 PM
        'available_end': 1110,   # 6:30 PM
        'required_duration': 120,
        'latest_start': 1110 - 120,
    },
    {
        'name': 'Carol',
        'location': "Haight-Ashbury",
        'available_start': 1290,  # 9:30 PM
        'available_end': 1350,    # 10:30 PM
        'required_duration': 60,
        'latest_start': 1350 - 60,
    },
]

best_schedule = []
best_count = 0

# Generate all permutations
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Golden Gate Park'
    schedule = []
    met_count = 0

    for friend in perm:
        # Calculate travel time
        dest = friend['location']
        travel_minutes = travel_time[current_location][dest]
        current_time += travel_minutes

        # Check if current_time is beyond latest_start
        if current_time > friend['latest_start']:
            break

        # Determine start_meeting time
        start_meeting = max(current_time, friend['available_start'])

        # Check if start_meeting exceeds latest_start
        if start_meeting > friend['latest_start']:
            break

        # Update current_time to end of meeting
        current_time = start_meeting + friend['required_duration']
        current_location = dest

        # Add to schedule
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_meeting),
            'end_time': minutes_to_time_str(current_time)
        })
        met_count += 1

    # Update best schedule
    if met_count > best_count:
        best_count = met_count
        best_schedule = schedule
    elif met_count == best_count and best_count > 0:
        # Optional: choose the one with earliest end time?
        # For simplicity, we'll just keep the first one found with max count
        pass

# Output the result as JSON
result = {
    "itinerary": best_schedule
}
print(json.dumps(result, indent=2))