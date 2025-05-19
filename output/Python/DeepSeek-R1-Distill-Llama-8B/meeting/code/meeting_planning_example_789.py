import json

# Define travel times from Union Square to each location
travel_times = {
    'Union Square': {
        'Russian Hill': 13,
        'Alamo Square': 15,
        'Haight-Ashbury': 18,
        'Marina District': 18,
        'Bayview': 15,
        'Chinatown': 7,
        'Presidio': 24,
        'Sunset District': 27,
        'Russian Hill': 10,
        'Alamo Square': 14,
        'Haight-Ashbury': 5,
        'Marina District': 15,
        'Bayview': 16,
        'Chinatown': 15,
        'Presidio': 17,
        'Sunset District': 16
    },
    'Russian Hill': {
        'Union Square': 10,
        'Alamo Square': 15,
        'Haight-Ashbury': 17,
        'Marina District': 7,
        'Bayview': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14,
        'Russian Hill': 13,
        'Haight-Ashbury': 5,
        'Marina District': 15,
        'Bayview': 16,
        'Chinatown': 15,
        'Presidio': 17,
        'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Russian Hill': 17,
        'Alamo Square': 5,
        'Marina District': 17,
        'Bayview': 18,
        'Chinatown': 19,
        'Presidio': 15,
        'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16,
        'Russian Hill': 8,
        'Alamo Square': 15,
        'Haight-Ashbury': 16,
        'Bayview': 27,
        'Chinatown': 15,
        'Presidio': 10,
        'Sunset District': 19
    },
    'Bayview': {
        'Union Square': 18,
        'Russian Hill': 23,
        'Alamo Square': 16,
        'Haight-Ashbury': 19,
        'Marina District': 27,
        'Chinatown': 19,
        'Presidio': 32,
        'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7,
        'Russian Hill': 7,
        'Alamo Square': 17,
        'Haight-Ashbury': 19,
        'Marina District': 12,
        'Bayview': 20,
        'Presidio': 19,
        'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22,
        'Russian Hill': 14,
        'Alamo Square': 19,
        'Haight-Ashbury': 15,
        'Marina District': 11,
        'Bayview': 31,
        'Chinatown': 21,
        'Sunset District': 15
    },
    'Sunset District': {
        'Union Square': 30,
        'Russian Hill': 24,
        'Alamo Square': 17,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Bayview': 22,
        'Chinatown': 30,
        'Presidio': 16
    }
}

# List of people with their details
people = [
    {
        'name': 'Betty',
        'location': 'Russian Hill',
        'start_time': '7:00',
        'end_time': '4:45',
        'duration': 105,
        'travel_time': 13
    },
    {
        'name': 'Melissa',
        'location': 'Alamo Square',
        'start_time': '9:30',
        'end_time': '5:15',
        'duration': 105,
        'travel_time': 15
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'start_time': '12:15',
        'end_time': '7:00',
        'duration': 90,
        'travel_time': 18
    },
    {
        'name': 'Jeffrey',
        'location': 'Marina District',
        'start_time': '12:15',
        'end_time': '6:00',
        'duration': 45,
        'travel_time': 18
    },
    {
        'name': 'James',
        'location': 'Bayview',
        'start_time': '7:30',
        'end_time': '8:00',
        'duration': 90,
        'travel_time': 15
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'start_time': '11:45',
        'end_time': '1:30',
        'duration': 75,
        'travel_time': 7
    },
    {
        'name': 'Timothy',
        'location': 'Presidio',
        'start_time': '12:30',
        'end_time': '2:45',
        'duration': 90,
        'travel_time': 24
    },
    {
        'name': 'Emily',
        'location': 'Sunset District',
        'start_time': '7:30',
        'end_time': '9:30',
        'duration': 120,
        'travel_time': 27
    }
]

# Function to calculate feasible meeting times
def calculate_feasible_meetings(people, travel_times):
    meetings = []
    for person in people:
        location = person['location']
        start_time = person['start_time']
        end_time = person['end_time']
        duration = person['duration']
        travel_time = travel_times['Union Square'][location]
        
        # Convert times to minutes since 9:00 AM
        earliest_start_min = (int(start_time.replace(':', '')) * 60) + 540  # 9:00 AM in minutes
        latest_start_min = (int(end_time.replace(':', '')) * 60) - duration
        
        # Ensure earliest start is at least 9:00 AM
        if earliest_start_min < 540:
            earliest_start_min = 540
        
        if latest_start_min < earliest_start_min:
            continue  # No possible meeting time
        
        meetings.append({
            'name': person['name'],
            'location': location,
            'start_time': earliest_start_min,
            'end_time': latest_start_min
        })
    
    return meetings

# Calculate feasible meeting times
feasible_meetings = calculate_feasible_meetings(people, travel_times)

# Sort meetings by end time
feasible_meetings.sort(key=lambda x: x['end_time'])

# Select non-overlapping meetings
itinerary = []
for meeting in feasible_meetings:
    start = meeting['start_time']
    end = meeting['end_time']
    if not itinerary or end <= itinerary[-1]['end_time']:
        itinerary.append(meeting)

# Convert time to 24-hour format strings
itinerary = [
    {
        'action': 'meet',
        'location': meeting['location'],
        'person': meeting['name'],
        'start_time': f"{meeting['start_time'] // 60 + (meeting['start_time'] % 60 // 10)}:{meeting['start_time'] % 60 // 10 * 10}",
        'end_time': f"{meeting['end_time'] // 60 + (meeting['end_time'] % 60 // 10)}:{meeting['end_time'] % 60 // 10 * 10}"
    }
    for meeting in itinerary
]

# Generate JSON output
output = {
    "itinerary": itinerary
}

print(json.dumps(output))