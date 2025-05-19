import json

# Define travel times from Marina District to each location
travel_times = {
    'Marina District': {
        'Bayview': 27,
        'Sunset District': 19,
        'Richmond District': 11,
        'Nob Hill': 12,
        'Chinatown': 15,
        'Haight-Ashbury': 16,
        'North Beach': 11,
        'Russian Hill': 8,
        'Embarcadero': 14
    },
    'Bayview': {
        'Marina District': 27,
        'Sunset District': 23,
        'Richmond District': 25,
        'Nob Hill': 20,
        'Chinatown': 19,
        'Haight-Ashbury': 19,
        'North Beach': 22,
        'Russian Hill': 23,
        'Embarcadero': 19
    },
    'Sunset District': {
        'Marina District': 21,
        'Bayview': 22,
        'Richmond District': 12,
        'Nob Hill': 27,
        'Chinatown': 30,
        'Haight-Ashbury': 15,
        'North Beach': 28,
        'Russian Hill': 24,
        'Embarcadero': 30
    },
    'Richmond District': {
        'Marina District': 9,
        'Bayview': 27,
        'Sunset District': 11,
        'Nob Hill': 17,
        'Chinatown': 20,
        'Haight-Ashbury': 10,
        'North Beach': 17,
        'Russian Hill': 13,
        'Embarcadero': 19
    },
    'Nob Hill': {
        'Marina District': 11,
        'Bayview': 19,
        'Sunset District': 24,
        'Richmond District': 14,
        'Chinatown': 6,
        'Haight-Ashbury': 13,
        'North Beach': 8,
        'Russian Hill': 5,
        'Embarcadero': 9
    },
    'Chinatown': {
        'Marina District': 15,
        'Bayview': 20,
        'Sunset District': 29,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Haight-Ashbury': 19,
        'North Beach': 3,
        'Russian Hill': 7,
        'Embarcadero': 5
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Bayview': 18,
        'Sunset District': 15,
        'Richmond District': 10,
        'Nob Hill': 15,
        'Chinatown': 19,
        'North Beach': 19,
        'Russian Hill': 17,
        'Embarcadero': 20
    },
    'North Beach': {
        'Marina District': 9,
        'Bayview': 25,
        'Sunset District': 27,
        'Richmond District': 18,
        'Nob Hill': 7,
        'Chinatown': 6,
        'Haight-Ashbury': 18,
        'Russian Hill': 4,
        'Embarcadero': 6
    },
    'Russian Hill': {
        'Marina District': 8,
        'Bayview': 23,
        'Sunset District': 23,
        'Richmond District': 13,
        'Nob Hill': 5,
        'Chinatown': 9,
        'Haight-Ashbury': 17,
        'North Beach': 5,
        'Embarcadero': 8
    },
    'Embarcadero': {
        'Marina District': 14,
        'Bayview': 21,
        'Sunset District': 30,
        'Richmond District': 21,
        'Nob Hill': 10,
        'Chinatown': 7,
        'Haight-Ashbury': 21,
        'North Beach': 5,
        'Russian Hill': 8
    }
}

# List of people with their details
people = [
    {
        'name': 'Charles',
        'location': 'Bayview',
        'start_time': '11:30',
        'end_time': '2:30',
        'duration': 45,
        'travel_time': 27
    },
    {
        'name': 'Robert',
        'location': 'Sunset District',
        'start_time': '4:45',
        'end_time': '9:00',
        'duration': 30,
        'travel_time': 19
    },
    {
        'name': 'Karen',
        'location': 'Richmond District',
        'start_time': '7:15',
        'end_time': '9:30',
        'duration': 60,
        'travel_time': 11
    },
    {
        'name': 'Rebecca',
        'location': 'Nob Hill',
        'start_time': '4:15',
        'end_time': '8:30',
        'duration': 90,
        'travel_time': 12
    },
    {
        'name': 'Margaret',
        'location': 'Chinatown',
        'start_time': '2:15',
        'end_time': '7:45',
        'duration': 120,
        'travel_time': 15
    },
    {
        'name': 'Patricia',
        'location': 'Haight-Ashbury',
        'start_time': '2:30',
        'end_time': '8:30',
        'duration': 45,
        'travel_time': 16
    },
    {
        'name': 'Mark',
        'location': 'North Beach',
        'start_time': '2:00',
        'end_time': '6:30',
        'duration': 105,
        'travel_time': 11
    },
    {
        'name': 'Melissa',
        'location': 'Russian Hill',
        'start_time': '1:00',
        'end_time': '7:45',
        'duration': 30,
        'travel_time': 8
    },
    {
        'name': 'Laura',
        'location': 'Embarcadero',
        'start_time': '7:45',
        'end_time': '1:15',
        'duration': 105,
        'travel_time': 14
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
        travel_time = travel_times['Marina District'][location]
        
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