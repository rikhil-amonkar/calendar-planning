import json

# Define travel times from Marina District to each location
travel_times = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Sunset District': 19,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Sunset District': 23,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Sunset District': 27,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14
    },
    'Chinatown': {
        'Marina District': 15,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Sunset District': 29,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Sunset District': {
        'Marina District': 21,
        'Embarcadero': 30,
        'Bayview': 22,
        'Union Square': 30,
        'Chinatown': 30,
        'Golden Gate Park': 11,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Mission District': 25
    },
    'Golden Gate Park': {
        'Marina District': 18,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Sunset District': 10,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17
    },
    'Financial District': {
        'Marina District': 17,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Sunset District': 30,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Sunset District': 15,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11
    },
    'Mission District': {
        'Marina District': 20,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Sunset District': 24,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12
    }
}

# List of people with their details
people = [
    {
        'name': 'Joshua',
        'location': 'Embarcadero',
        'start_time': '9:45',
        'end_time': '6:00',
        'duration': 105,
        'travel_time': 14
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'start_time': '9:45',
        'end_time': '8:15',
        'duration': 75,
        'travel_time': 27
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'start_time': '10:45',
        'end_time': '8:15',
        'duration': 120,
        'travel_time': 16
    },
    {
        'name': 'Joseph',
        'location': 'Chinatown',
        'start_time': '7:00',
        'end_time': '3:30',
        'duration': 60,
        'travel_time': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'start_time': '9:00',
        'end_time': '9:45',
        'duration': 45,
        'travel_time': 19
    },
    {
        'name': 'Matthew',
        'location': 'Golden Gate Park',
        'start_time': '11:00',
        'end_time': '7:30',
        'duration': 45,
        'travel_time': 18
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start_time': '10:45',
        'end_time': '11:15',
        'duration': 15,
        'travel_time': 17
    },
    {
        'name': 'Paul',
        'location': 'Haight-Ashbury',
        'start_time': '7:15',
        'end_time': '8:30',
        'duration': 15,
        'travel_time': 16
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'start_time': '5:00',
        'end_time': '9:45',
        'duration': 45,
        'travel_time': 20
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