import json

# Define travel times from Nob Hill to each location
travel_times = {
    'Nob Hill': {
        'Embarcadero': 9,
        'The Castro': 17,
        'Haight-Ashbury': 13,
        'Union Square': 7,
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Russian Hill': 5
    },
    'Embarcadero': {
        'Nob Hill': 10,
        'The Castro': 25,
        'Haight-Ashbury': 21,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 11,
        'Chinatown': 7,
        'Golden Gate Park': 25,
        'Marina District': 12,
        'Russian Hill': 8
    },
    'The Castro': {
        'Nob Hill': 16,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Union Square': 19,
        'North Beach': 20,
        'Pacific Heights': 16,
        'Chinatown': 22,
        'Golden Gate Park': 11,
        'Marina District': 21,
        'Russian Hill': 18
    },
    'Haight-Ashbury': {
        'Nob Hill': 15,
        'Embarcadero': 20,
        'The Castro': 6,
        'Union Square': 19,
        'North Beach': 19,
        'Pacific Heights': 12,
        'Chinatown': 19,
        'Golden Gate Park': 7,
        'Marina District': 17,
        'Russian Hill': 17
    },
    'Union Square': {
        'Nob Hill': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Haight-Ashbury': 18,
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Golden Gate Park': 22,
        'Marina District': 18,
        'Russian Hill': 13
    },
    'North Beach': {
        'Nob Hill': 7,
        'Embarcadero': 6,
        'The Castro': 23,
        'Haight-Ashbury': 18,
        'Union Square': 7,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 22,
        'Marina District': 9,
        'Russian Hill': 4
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Embarcadero': 10,
        'The Castro': 16,
        'Haight-Ashbury': 11,
        'Union Square': 12,
        'North Beach': 9,
        'Chinatown': 11,
        'Golden Gate Park': 15,
        'Marina District': 6,
        'Russian Hill': 7
    },
    'Chinatown': {
        'Nob Hill': 9,
        'Embarcadero': 5,
        'The Castro': 22,
        'Haight-Ashbury': 19,
        'Union Square': 7,
        'North Beach': 3,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Marina District': 12,
        'Russian Hill': 7
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Embarcadero': 25,
        'The Castro': 13,
        'Haight-Ashbury': 7,
        'Union Square': 22,
        'North Beach': 23,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Marina District': 16,
        'Russian Hill': 19
    },
    'Marina District': {
        'Nob Hill': 12,
        'Embarcadero': 14,
        'The Castro': 22,
        'Haight-Ashbury': 16,
        'Union Square': 16,
        'North Beach': 11,
        'Pacific Heights': 7,
        'Chinatown': 15,
        'Golden Gate Park': 18,
        'Russian Hill': 8
    },
    'Russian Hill': {
        'Nob Hill': 5,
        'Embarcadero': 8,
        'The Castro': 21,
        'Haight-Ashbury': 17,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 7,
        'Chinatown': 9,
        'Golden Gate Park': 21,
        'Marina District': 7
    }
}

# List of people with their details
people = [
    {
        'name': 'Mary',
        'location': 'Embarcadero',
        'start_time': '20:00',
        'end_time': '21:15',
        'duration': 75,
        'travel_time': 9
    },
    {
        'name': 'Kenneth',
        'location': 'The Castro',
        'start_time': '11:15',
        'end_time': '19:15',
        'duration': 30,
        'travel_time': 17
    },
    {
        'name': 'Joseph',
        'location': 'Haight-Ashbury',
        'start_time': '20:00',
        'end_time': '22:00',
        'duration': 120,
        'travel_time': 13
    },
    {
        'name': 'Sarah',
        'location': 'Union Square',
        'start_time': '11:45',
        'end_time': '14:30',
        'duration': 90,
        'travel_time': 10
    },
    {
        'name': 'Thomas',
        'location': 'North Beach',
        'start_time': '19:15',
        'end_time': '19:45',
        'duration': 15,
        'travel_time': 6
    },
    {
        'name': 'Daniel',
        'location': 'Pacific Heights',
        'start_time': '13:45',
        'end_time': '20:30',
        'duration': 15,
        'travel_time': 11
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'start_time': '8:00',
        'end_time': '18:45',
        'duration': 30,
        'travel_time': 5
    },
    {
        'name': 'Mark',
        'location': 'Golden Gate Park',
        'start_time': '17:30',
        'end_time': '21:30',
        'duration': 120,
        'travel_time': 17
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'start_time': '20:00',
        'end_time': '21:00',
        'duration': 60,
        'travel_time': 12
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start_time': '13:15',
        'end_time': '19:30',
        'duration': 120,
        'travel_time': 8
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
        travel_time = travel_times['Nob Hill'][location]
        
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