import json

# Define travel times from Presidio to each location
travel_times = {
    'Presidio': {
        'Richmond District': 7,
        'North Beach': 18,
        'Financial District': 23,
        'Golden Gate Park': 12,
        'Union Square': 22
    },
    'Richmond District': {
        'Presidio': 7,
        'North Beach': 17,
        'Financial District': 22,
        'Golden Gate Park': 9,
        'Union Square': 21
    },
    'North Beach': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 7,
        'Golden Gate Park': 22,
        'Union Square': 7
    },
    'Financial District': {
        'Presidio': 22,
        'Richmond District': 21,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Union Square': 9
    },
    'Golden Gate Park': {
        'Presidio': 12,
        'Richmond District': 7,
        'North Beach': 24,
        'Financial District': 26,
        'Union Square': 22
    },
    'Union Square': {
        'Presidio': 24,
        'Richmond District': 20,
        'North Beach': 10,
        'Financial District': 9,
        'Golden Gate Park': 22
    }
}

# List of people with their details
people = [
    {
        'name': 'Jason',
        'location': 'Richmond District',
        'start_time': '1:00',
        'end_time': '8:45',
        'duration': 90,
        'travel_time': 7
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start_time': '6:45',
        'end_time': '8:15',
        'duration': 45,
        'travel_time': 18
    },
    {
        'name': 'Brian',
        'location': 'Financial District',
        'start_time': '9:45',
        'end_time': '9:45',
        'duration': 15,
        'travel_time': 23
    },
    {
        'name': 'Elizabeth',
        'location': 'Golden Gate Park',
        'start_time': '8:45',
        'end_time': '9:30',
        'duration': 105,
        'travel_time': 12
    },
    {
        'name': 'Laura',
        'location': 'Union Square',
        'start_time': '2:15',
        'end_time': '7:30',
        'duration': 75,
        'travel_time': 24
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
        travel_time = travel_times['Presidio'][location]
        
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
        ])
    
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