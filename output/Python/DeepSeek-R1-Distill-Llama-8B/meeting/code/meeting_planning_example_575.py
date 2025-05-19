import json

# Define travel times from The Castro to each location
travel_times = {
    'The Castro': {
        'Presidio': 20,
        'Sunset District': 17,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Golden Gate Park': 11,
        'Russian Hill': 18
    },
    'Presidio': {
        'The Castro': 21,
        'Sunset District': 15,
        'Haight-Ashbury': 15,
        'Mission District': 26,
        'Golden Gate Park': 12,
        'Russian Hill': 14
    },
    'Sunset District': {
        'The Castro': 17,
        'Presidio': 16,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11,
        'Russian Hill': 24
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Presidio': 15,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7,
        'Russian Hill': 17
    },
    'Mission District': {
        'The Castro': 7,
        'Presidio': 25,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17,
        'Russian Hill': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Presidio': 11,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Russian Hill': 19
    },
    'Russian Hill': {
        'The Castro': 21,
        'Presidio': 14,
        'Sunset District': 23,
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Golden Gate Park': 21
    }
}

# List of people with their details
people = [
    {
        'name': 'Rebecca',
        'location': 'Presidio',
        'start_time': '18:15',
        'end_time': '20:45',
        'duration': 60,
        'travel_time': 20
    },
    {
        'name': 'Linda',
        'location': 'Sunset District',
        'start_time': '15:30',
        'end_time': '19:45',
        'duration': 30,
        'travel_time': 17
    },
    {
        'name': 'Elizabeth',
        'location': 'Haight-Ashbury',
        'start_time': '17:15',
        'end_time': '19:30',
        'duration': 105,
        'travel_time': 6
    },
    {
        'name': 'William',
        'location': 'Mission District',
        'start_time': '13:15',
        'end_time': '19:30',
        'duration': 30,
        'travel_time': 7
    },
    {
        'name': 'Robert',
        'location': 'Golden Gate Park',
        'start_time': '14:15',
        'end_time': '21:30',
        'duration': 45,
        'travel_time': 11
    },
    {
        'name': 'Mark',
        'location': 'Russian Hill',
        'start_time': '10:00',
        'end_time': '21:15',
        'duration': 75,
        'travel_time': 18
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
        travel_time = travel_times['The Castro'][location]
        
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