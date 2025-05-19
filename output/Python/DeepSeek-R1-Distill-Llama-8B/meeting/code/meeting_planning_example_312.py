import json

# Define travel times from Richmond District to each location
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17
    }
}

# List of people with their details
people = [
    {
        'name': 'Sarah',
        'location': 'Sunset District',
        'start_time': '10:45',
        'end_time': '7:00',
        'duration': 30,
        'travel_time': 11
    },
    {
        'name': 'Richard',
        'location': 'Haight-Ashbury',
        'start_time': '11:45',
        'end_time': '3:45',
        'duration': 90,
        'travel_time': 10
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'start_time': '11:00',
        'end_time': '5:15',
        'duration': 120,
        'travel_time': 20
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'start_time': '6:15',
        'end_time': '8:45',
        'duration': 90,
        'travel_time': 9
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
        travel_time = travel_times['Richmond District'][location]
        
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