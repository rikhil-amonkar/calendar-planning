import json

# Define travel times from Fisherman's Wharf to each location
travel_times = {
    'Fisherman's Wharf': {
        'Golden Gate Park': 25,
        'Presidio': 17,
        'Richmond District': 18,
        'Golden Gate Park': 24,
        'Presidio': 19,
        'Richmond District': 18
    },
    'Golden Gate Park': {
        'Fisherman's Wharf': 24,
        'Presidio': 11,
        'Richmond District': 7,
        'Fisherman's Wharf': 25,
        'Presidio': 12,
        'Richmond District': 9
    },
    'Presidio': {
        'Fisherman's Wharf': 17,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Fisherman's Wharf': 19,
        'Golden Gate Park': 11,
        'Richmond District': 7
    },
    'Richmond District': {
        'Fisherman's Wharf': 18,
        'Golden Gate Park': 9,
        'Presidio': 7,
        'Fisherman's Wharf': 18,
        'Golden Gate Park': 7,
        'Presidio': 7
    }
}

# List of people with their details
people = [
    {
        'name': 'Melissa',
        'location': 'Golden Gate Park',
        'start_time': '8:30',
        'end_time': '8:00',
        'duration': 15,
        'travel_time': 25
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'start_time': '7:45',
        'end_time': '10:00',
        'duration': 105,
        'travel_time': 17
    },
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'start_time': '4:45',
        'end_time': '10:00',
        'duration': 120,
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
        travel_time = travel_times['Fisherman's Wharf'][location]
        
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