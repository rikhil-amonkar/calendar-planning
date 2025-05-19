import json

# Define travel times from Nob Hill to each location
travel_times = {
    'Nob Hill': {
        'Richmond District': 14,
        'Financial District': 9,
        'North Beach': 8,
        'The Castro': 17,
        'Golden Gate Park': 17
    },
    'Richmond District': {
        'Nob Hill': 17,
        'Financial District': 22,
        'North Beach': 17,
        'The Castro': 16,
        'Golden Gate Park': 9
    },
    'Financial District': {
        'Nob Hill': 8,
        'Richmond District': 21,
        'North Beach': 7,
        'The Castro': 23,
        'Golden Gate Park': 23
    },
    'North Beach': {
        'Nob Hill': 7,
        'Richmond District': 18,
        'Financial District': 8,
        'The Castro': 22,
        'Golden Gate Park': 22
    },
    'The Castro': {
        'Nob Hill': 16,
        'Richmond District': 16,
        'Financial District': 20,
        'North Beach': 20,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Richmond District': 7,
        'Financial District': 26,
        'North Beach': 24,
        'The Castro': 13
    }
}

# List of people with their details
people = [
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'start_time': '7:00',
        'end_time': '9:00',
        'duration': 15,
        'travel_time': 14
    },
    {
        'name': 'Margaret',
        'location': 'Financial District',
        'start_time': '4:30',
        'end_time': '8:15',
        'duration': 75,
        'travel_time': 9
    },
    {
        'name': 'Ronald',
        'location': 'North Beach',
        'start_time': '6:30',
        'end_time': '7:30',
        'duration': 45,
        'travel_time': 8
    },
    {
        'name': 'Deborah',
        'location': 'The Castro',
        'start_time': '1:45',
        'end_time': '9:15',
        'duration': 90,
        'travel_time': 17
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'start_time': '11:15',
        'end_time': '2:30',
        'duration': 120,
        'travel_time': 17
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