import json

# Define travel times from Pacific Heights to each location
travel_times = {
    'Pacific Heights': {
        'Nob Hill': 8,
        'Russian Hill': 7,
        'The Castro': 16,
        'Sunset District': 21,
        'Haight-Ashbury': 11
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Russian Hill': 5,
        'The Castro': 17,
        'Sunset District': 25,
        'Haight-Ashbury': 13
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Nob Hill': 5,
        'The Castro': 18,
        'Sunset District': 23,
        'Haight-Ashbury': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Russian Hill': 18,
        'Sunset District': 17,
        'Haight-Ashbury': 6
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Nob Hill': 27,
        'Russian Hill': 24,
        'The Castro': 17,
        'Haight-Ashbury': 15
    },
    'Haight-Ashbury': {
        'Pacific Heights': 11,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'The Castro': 6,
        'Sunset District': 15
    }
}

# List of people with their details
people = [
    {
        'name': 'Ronald',
        'location': 'Nob Hill',
        'start_time': '10:00',
        'end_time': '5:00',
        'duration': 105,
        'travel_time': 8
    },
    {
        'name': 'Sarah',
        'location': 'Russian Hill',
        'start_time': '7:15',
        'end_time': '9:30',
        'duration': 45,
        'travel_time': 7
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'start_time': '1:30',
        'end_time': '5:00',
        'duration': 120,
        'travel_time': 16
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'start_time': '2:15',
        'end_time': '7:30',
        'duration': 90,
        'travel_time': 21
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'start_time': '10:15',
        'end_time': '10:00',
        'duration': 60,
        'travel_time': 11
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
        travel_time = travel_times['Pacific Heights'][location]
        
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