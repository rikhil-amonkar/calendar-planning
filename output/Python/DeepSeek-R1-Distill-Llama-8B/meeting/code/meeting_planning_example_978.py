import json

# Define travel times from Embarcadero to each location
travel_times = {
    'Embarcadero': {
        'Fisherman's Wharf': 6,
        'Financial District': 5,
        'Russian Hill': 8,
        'Marina District': 12,
        'Richmond District': 21,
        'Pacific Heights': 10,
        'Haight-Ashbury': 21,
        'Presidio': 20,
        'Nob Hill': 10,
        'The Castro': 25
    },
    'Fisherman's Wharf': {
        'Embarcadero': 8,
        'Financial District': 11,
        'Russian Hill': 7,
        'Marina District': 9,
        'Richmond District': 18,
        'Pacific Heights': 12,
        'Haight-Ashbury': 22,
        'Presidio': 17,
        'Nob Hill': 11,
        'The Castro': 27
    },
    'Financial District': {
        'Embarcadero': 4,
        'Fisherman's Wharf': 10,
        'Russian Hill': 11,
        'Marina District': 15,
        'Richmond District': 22,
        'Pacific Heights': 13,
        'Haight-Ashbury': 19,
        'Presidio': 22,
        'Nob Hill': 8,
        'The Castro': 20
    },
    'Russian Hill': {
        'Embarcadero': 8,
        'Fisherman's Wharf': 7,
        'Financial District': 11,
        'Marina District': 8,
        'Richmond District': 14,
        'Pacific Heights': 7,
        'Haight-Ashbury': 17,
        'Presidio': 14,
        'Nob Hill': 5,
        'The Castro': 21
    },
    'Marina District': {
        'Embarcadero': 14,
        'Fisherman's Wharf': 10,
        'Financial District': 17,
        'Russian Hill': 8,
        'Richmond District': 11,
        'Pacific Heights': 7,
        'Haight-Ashbury': 16,
        'Presidio': 10,
        'Nob Hill': 12,
        'The Castro': 22
    },
    'Richmond District': {
        'Embarcadero': 19,
        'Fisherman's Wharf': 18,
        'Financial District': 22,
        'Russian Hill': 13,
        'Marina District': 11,
        'Pacific Heights': 10,
        'Haight-Ashbury': 10,
        'Presidio': 7,
        'Nob Hill': 17,
        'The Castro': 16
    },
    'Pacific Heights': {
        'Embarcadero': 10,
        'Fisherman's Wharf': 13,
        'Financial District': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'Richmond District': 12,
        'Haight-Ashbury': 11,
        'Presidio': 11,
        'Nob Hill': 8,
        'The Castro': 16
    },
    'Haight-Ashbury': {
        'Embarcadero': 21,
        'Fisherman's Wharf': 23,
        'Financial District': 21,
        'Russian Hill': 17,
        'Marina District': 17,
        'Richmond District': 10,
        'Pacific Heights': 11,
        'Presidio': 15,
        'Nob Hill': 15,
        'The Castro': 6
    },
    'Presidio': {
        'Embarcadero': 20,
        'Fisherman's Wharf': 19,
        'Financial District': 23,
        'Russian Hill': 14,
        'Marina District': 11,
        'Richmond District': 7,
        'Pacific Heights': 11,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'The Castro': 21
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Fisherman's Wharf': 10,
        'Financial District': 9,
        'Russian Hill': 5,
        'Marina District': 11,
        'Richmond District': 14,
        'Pacific Heights': 8,
        'Haight-Ashbury': 13,
        'Presidio': 17,
        'The Castro': 17
    },
    'The Castro': {
        'Embarcadero': 22,
        'Fisherman's Wharf': 24,
        'Financial District': 21,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Pacific Heights': 16,
        'Haight-Ashbury': 6,
        'Presidio': 20,
        'Nob Hill': 16
    }
}

# List of people with their details
people = [
    {
        'name': 'Stephanie',
        'location': 'Fisherman's Wharf',
        'start_time': '3:30',
        'end_time': '10:00',
        'duration': 30,
        'travel_time': 6
    },
    {
        'name': 'Lisa',
        'location': 'Financial District',
        'start_time': '10:45',
        'end_time': '5:15',
        'duration': 15,
        'travel_time': 5
    },
    {
        'name': 'Melissa',
        'location': 'Russian Hill',
        'start_time': '5:00',
        'end_time': '9:45',
        'duration': 120,
        'travel_time': 8
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'start_time': '10:45',
        'end_time': '14:15',
        'duration': 60,
        'travel_time': 12
    },
    {
        'name': 'Sarah',
        'location': 'Richmond District',
        'start_time': '16:15',
        'end_time': '19:30',
        'duration': 105,
        'travel_time': 21
    },
    {
        'name': 'Daniel',
        'location': 'Pacific Heights',
        'start_time': '18:30',
        'end_time': '21:45',
        'duration': 60,
        'travel_time': 10
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'start_time': '9:00',
        'end_time': '13:30',
        'duration': 15,
        'travel_time': 21
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'start_time': '7:00',
        'end_time': '13:00',
        'duration': 45,
        'travel_time': 20
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'start_time': '19:45',
        'end_time': '22:00',
        'duration': 105,
        'travel_time': 10
    },
    {
        'name': 'John',
        'location': 'The Castro',
        'start_time': '13:15',
        'end_time': '19:45',
        'duration': 45,
        'travel_time': 25
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
        travel_time = travel_times['Embarcadero'][location]
        
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