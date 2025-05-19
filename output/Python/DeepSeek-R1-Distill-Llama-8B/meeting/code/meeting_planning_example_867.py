import json

# Define the travel times from Haight-Ashbury to each location
travel_times = {
    'Haight-Ashbury': {
        'Mission District': 17,
        'Union Square': 19,
        'Pacific Heights': 12,
        'Bayview': 18,
        'Fisherman's Wharf': 23,
        'Marina District': 17,
        'Richmond District': 10,
        'Sunset District': 15,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Union Square': 15,
        'Pacific Heights': 16,
        'Bayview': 14,
        'Fisherman's Wharf': 22,
        'Marina District': 19,
        'Richmond District': 20,
        'Sunset District': 24,
        'Golden Gate Park': 17
    },
    'Union Square': {
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Bayview': 15,
        'Fisherman's Wharf': 15,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Union Square': 12,
        'Bayview': 22,
        'Fisherman's Wharf': 13,
        'Marina District': 6,
        'Richmond District': 12,
        'Sunset District': 21,
        'Golden Gate Park': 15
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Union Square': 18,
        'Pacific Heights': 23,
        'Fisherman's Wharf': 25,
        'Marina District': 27,
        'Richmond District': 25,
        'Sunset District': 23,
        'Golden Gate Park': 22
    },
    'Fisherman's Wharf': {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Union Square': 13,
        'Pacific Heights': 12,
        'Bayview': 26,
        'Marina District': 9,
        'Richmond District': 18,
        'Sunset District': 27,
        'Golden Gate Park': 25
    },
    'Marina District': {
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Union Square': 16,
        'Pacific Heights': 7,
        'Bayview': 27,
        'Fisherman's Wharf': 10,
        'Richmond District': 9,
        'Sunset District': 19,
        'Golden Gate Park': 18
    },
    'Richmond District': {
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Union Square': 21,
        'Pacific Heights': 10,
        'Bayview': 27,
        'Fisherman's Wharf': 18,
        'Marina District': 9,
        'Sunset District': 11,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Haight-Ashbury': 15,
        'Mission District': 25,
        'Union Square': 30,
        'Pacific Heights': 21,
        'Bayview': 22,
        'Fisherman's Wharf': 29,
        'Marina District': 21,
        'Richmond District': 12,
        'Golden Gate Park': 11
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Union Square': 22,
        'Pacific Heights': 16,
        'Bayview': 23,
        'Fisherman's Wharf': 24,
        'Marina District': 16,
        'Richmond District': 7,
        'Sunset District': 10
    }
}

# List of people with their details
people = [
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'start_time': '7:00',
        'end_time': '8:00',
        'duration': 120,
        'travel_time': 12
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'start_time': '10:30',
        'end_time': '8:00',
        'duration': 90,
        'travel_time': 17
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'start_time': '3:15',
        'end_time': '7:00',
        'duration': 45,
        'travel_time': 19
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'start_time': '7:30',
        'end_time': '8:30',
        'duration': 30,
        'travel_time': 18
    },
    {
        'name': 'Robert',
        'location': 'Fisherman's Wharf',
        'start_time': '10:00',
        'end_time': '3:00',
        'duration': 15,
        'travel_time': 23
    },
    {
        'name': 'Kenneth',
        'location': 'Marina District',
        'start_time': '10:45',
        'end_time': '1:00',
        'duration': 45,
        'travel_time': 20
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start_time': '6:15',
        'end_time': '8:00',
        'duration': 15,
        'travel_time': 12
    },
    {
        'name': 'Kimberly',
        'location': 'Sunset District',
        'start_time': '10:15',
        'end_time': '6:15',
        'duration': 105,
        'travel_time': 15
    },
    {
        'name': 'Amanda',
        'location': 'Golden Gate Park',
        'start_time': '7:45',
        'end_time': '6:45',
        'duration': 15,
        'travel_time': 7
    }
]

# Function to calculate the possible meeting time for a person
def calculate_meeting_time(people, travel_times):
    meetings = []
    for person in people:
        location = person['location']
        start_time = person['start_time']
        end_time = person['end_time']
        duration = person['duration']
        travel_time = travel_times['Haight-Ashbury'][location]
        
        # Calculate the earliest and latest possible start time
        earliest_start = f"{start_time}:00"
        latest_start = f"{end_time}:00"
        
        if earliest_start < '9:00':
            earliest_start = '9:00'
        
        if latest_start < earliest_start:
            continue  # No possible meeting time
        
        # Convert times to minutes since 9:00 AM for easier calculation
        earliest_start_min = int(earliest_start.replace(':', '')) * 60
        latest_start_min = int(end_time.replace(':', '')) * 60 - duration
        
        if latest_start_min < earliest_start_min:
            continue
        
        meetings.append({
            'name': person['name'],
            'location': location,
            'start_time': earliest_start_min,
            'end_time': latest_start_min
        })
    
    return meetings

# Calculate feasible meeting times
feasible_meetings = calculate_meeting_time(people, travel_times)

# Sort feasible meetings by end time
feasible_meetings.sort(key=lambda x: x['end_time'])

# Select non-overlapping meetings
itinerary = []
for meeting in feasible_meetings:
    start = meeting['start_time']
    end = meeting['end_time']
    if not itinerary or end <= itinerary[-1]['end_time']:
        itinerary.append(meeting)

# Convert to 24-hour format strings
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

# Convert to required format
output = {
    "itinerary": itinerary
}

# Print the JSON output
print(json.dumps(output))