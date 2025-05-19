import json

# Define travel times from Presidio to each location
travel_times = {
    'Presidio': {
        'Marina District': 11,
        'The Castro': 21,
        'Fisherman's Wharf': 19,
        'Bayview': 31,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Alamo Square': 19,
        'Golden Gate Park': 12
    },
    'Marina District': {
        'Presidio': 10,
        'The Castro': 22,
        'Fisherman's Wharf': 10,
        'Bayview': 27,
        'Pacific Heights': 7,
        'Mission District': 20,
        'Alamo Square': 15,
        'Golden Gate Park': 18
    },
    'The Castro': {
        'Presidio': 20,
        'Marina District': 21,
        'Fisherman's Wharf': 24,
        'Bayview': 19,
        'Pacific Heights': 16,
        'Mission District': 7,
        'Alamo Square': 8,
        'Golden Gate Park': 11
    },
    'Fisherman's Wharf': {
        'Presidio': 17,
        'Marina District': 9,
        'The Castro': 27,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Alamo Square': 21,
        'Golden Gate Park': 25
    },
    'Bayview': {
        'Presidio': 32,
        'Marina District': 27,
        'The Castro': 19,
        'Fisherman's Wharf': 25,
        'Pacific Heights': 23,
        'Mission District': 13,
        'Alamo Square': 16,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6,
        'The Castro': 16,
        'Fisherman's Wharf': 13,
        'Bayview': 22,
        'Mission District': 15,
        'Alamo Square': 10,
        'Golden Gate Park': 15
    },
    'Mission District': {
        'Presidio': 25,
        'Marina District': 19,
        'The Castro': 7,
        'Fisherman's Wharf': 22,
        'Bayview': 14,
        'Pacific Heights': 16,
        'Alamo Square': 11,
        'Golden Gate Park': 17
    },
    'Alamo Square': {
        'Presidio': 17,
        'Marina District': 15,
        'The Castro': 8,
        'Fisherman's Wharf': 19,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Golden Gate Park': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Marina District': 16,
        'The Castro': 13,
        'Fisherman's Wharf': 24,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Mission District': 17,
        'Alamo Square': 9
    }
}

# List of people with their details
people = [
    {
        'name': 'Amanda',
        'location': 'Marina District',
        'start_time': '2:45',
        'end_time': '7:30',
        'duration': 105,
        'travel_time': 11
    },
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'start_time': '9:30',
        'end_time': '5:00',
        'duration': 30,
        'travel_time': 21
    },
    {
        'name': 'Jeffrey',
        'location': 'Fisherman's Wharf',
        'start_time': '12:45',
        'end_time': '6:45',
        'duration': 120,
        'travel_time': 19
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'start_time': '10:15',
        'end_time': '1:15',
        'duration': 30,
        'travel_time': 31
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'start_time': '5:00',
        'end_time': '9:30',
        'duration': 105,
        'travel_time': 11
    },
    {
        'name': 'Karen',
        'location': 'Mission District',
        'start_time': '5:30',
        'end_time': '8:30',
        'duration': 105,
        'travel_time': 26
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'start_time': '11:15',
        'end_time': '5:30',
        'duration': 120,
        'travel_time': 19
    },
    {
        'name': 'Joseph',
        'location': 'Golden Gate Park',
        'start_time': '8:30',
        'end_time': '9:15',
        'duration': 105,
        'travel_time': 12
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