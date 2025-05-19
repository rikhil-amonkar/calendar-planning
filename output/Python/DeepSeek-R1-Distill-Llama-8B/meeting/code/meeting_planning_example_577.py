import json

# Define travel times from Haight-Ashbury to each location
travel_times = {
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Fisherman's Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Alamo Square': 5,
        'Pacific Heights': 12
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Fisherman's Wharf': 7,
        'Nob Hill': 5,
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Pacific Heights': 7
    },
    'Fisherman's Wharf': {
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Alamo Square': 20,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'Fisherman's Wharf': 11,
        'Golden Gate Park': 17,
        'Alamo Square': 11,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Russian Hill': 19,
        'Fisherman's Wharf': 24,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'Pacific Heights': 16
    },
    'Alamo Square': {
        'Haight-Ashbury': 5,
        'Russian Hill': 13,
        'Fisherman's Wharf': 19,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Russian Hill': 7,
        'Fisherman's Wharf': 13,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Alamo Square': 10
    }
}

# List of people with their details
people = [
    {
        'name': 'Stephanie',
        'location': 'Russian Hill',
        'start_time': '8:00',
        'end_time': '8:45',
        'duration': 15,
        'travel_time': 17
    },
    {
        'name': 'Kevin',
        'location': 'Fisherman's Wharf',
        'start_time': '7:15',
        'end_time': '9:45',
        'duration': 75,
        'travel_time': 23
    },
    {
        'name': 'Robert',
        'location': 'Nob Hill',
        'start_time': '7:45',
        'end_time': '10:30',
        'duration': 90,
        'travel_time': 15
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'start_time': '8:30',
        'end_time': '5:00',
        'duration': 75,
        'travel_time': 7
    },
    {
        'name': 'Anthony',
        'location': 'Alamo Square',
        'start_time': '7:45',
        'end_time': '7:45',
        'duration': 15,
        'travel_time': 5
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'start_time': '2:45',
        'end_time': '9:45',
        'duration': 45,
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
        travel_time = travel_times['Haight-Ashbury'][location]
        
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