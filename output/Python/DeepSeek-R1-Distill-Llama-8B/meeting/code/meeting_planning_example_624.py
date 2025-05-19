import json

# Define travel times from Golden Gate Park to each location
travel_times = {
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Fisherman's Wharf': 24,
        'The Castro': 13,
        'Chinatown': 23,
        'Alamo Square': 10,
        'North Beach': 24,
        'Russian Hill': 19
    },
    'Haight-Ashbury': {
        'Golden Gate Park': 7,
        'Fisherman's Wharf': 23,
        'The Castro': 6,
        'Chinatown': 19,
        'Alamo Square': 5,
        'North Beach': 19,
        'Russian Hill': 17
    },
    'Fisherman's Wharf': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 22,
        'The Castro': 26,
        'Chinatown': 12,
        'Alamo Square': 20,
        'North Beach': 6,
        'Russian Hill': 7
    },
    'The Castro': {
        'Golden Gate Park': 11,
        'Haight-Ashbury': 6,
        'Fisherman's Wharf': 24,
        'Chinatown': 20,
        'Alamo Square': 8,
        'North Beach': 20,
        'Russian Hill': 18
    },
    'Chinatown': {
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Fisherman's Wharf': 8,
        'The Castro': 22,
        'Alamo Square': 17,
        'North Beach': 3,
        'Russian Hill': 7
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Haight-Ashbury': 5,
        'Fisherman's Wharf': 19,
        'Chinatown': 16,
        'North Beach': 15,
        'Russian Hill': 13
    },
    'North Beach': {
        'Golden Gate Park': 22,
        'Haight-Ashbury': 18,
        'Fisherman's Wharf': 5,
        'The Castro': 22,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Russian Hill': 4
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Haight-Ashbury': 17,
        'Fisherman's Wharf': 7,
        'The Castro': 21,
        'Chinatown': 9,
        'Alamo Square': 15,
        'North Beach': 5
    }
}

# List of people with their details
people = [
    {
        'name': 'Carol',
        'location': 'Haight-Ashbury',
        'start_time': '9:30',
        'end_time': '10:30',
        'duration': 60,
        'travel_time': 7
    },
    {
        'name': 'Laura',
        'location': 'Fisherman's Wharf',
        'start_time': '11:45',
        'end_time': '9:30',
        'duration': 60,
        'travel_time': 24
    },
    {
        'name': 'Karen',
        'location': 'The Castro',
        'start_time': '7:15',
        'end_time': '14:00',
        'duration': 75,
        'travel_time': 13
    },
    {
        'name': 'Elizabeth',
        'location': 'Chinatown',
        'start_time': '12:15',
        'end_time': '21:30',
        'duration': 75,
        'travel_time': 23
    },
    {
        'name': 'Deborah',
        'location': 'Alamo Square',
        'start_time': '12:00',
        'end_time': '15:00',
        'duration': 105,
        'travel_time': 10
    },
    {
        'name': 'Jason',
        'location': 'North Beach',
        'start_time': '14:45',
        'end_time': '19:00',
        'duration': 90,
        'travel_time': 24
    },
    {
        'name': 'Steven',
        'location': 'Russian Hill',
        'start_time': '14:45',
        'end_time': '20:30',
        'duration': 120,
        'travel_time': 19
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
        travel_time = travel_times['Golden Gate Park'][location]
        
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