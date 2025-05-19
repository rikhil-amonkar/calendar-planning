import json

# Define travel times from Marina District to each location
travel_times = {
    'Marina District': {
        'Mission District': 20,
        'Fisherman's Wharf': 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8
    },
    'Mission District': {
        'Marina District': 19,
        'Fisherman's Wharf': 22,
        'Presidio': 25,
        'Union Square': 15,
        'Sunset District': 24,
        'Financial District': 15,
        'Haight-Ashbury': 12,
        'Russian Hill': 15
    },
    'Fisherman's Wharf': {
        'Marina District': 9,
        'Mission District': 22,
        'Presidio': 17,
        'Union Square': 13,
        'Sunset District': 27,
        'Financial District': 11,
        'Haight-Ashbury': 22,
        'Russian Hill': 7
    },
    'Presidio': {
        'Marina District': 11,
        'Mission District': 26,
        'Fisherman's Wharf': 19,
        'Union Square': 22,
        'Sunset District': 15,
        'Financial District': 23,
        'Haight-Ashbury': 15,
        'Russian Hill': 14
    },
    'Union Square': {
        'Marina District': 18,
        'Mission District': 14,
        'Fisherman's Wharf': 15,
        'Presidio': 24,
        'Sunset District': 27,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Russian Hill': 13
    },
    'Sunset District': {
        'Marina District': 21,
        'Mission District': 25,
        'Fisherman's Wharf': 29,
        'Presidio': 16,
        'Union Square': 30,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Russian Hill': 24
    },
    'Financial District': {
        'Marina District': 15,
        'Mission District': 17,
        'Fisherman's Wharf': 10,
        'Presidio': 22,
        'Union Square': 9,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Russian Hill': 11
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Mission District': 11,
        'Fisherman's Wharf': 23,
        'Presidio': 15,
        'Union Square': 19,
        'Sunset District': 15,
        'Financial District': 21,
        'Russian Hill': 17
    },
    'Russian Hill': {
        'Marina District': 7,
        'Mission District': 16,
        'Fisherman's Wharf': 7,
        'Presidio': 14,
        'Union Square': 10,
        'Sunset District': 23,
        'Financial District': 11,
        'Haight-Ashbury': 17
    }
}

# List of people with their details
people = [
    {
        'name': 'Karen',
        'location': 'Mission District',
        'start_time': '2:15',
        'end_time': '10:00',
        'duration': 30,
        'travel_time': 20
    },
    {
        'name': 'Richard',
        'location': 'Fisherman's Wharf',
        'start_time': '2:30',
        'end_time': '5:30',
        'duration': 30,
        'travel_time': 10
    },
    {
        'name': 'Robert',
        'location': 'Presidio',
        'start_time': '9:45',
        'end_time': '10:45',
        'duration': 60,
        'travel_time': 10
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'start_time': '11:45',
        'end_time': '2:45',
        'duration': 120,
        'travel_time': 16
    },
    {
        'name': 'Helen',
        'location': 'Sunset District',
        'start_time': '2:45',
        'end_time': '8:45',
        'duration': 105,
        'travel_time': 19
    },
    {
        'name': 'Elizabeth',
        'location': 'Financial District',
        'start_time': '10:00',
        'end_time': '12:45',
        'duration': 75,
        'travel_time': 17
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'start_time': '2:15',
        'end_time': '5:30',
        'duration': 105,
        'travel_time': 16
    },
    {
        'name': 'Ashley',
        'location': 'Russian Hill',
        'start_time': '11:30',
        'end_time': '9:30',
        'duration': 45,
        'travel_time': 8
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
        travel_time = travel_times['Marina District'][location]
        
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