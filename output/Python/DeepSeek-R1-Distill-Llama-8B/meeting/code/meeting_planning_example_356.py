import json

# Define travel times from Bayview to each location
travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 24
    },
    'Haight-Ashbury': {
        'Bayview': 19,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18
    }
}

# List of people with their details
people = [
    {
        'name': 'Barbara',
        'location': 'North Beach',
        'start_time': '13:45',
        'end_time': '20:15',
        'duration': 60,
        'travel_time': 21
    },
    {
        'name': 'Margaret',
        'location': 'Presidio',
        'start_time': '10:15',
        'end_time': '15:15',
        'duration': 30,
        'travel_time': 31
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'start_time': '20:00',
        'end_time': '20:45',
        'duration': 30,
        'travel_time': 19
    },
    {
        'name': 'Kimberly',
        'location': 'Union Square',
        'start_time': '7:45',
        'end_time': '16:45',
        'duration': 30,
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
        travel_time = travel_times['Bayview'][location]
        
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