import json

# Define travel times from Union Square to each location
travel_times = {
    'Union Square': {
        'Mission District': 14,
        'Bayview': 15,
        'Sunset District': 26,
        'Mission District': 15,
        'Bayview': 15,
        'Sunset District': 30
    },
    'Mission District': {
        'Union Square': 15,
        'Bayview': 15,
        'Sunset District': 24,
        'Union Square': 14,
        'Bayview': 13,
        'Sunset District': 24
    },
    'Bayview': {
        'Union Square': 17,
        'Mission District': 13,
        'Sunset District': 23,
        'Union Square': 15,
        'Mission District': 15,
        'Sunset District': 22
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 24,
        'Bayview': 22,
        'Union Square': 26,
        'Mission District': 24,
        'Bayview': 23
    }
}

# List of people with their details
people = [
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'start_time': '11:30',
        'end_time': '20:15',
        'duration': 120,
        'travel_time': 14
    },
    {
        'name': 'Karen',
        'location': 'Bayview',
        'start_time': '12:45',
        'end_time': '15:00',
        'duration': 120,
        'travel_time': 15
    },
    {
        'name': 'Carol',
        'location': 'Sunset District',
        'start_time': '10:15',
        'end_time': '11:45',
        'duration': 30,
        'travel_time': 26
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
        travel_time = travel_times['Union Square'][location]
        
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