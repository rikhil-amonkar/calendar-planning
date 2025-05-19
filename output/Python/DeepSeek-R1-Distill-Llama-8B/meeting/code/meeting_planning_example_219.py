import json

# Define travel times from The Castro to each location
travel_times = {
    'The Castro': {
        'Alamo Square': 8,
        'Union Square': 19,
        'Chinatown': 20
    },
    'Alamo Square': {
        'The Castro': 8,
        'Union Square': 14,
        'Chinatown': 16
    },
    'Union Square': {
        'The Castro': 19,
        'Alamo Square': 15,
        'Chinatown': 7
    },
    'Chinatown': {
        'The Castro': 20,
        'Alamo Square': 17,
        'Union Square': 7
    }
}

# List of people with their details
people = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'start_time': '11:45',
        'end_time': '3:15',
        'duration': 105,
        'travel_time': 8
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'start_time': '4:45',
        'end_time': '6:15',
        'duration': 60,
        'travel_time': 19
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'start_time': '5:15',
        'end_time': '7:00',
        'duration': 105,
        'travel_time': 20
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
        travel_time = travel_times['The Castro'][location]
        
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