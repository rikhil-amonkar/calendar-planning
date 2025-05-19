import json

# Define travel times from Financial District to each location
travel_times = {
    'Financial District': {
        'Fisherman's Wharf': 10,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Fisherman's Wharf': 11,
        'Pacific Heights': 13,
        'Mission District': 17
    },
    'Fisherman's Wharf': {
        'Financial District': 11,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Fisherman's Wharf': 0,
        'Pacific Heights': 13
    },
    'Pacific Heights': {
        'Financial District': 13,
        'Fisherman's Wharf': 13,
        'Mission District': 15,
        'Pacific Heights': 0,
        'Mission District': 15
    },
    'Mission District': {
        'Financial District': 17,
        'Fisherman's Wharf': 22,
        'Pacific Heights': 16,
        'Mission District': 0,
        'Pacific Heights': 16
    }
}

# List of people with their details
people = [
    {
        'name': 'David',
        'location': 'Fisherman's Wharf',
        'start_time': '10:45',
        'end_time': '3:30',
        'duration': 15,
        'travel_time': 11
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start_time': '9:00',
        'end_time': '3:30',
        'duration': 75,
        'travel_time': 13
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'start_time': '12:15',
        'end_time': '7:45',
        'duration': 90,
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
        travel_time = travel_times['Financial District'][location]
        
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