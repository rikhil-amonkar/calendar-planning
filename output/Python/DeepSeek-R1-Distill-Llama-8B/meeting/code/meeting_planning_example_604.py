import json

# Define travel times from Fisherman's Wharf to each location
travel_times = {
    'Fisherman's Wharf': {
        'The Castro': 26,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Alamo Square': 20,
        'North Beach': 6
    },
    'The Castro': {
        'Fisherman's Wharf': 24,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Russian Hill': 18,
        'Nob Hill': 16,
        'Alamo Square': 8,
        'North Beach': 20
    },
    'Golden Gate Park': {
        'Fisherman's Wharf': 25,
        'The Castro': 13,
        'Embarcadero': 25,
        'Russian Hill': 19,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'North Beach': 24
    },
    'Embarcadero': {
        'Fisherman's Wharf': 6,
        'The Castro': 25,
        'Golden Gate Park': 25,
        'Russian Hill': 8,
        'Nob Hill': 10,
        'Alamo Square': 19,
        'North Beach': 5
    },
    'Russian Hill': {
        'Fisherman's Wharf': 7,
        'The Castro': 21,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Nob Hill': 5,
        'Alamo Square': 15,
        'North Beach': 5
    },
    'Nob Hill': {
        'Fisherman's Wharf': 11,
        'The Castro': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Russian Hill': 5,
        'Alamo Square': 11,
        'North Beach': 8
    },
    'Alamo Square': {
        'Fisherman's Wharf': 19,
        'The Castro': 8,
        'Golden Gate Park': 9,
        'Embarcadero': 17,
        'Russian Hill': 13,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'North Beach': {
        'Fisherman's Wharf': 5,
        'The Castro': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Russian Hill': 4,
        'Nob Hill': 7,
        'Alamo Square': 16
    }
}

# List of people with their details
people = [
    {
        'name': 'Laura',
        'location': 'The Castro',
        'start_time': '7:45',
        'end_time': '9:30',
        'duration': 105,
        'travel_time': 26
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'start_time': '9:15',
        'end_time': '9:45',
        'duration': 15,
        'travel_time': 25
    },
    {
        'name': 'William',
        'location': 'Embarcadero',
        'start_time': '7:00',
        'end_time': '9:00',
        'duration': 90,
        'travel_time': 8
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start_time': '2:30',
        'end_time': '7:45',
        'duration': 30,
        'travel_time': 7
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'start_time': '7:30',
        'end_time': '9:30',
        'duration': 45,
        'travel_time': 11
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
        travel_time = travel_times['Fisherman's Wharf'][location]
        
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