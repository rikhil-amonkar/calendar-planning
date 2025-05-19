import json

# Define travel times from Alamo Square to each location
travel_times = {
    'Alamo Square': {
        'Russian Hill': 13,
        'Presidio': 18,
        'Chinatown': 16,
        'Sunset District': 16,
        'The Castro': 8,
        'Embarcadero': 17,
        'Golden Gate Park': 9
    },
    'Russian Hill': {
        'Alamo Square': 15,
        'Presidio': 14,
        'Chinatown': 9,
        'Sunset District': 24,
        'The Castro': 21,
        'Embarcadero': 8,
        'Golden Gate Park': 21
    },
    'Presidio': {
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Sunset District': 15,
        'The Castro': 21,
        'Embarcadero': 20,
        'Golden Gate Park': 12
    },
    'Chinatown': {
        'Alamo Square': 17,
        'Russian Hill': 7,
        'Presidio': 19,
        'Sunset District': 30,
        'The Castro': 22,
        'Embarcadero': 5,
        'Golden Gate Park': 23
    },
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Chinatown': 30,
        'The Castro': 17,
        'Embarcadero': 31,
        'Golden Gate Park': 11
    },
    'The Castro': {
        'Alamo Square': 8,
        'Russian Hill': 18,
        'Presidio': 20,
        'Chinatown': 20,
        'Sunset District': 17,
        'Embarcadero': 22,
        'Golden Gate Park': 11
    },
    'Embarcadero': {
        'Alamo Square': 19,
        'Russian Hill': 8,
        'Presidio': 20,
        'Chinatown': 7,
        'Sunset District': 31,
        'The Castro': 25,
        'Golden Gate Park': 25
    },
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Sunset District': 10,
        'The Castro': 13,
        'Embarcadero': 25
    }
}

# List of people with their details
people = [
    {
        'name': 'Emily',
        'location': 'Russian Hill',
        'start_time': '12:15',
        'end_time': '14:15',
        'duration': 105,
        'travel_time': 13
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'start_time': '14:45',
        'end_time': '20:30',
        'duration': 60,
        'travel_time': 18
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'start_time': '7:30',
        'end_time': '16:30',
        'duration': 45,
        'travel_time': 16
    },
    {
        'name': 'Margaret',
        'location': 'Sunset District',
        'start_time': '21:30',
        'end_time': '22:30',
        'duration': 60,
        'travel_time': 16
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'start_time': '7:30',
        'end_time': '12:45',
        'duration': 60,
        'travel_time': 8
    },
    {
        'name': 'Andrew',
        'location': 'Embarcadero',
        'start_time': '20:15',
        'end_time': '22:00',
        'duration': 75,
        'travel_time': 17
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'start_time': '10:00',
        'end_time': '16:00',
        'duration': 105,
        'travel_time': 9
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
        travel_time = travel_times['Alamo Square'][location]
        
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