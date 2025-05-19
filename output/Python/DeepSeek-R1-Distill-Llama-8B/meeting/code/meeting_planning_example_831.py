import json

# Define travel times from Presidio to each location
travel_times = {
    'Presidio': {
        'Fisherman's Wharf': 19,
        'Alamo Square': 19,
        'Financial District': 23,
        'Union Square': 22,
        'Sunset District': 15,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Fisherman's Wharf': {
        'Presidio': 17,
        'Alamo Square': 21,
        'Financial District': 11,
        'Union Square': 13,
        'Sunset District': 27,
        'Embarcadero': 8,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Richmond District': 18
    },
    'Alamo Square': {
        'Presidio': 17,
        'Fisherman's Wharf': 19,
        'Financial District': 17,
        'Union Square': 14,
        'Sunset District': 16,
        'Embarcadero': 16,
        'Golden Gate Park': 9,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Financial District': {
        'Presidio': 22,
        'Fisherman's Wharf': 10,
        'Alamo Square': 17,
        'Union Square': 9,
        'Sunset District': 30,
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Richmond District': 21
    },
    'Union Square': {
        'Presidio': 24,
        'Fisherman's Wharf': 15,
        'Alamo Square': 15,
        'Financial District': 9,
        'Sunset District': 27,
        'Embarcadero': 11,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Richmond District': 20
    },
    'Sunset District': {
        'Presidio': 16,
        'Fisherman's Wharf': 29,
        'Alamo Square': 17,
        'Financial District': 30,
        'Union Square': 30,
        'Embarcadero': 30,
        'Golden Gate Park': 11,
        'Chinatown': 30,
        'Richmond District': 12
    },
    'Embarcadero': {
        'Presidio': 20,
        'Fisherman's Wharf': 6,
        'Alamo Square': 19,
        'Financial District': 5,
        'Union Square': 10,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Chinatown': 7,
        'Richmond District': 21
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Fisherman's Wharf': 24,
        'Alamo Square': 9,
        'Financial District': 26,
        'Union Square': 22,
        'Sunset District': 10,
        'Embarcadero': 25,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Presidio': 19,
        'Fisherman's Wharf': 8,
        'Alamo Square': 17,
        'Financial District': 5,
        'Union Square': 7,
        'Sunset District': 29,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Presidio': 7,
        'Fisherman's Wharf': 18,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Sunset District': 11,
        'Embarcadero': 19,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

# List of people with their details
people = [
    {
        'name': 'Jeffrey',
        'location': 'Fisherman's Wharf',
        'start_time': '10:15',
        'end_time': '1:00',
        'duration': 90,
        'travel_time': 19
    },
    {
        'name': 'Ronald',
        'location': 'Alamo Square',
        'start_time': '7:45',
        'end_time': '2:45',
        'duration': 120,
        'travel_time': 19
    },
    {
        'name': 'Jason',
        'location': 'Financial District',
        'start_time': '10:45',
        'end_time': '4:00',
        'duration': 105,
        'travel_time': 23
    },
    {
        'name': 'Melissa',
        'location': 'Union Square',
        'start_time': '5:45',
        'end_time': '6:15',
        'duration': 15,
        'travel_time': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'start_time': '2:45',
        'end_time': '5:30',
        'duration': 105,
        'travel_time': 15
    },
    {
        'name': 'Margaret',
        'location': 'Embarcadero',
        'start_time': '1:15',
        'end_time': '7:00',
        'duration': 90,
        'travel_time': 20
    },
    {
        'name': 'George',
        'location': 'Golden Gate Park',
        'start_time': '7:00',
        'end_time': '10:00',
        'duration': 75,
        'travel_time': 12
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'start_time': '9:30',
        'end_time': '9:00',
        'duration': 15,
        'travel_time': 21
    },
    {
        'name': 'Laura',
        'location': 'Richmond District',
        'start_time': '9:45',
        'end_time': '6:00',
        'duration': 60,
        'travel_time': 7
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