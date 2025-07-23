import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Bayview': 21,
        'Presidio': 20,
        'Financial District': 5
    },
    'Golden Gate Park': {
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Bayview': 23,
        'Presidio': 11,
        'Financial District': 26
    },
    'Haight-Ashbury': {
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Bayview': 18,
        'Presidio': 15,
        'Financial District': 21
    },
    'Bayview': {
        'Embarcadero': 19,
        'Golden Gate Park': 22,
        'Haight-Ashbury': 19,
        'Presidio': 31,
        'Financial District': 19
    },
    'Presidio': {
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Haight-Ashbury': 15,
        'Bayview': 31,
        'Financial District': 23
    },
    'Financial District': {
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Bayview': 19,
        'Presidio': 22
    }
}

people = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'available_start': '8:45',
        'available_end': '11:45',
        'duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '16:15',
        'duration': 90
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': '15:00',
        'available_end': '19:15',
        'duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'available_start': '10:00',
        'available_end': '17:15',
        'duration': 120
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'available_start': '11:30',
        'available_end': '21:45',
        'duration': 105
    }
]

current_location = 'Embarcadero'
current_time = time_to_minutes('9:00')

# Generate all possible orders to meet people
all_permutations = permutations(people)

best_schedule = None
best_meetings = 0

for perm in all_permutations:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for person in perm:
        location = person['location']
        travel_time = travel_times[temp_location][location]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(person['available_start'])
        available_end = time_to_minutes(person['available_end'])
        duration = person['duration']
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        
        if meeting_end <= available_end:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': person['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            temp_location = location
            temp_time = meeting_end
    
    if meetings > best_meetings or (meetings == best_meetings and best_schedule is None):
        best_meetings = meetings
        best_schedule = schedule

# Prepare output
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))