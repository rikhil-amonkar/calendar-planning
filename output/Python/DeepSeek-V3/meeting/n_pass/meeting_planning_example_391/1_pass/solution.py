import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Financial District': 30
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Presidio': 18,
        'Financial District': 17
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Presidio': 14,
        'Financial District': 11
    },
    'Presidio': {
        'Sunset District': 15,
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Financial District': 23
    },
    'Financial District': {
        'Sunset District': 31,
        'Alamo Square': 17,
        'Russian Hill': 10,
        'Presidio': 22
    }
}

people = [
    {
        'name': 'Kevin',
        'location': 'Alamo Square',
        'available_start': '8:15',
        'available_end': '21:30',
        'duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Russian Hill',
        'available_start': '8:45',
        'available_end': '12:30',
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'available_start': '18:30',
        'available_end': '19:15',
        'duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'duration': 45
    }
]

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for person_idx in order:
        person = people[person_idx]
        dest = person['location']
        travel_time = travel_times[loc][dest]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(person['available_start'])
        available_end = time_to_minutes(person['available_end'])
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + person['duration']
        
        if meeting_end > available_end:
            return None  # Not enough time to meet
        
        schedule.append({
            'person': person['name'],
            'location': dest,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        time = meeting_end
        loc = dest
    
    return schedule

# Try all possible orders of meetings
best_schedule = None
best_meetings = 0

for order in permutations(range(len(people))):
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > best_meetings:
        best_schedule = schedule
        best_meetings = len(schedule)
    elif schedule and len(schedule) == best_meetings and schedule:
        # Prefer schedules that end earlier
        if not best_schedule or time_to_minutes(schedule[-1]['end_time']) < time_to_minutes(best_schedule[-1]['end_time']):
            best_schedule = schedule

# Prepare output
if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": meeting['start_time'],
            "end_time": meeting['end_time']
        })
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))