import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input data
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

people = {
    'Kevin': {
        'location': 'Alamo Square',
        'available_start': '8:15',
        'available_end': '21:30',
        'duration': 75
    },
    'Kimberly': {
        'location': 'Russian Hill',
        'available_start': '8:45',
        'available_end': '12:30',
        'duration': 30
    },
    'Joseph': {
        'location': 'Presidio',
        'available_start': '18:30',
        'available_end': '19:15',
        'duration': 45
    },
    'Thomas': {
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'duration': 45
    }
}

# Convert all times to minutes
for person in people.values():
    person['available_start_min'] = time_to_minutes(person['available_start'])
    person['available_end_min'] = time_to_minutes(person['available_end'])

def calculate_schedule(order):
    current_location = 'Sunset District'
    current_time = time_to_minutes('9:00')
    schedule = []
    met_people = set()
    
    for person_name in order:
        person = people[person_name]
        location = person['location']
        
        # Travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this person
        meeting_start = max(arrival_time, person['available_start_min'])
        meeting_end = meeting_start + person['duration']
        
        if meeting_end > person['available_end_min']:
            return None  # Can't meet this person
        
        # Add to schedule
        schedule.append({
            'person': person_name,
            'location': location,
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        
        met_people.add(person_name)
        current_time = meeting_end
        current_location = location
    
    return {
        'schedule': schedule,
        'met_count': len(met_people),
        'total_people': len(order)
    }

# Try all possible orders of meeting people
best_schedule = None
best_met = 0

for order in permutations(people.keys()):
    result = calculate_schedule(order)
    if result and result['met_count'] > best_met:
        best_met = result['met_count']
        best_schedule = result['schedule']

# If no schedule meets all, try subsets
if best_met < len(people):
    for size in range(len(people)-1, 0, -1):
        from itertools import combinations
        for subset in combinations(people.keys(), size):
            for order in permutations(subset):
                result = calculate_schedule(order)
                if result and result['met_count'] > best_met:
                    best_met = result['met_count']
                    best_schedule = result['schedule']
        if best_schedule:
            break

# Format the output
itinerary = []
if best_schedule:
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))