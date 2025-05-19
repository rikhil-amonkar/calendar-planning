import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes
travel_times = {
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26
    },
    'Fisherman\'s Wharf': {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Bayview': {
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19
    },
    'Mission District': {
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Fisherman\'s Wharf': 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4
    }
}

# People and their constraints
people = [
    {
        'name': 'Joseph',
        'location': 'Fisherman\'s Wharf',
        'available_start': '8:00',
        'available_end': '17:30',
        'min_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'available_start': '17:30',
        'available_end': '21:30',
        'min_duration': 60
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'available_start': '11:15',
        'available_end': '15:15',
        'min_duration': 30
    },
    {
        'name': 'David',
        'location': 'Embarcadero',
        'available_start': '8:15',
        'available_end': '9:00',
        'min_duration': 30
    },
    {
        'name': 'Barbara',
        'location': 'Financial District',
        'available_start': '10:30',
        'available_end': '16:30',
        'min_duration': 15
    }
]

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Golden Gate Park'
    schedule = []
    met_people = set()
    
    for person_name in order:
        person = next(p for p in people if p['name'] == person_name)
        location = person['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(person['available_start'])
        available_end = time_to_minutes(person['available_end'])
        min_duration = person['min_duration']
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            return None  # Can't meet this person
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        met_people.add(person['name'])
        current_time = meeting_end
        current_location = location
    
    # Check if we can meet Jeffrey after all other meetings
    jeffrey = next(p for p in people if p['name'] == 'Jeffrey')
    if 'Jeffrey' not in met_people:
        location = jeffrey['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(jeffrey['available_start'])
        available_end = time_to_minutes(jeffrey['available_end'])
        min_duration = jeffrey['min_duration']
        
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= available_end:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': 'Jeffrey',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            met_people.add('Jeffrey')
    
    return schedule if len(met_people) >= 3 else None  # At least meet 3 people

# Generate all possible orders of meeting people (excluding Jeffrey initially)
people_names = [p['name'] for p in people if p['name'] != 'Jeffrey']
all_orders = list(permutations(people_names))

best_schedule = None
max_people_met = 0

for order in all_orders:
    schedule = calculate_schedule(order)
    if schedule:
        people_met = len(set(item['person'] for item in schedule))
        if people_met > max_people_met or (people_met == max_people_met and len(schedule) > len(best_schedule or [])):
            best_schedule = schedule
            max_people_met = people_met

if not best_schedule:
    best_schedule = []

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))