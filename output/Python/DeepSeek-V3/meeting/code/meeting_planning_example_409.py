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
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

people = [
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': '15:30',
        'available_end': '18:30',
        'min_duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'available_start': '18:30',
        'available_end': '21:45',
        'min_duration': 30
    },
    {
        'name': 'Laura',
        'location': 'Nob Hill',
        'available_start': '8:45',
        'available_end': '16:15',
        'min_duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'available_start': '18:45',
        'available_end': '21:45',
        'min_duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Embarcadero',
        'available_start': '17:30',
        'available_end': '22:00',
        'min_duration': 45
    }
]

current_location = 'Fisherman\'s Wharf'
current_time = time_to_minutes('9:00')

def get_possible_schedules():
    # Generate all possible orders of meeting people
    possible_orders = permutations(people)
    valid_schedules = []
    
    for order in possible_orders:
        schedule = []
        loc = current_location
        time = current_time
        valid = True
        
        for person in order:
            # Calculate travel time
            travel_time = travel_times[loc][person['location']]
            arrival_time = time + travel_time
            
            # Check if we can meet this person
            available_start = time_to_minutes(person['available_start'])
            available_end = time_to_minutes(person['available_end'])
            
            # Determine meeting window
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + person['min_duration']
            
            if meeting_end > available_end:
                valid = False
                break
            
            # Add to schedule
            schedule.append({
                'person': person['name'],
                'location': person['location'],
                'start_time': meeting_start,
                'end_time': meeting_end
            })
            
            # Update current location and time
            loc = person['location']
            time = meeting_end
        
        if valid:
            valid_schedules.append(schedule)
    
    return valid_schedules

def evaluate_schedule(schedule):
    # Score based on number of people met and total time spent
    return len(schedule)

def find_best_schedule():
    schedules = get_possible_schedules()
    if not schedules:
        return None
    
    best_schedule = max(schedules, key=evaluate_schedule)
    return best_schedule

best_schedule = find_best_schedule()

if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": minutes_to_time(meeting['start_time']),
            "end_time": minutes_to_time(meeting['end_time'])
        })
    
    result = {
        "itinerary": itinerary
    }
else:
    result = {
        "itinerary": []
    }

print(json.dumps(result, indent=2))