import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    'Richmond District': {
        'Richmond District': 0,
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Chinatown': 0,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Sunset District': 0,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Alamo Square': 0,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Financial District': 0,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'North Beach': 0,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Embarcadero': 0,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Presidio': 0,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Golden Gate Park': 0,
        'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22,
        'Bayview': 0
    }
}

# Meeting constraints
meetings = [
    {'name': 'Robert', 'location': 'Chinatown', 'start': 7.75, 'end': 17.5, 'duration': 2.0},
    {'name': 'David', 'location': 'Sunset District', 'start': 12.5, 'end': 19.75, 'duration': 0.75},
    {'name': 'Matthew', 'location': 'Alamo Square', 'start': 8.75, 'end': 13.75, 'duration': 1.5},
    {'name': 'Jessica', 'location': 'Financial District', 'start': 9.5, 'end': 18.75, 'duration': 0.75},
    {'name': 'Melissa', 'location': 'North Beach', 'start': 7.25, 'end': 16.75, 'duration': 0.75},
    {'name': 'Mark', 'location': 'Embarcadero', 'start': 15.25, 'end': 17.0, 'duration': 0.75},
    {'name': 'Deborah', 'location': 'Presidio', 'start': 19.0, 'end': 19.75, 'duration': 0.75},
    {'name': 'Karen', 'location': 'Golden Gate Park', 'start': 19.5, 'end': 22.0, 'duration': 2.0},
    {'name': 'Laura', 'location': 'Bayview', 'start': 21.25, 'end': 22.25, 'duration': 0.25}
]

def time_to_float(time_str):
    if isinstance(time_str, str):
        h, m = map(int, time_str.split(':'))
        return h + m / 60.0
    return time_str

def float_to_time(time_float):
    h = int(time_float)
    m = int((time_float - h) * 60)
    return f"{h}:{m:02d}"

def is_valid_schedule(schedule):
    current_time = 9.0  # Start at 9:00 AM
    current_location = 'Richmond District'
    
    for entry in schedule:
        travel_time = travel_times[current_location][entry['location']] / 60.0
        arrival_time = current_time + travel_time
        
        # Check if arrival is before meeting end and can fit duration
        if arrival_time > entry['end']:
            return False
        
        start_time = max(arrival_time, entry['start'])
        end_time = start_time + entry['duration']
        
        if end_time > entry['end']:
            return False
        
        current_time = end_time
        current_location = entry['location']
    
    return True

def calculate_total_meetings(schedule):
    total = 0
    current_time = 9.0
    current_location = 'Richmond District'
    
    for entry in schedule:
        travel_time = travel_times[current_location][entry['location']] / 60.0
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, entry['start'])
        end_time = start_time + entry['duration']
        
        if end_time > entry['end']:
            return -1
        
        total += 1
        current_time = end_time
        current_location = entry['location']
    
    return total

def generate_itinerary(schedule):
    itinerary = []
    current_time = 9.0
    current_location = 'Richmond District'
    
    for entry in schedule:
        travel_time = travel_times[current_location][entry['location']] / 60.0
        arrival_time = current_time + travel_time
        start_time = max(arrival_time, entry['start'])
        end_time = start_time + entry['duration']
        
        itinerary.append({
            'action': 'meet',
            'location': entry['location'],
            'person': entry['name'],
            'start_time': float_to_time(start_time),
            'end_time': float_to_time(end_time)
        })
        
        current_time = end_time
        current_location = entry['location']
    
    return itinerary

def find_best_schedule():
    best_schedule = None
    max_meetings = 0
    
    # Try all permutations of meetings (limited to 5 for performance)
    for perm in permutations(meetings, min(5, len(meetings))):
        if is_valid_schedule(perm):
            total = calculate_total_meetings(perm)
            if total > max_meetings:
                max_meetings = total
                best_schedule = perm
    
    # If no permutation found, try greedy approach
    if best_schedule is None:
        sorted_meetings = sorted(meetings, key=lambda x: x['start'])
        current_time = 9.0
        current_location = 'Richmond District'
        best_schedule = []
        
        for meeting in sorted_meetings:
            travel_time = travel_times[current_location][meeting['location']] / 60.0
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, meeting['start'])
            end_time = start_time + meeting['duration']
            
            if end_time <= meeting['end']:
                best_schedule.append(meeting)
                current_time = end_time
                current_location = meeting['location']
    
    return best_schedule

best_schedule = find_best_schedule()
itinerary = generate_itinerary(best_schedule)

output = {
    "itinerary": itinerary
}

print(json.dumps(output, indent=2))