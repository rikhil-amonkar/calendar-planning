import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'The Castro': {
        'Bayview': 19,
        'Pacific Heights': 16,
        'Alamo Square': 8,
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11
    },
    'Bayview': {
        'The Castro': 20,
        'Pacific Heights': 23,
        'Alamo Square': 16,
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Bayview': 22,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 13,
        'Golden Gate Park': 15
    },
    'Alamo Square': {
        'The Castro': 8,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 9
    },
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Alamo Square': 20,
        'Golden Gate Park': 25
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Alamo Square': 10,
        'Fisherman\'s Wharf': 24
    }
}

people = {
    'Rebecca': {
        'location': 'Bayview',
        'start': time_to_minutes('9:00'),
        'end': time_to_minutes('12:45'),
        'duration': 90
    },
    'Amanda': {
        'location': 'Pacific Heights',
        'start': time_to_minutes('18:30'),
        'end': time_to_minutes('21:45'),
        'duration': 90
    },
    'James': {
        'location': 'Alamo Square',
        'start': time_to_minutes('9:45'),
        'end': time_to_minutes('21:15'),
        'duration': 90
    },
    'Sarah': {
        'location': 'Fisherman\'s Wharf',
        'start': time_to_minutes('8:00'),
        'end': time_to_minutes('21:30'),
        'duration': 90
    },
    'Melissa': {
        'location': 'Golden Gate Park',
        'start': time_to_minutes('9:00'),
        'end': time_to_minutes('18:45'),
        'duration': 90
    }
}

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'The Castro'
    schedule = []
    
    for person in order:
        info = people[person]
        location = info['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Calculate meeting window
        meeting_start = max(arrival_time, info['start'])
        meeting_end = meeting_start + info['duration']
        
        if meeting_end > info['end']:
            return None  # Not enough time to meet
        
        schedule.append({
            'person': person,
            'location': location,
            'start_time': meeting_start,
            'end_time': meeting_end,
            'travel_time': travel_time
        })
        
        current_time = meeting_end
        current_location = location
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return 0
    # Count number of people met
    return len(schedule)

best_schedule = None
best_score = 0

# Try all possible orders of meeting people
for order in permutations(people.keys()):
    schedule = calculate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Convert to output format
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
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))