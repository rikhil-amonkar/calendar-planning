import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str == '24:00':
        return 24 * 60
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Pacific Heights': 8
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Pacific Heights': 11
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8
    },
    'Fisherman\'s Wharf': {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 12
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13
    }
}

people = {
    'Jeffrey': {
        'location': 'Presidio',
        'available_start': '8:00',
        'available_end': '10:00',
        'duration': 105
    },
    'Steven': {
        'location': 'North Beach',
        'available_start': '13:30',
        'available_end': '22:00',
        'duration': 45
    },
    'Barbara': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '18:00',
        'available_end': '21:30',
        'duration': 30
    },
    'John': {
        'location': 'Pacific Heights',
        'available_start': '9:00',
        'available_end': '13:30',
        'duration': 15
    }
}

current_location = 'Nob Hill'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    
    for person in order:
        info = people[person]
        dest = info['location']
        travel = travel_times[loc][dest]
        arrival = time + travel
        
        available_start = time_to_minutes(info['available_start'])
        available_end = time_to_minutes(info['available_end'])
        duration = info['duration']
        
        start = max(arrival, available_start)
        end = start + duration
        
        if end > available_end:
            return None
        
        schedule.append({
            'person': person,
            'location': dest,
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
            'departure_time': end
        })
        
        loc = dest
        time = end
    
    return schedule

best_schedule = None
max_people = 0

# Try all possible orders of meeting people
for order in permutations(people.keys()):
    schedule = calculate_schedule(order)
    if schedule:
        if len(schedule) > max_people:
            max_people = len(schedule)
            best_schedule = schedule
        elif len(schedule) == max_people:
            # Prefer schedules that end earlier
            current_end = time_to_minutes(best_schedule[-1]['end_time'])
            new_end = time_to_minutes(schedule[-1]['end_time'])
            if new_end < current_end:
                best_schedule = schedule

# Format the output
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
    
    output = {
        "itinerary": itinerary
    }
else:
    output = {
        "itinerary": []
    }

print(json.dumps(output, indent=2))