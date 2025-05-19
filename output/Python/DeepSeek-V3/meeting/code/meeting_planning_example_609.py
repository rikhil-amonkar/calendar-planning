import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29,
        'Presidio': 19
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24,
        'Presidio': 25
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16,
        'Presidio': 18
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21,
        'Presidio': 11
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26,
        'Presidio': 24
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Presidio': 11
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11,
        'Presidio': 16
    },
    'Presidio': {
        'Chinatown': 21,
        'Mission District': 26,
        'Alamo Square': 18,
        'Pacific Heights': 11,
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Sunset District': 15
    }
}

# People's availability
people = {
    'David': {
        'location': 'Mission District',
        'start': 8.0,
        'end': 19.75,
        'duration': 0.75
    },
    'Kenneth': {
        'location': 'Alamo Square',
        'start': 14.0,
        'end': 19.75,
        'duration': 2.0
    },
    'John': {
        'location': 'Pacific Heights',
        'start': 17.0,
        'end': 20.0,
        'duration': 0.25
    },
    'Charles': {
        'location': 'Union Square',
        'start': 21.75,
        'end': 22.75,
        'duration': 1.0
    },
    'Deborah': {
        'location': 'Golden Gate Park',
        'start': 7.0,
        'end': 18.25,
        'duration': 1.5
    },
    'Karen': {
        'location': 'Sunset District',
        'start': 17.75,
        'end': 21.25,
        'duration': 0.25
    },
    'Carol': {
        'location': 'Presidio',
        'start': 8.25,
        'end': 9.25,
        'duration': 0.5
    }
}

def time_to_float(time_str):
    if isinstance(time_str, float):
        return time_str
    h, m = map(int, time_str.split(':'))
    return h + m / 60.0

def float_to_time(time_float):
    h = int(time_float)
    m = int((time_float - h) * 60)
    return f"{h}:{m:02d}"

def calculate_schedule(order):
    current_time = 9.0  # Start at Chinatown at 9:00
    current_location = 'Chinatown'
    schedule = []
    met_people = set()
    
    for person in order:
        if person in met_people:
            continue
            
        info = people[person]
        location = info['location']
        travel_time = travel_times[current_location][location] / 60.0
        arrival_time = current_time + travel_time
        
        # Check if we can meet this person
        meeting_start = max(arrival_time, info['start'])
        meeting_end = meeting_start + info['duration']
        
        if meeting_end > info['end']:
            continue  # Can't meet this person in this order
            
        # Add to schedule
        schedule.append({
            'person': person,
            'location': location,
            'start_time': meeting_start,
            'end_time': meeting_end,
            'duration': info['duration']
        })
        
        met_people.add(person)
        current_time = meeting_end
        current_location = location
    
    return schedule, len(met_people)

def generate_possible_orders():
    # Generate possible meeting orders (prioritizing people with tighter schedules)
    all_people = list(people.keys())
    # Try Carol first since she's only available in the morning
    priority_order = ['Carol'] + [p for p in all_people if p != 'Carol']
    return [priority_order] + list(permutations(all_people))

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try different meeting orders
    for order in generate_possible_orders():
        schedule, num_meetings = calculate_schedule(order)
        if num_meetings > max_meetings or (num_meetings == max_meetings and len(schedule) > len(best_schedule)):
            best_schedule = schedule
            max_meetings = num_meetings
    
    return best_schedule

def format_schedule(schedule):
    itinerary = []
    for meeting in schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": float_to_time(meeting['start_time']),
            "end_time": float_to_time(meeting['end_time'])
        })
    return {"itinerary": itinerary}

# Main execution
best_schedule = find_best_schedule()
result = format_schedule(best_schedule)
print(json.dumps(result, indent=2))