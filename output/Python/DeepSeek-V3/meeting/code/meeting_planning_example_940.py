import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    'Union Square': {
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Russian Hill': 13,
        'Marina District': 18,
        'North Beach': 10,
        'Chinatown': 7,
        'Pacific Heights': 15,
        'The Castro': 17,
        'Nob Hill': 9,
        'Sunset District': 27
    },
    'Mission District': {
        'Union Square': 15,
        'Fisherman\'s Wharf': 22,
        'Russian Hill': 15,
        'Marina District': 19,
        'North Beach': 17,
        'Chinatown': 16,
        'Pacific Heights': 16,
        'The Castro': 7,
        'Nob Hill': 12,
        'Sunset District': 24
    },
    'Fisherman\'s Wharf': {
        'Union Square': 13,
        'Mission District': 22,
        'Russian Hill': 7,
        'Marina District': 9,
        'North Beach': 6,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'The Castro': 27,
        'Nob Hill': 11,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Marina District': 7,
        'North Beach': 5,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'The Castro': 21,
        'Nob Hill': 5,
        'Sunset District': 23
    },
    'Marina District': {
        'Union Square': 16,
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Pacific Heights': 7,
        'The Castro': 22,
        'Nob Hill': 12,
        'Sunset District': 19
    },
    'North Beach': {
        'Union Square': 7,
        'Mission District': 18,
        'Fisherman\'s Wharf': 5,
        'Russian Hill': 4,
        'Marina District': 9,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 23,
        'Nob Hill': 7,
        'Sunset District': 27
    },
    'Chinatown': {
        'Union Square': 7,
        'Mission District': 17,
        'Fisherman\'s Wharf': 8,
        'Russian Hill': 7,
        'Marina District': 12,
        'North Beach': 3,
        'Pacific Heights': 10,
        'The Castro': 22,
        'Nob Hill': 9,
        'Sunset District': 29
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Mission District': 15,
        'Fisherman\'s Wharf': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'North Beach': 9,
        'Chinatown': 11,
        'The Castro': 16,
        'Nob Hill': 8,
        'Sunset District': 21
    },
    'The Castro': {
        'Union Square': 19,
        'Mission District': 7,
        'Fisherman\'s Wharf': 24,
        'Russian Hill': 18,
        'Marina District': 21,
        'North Beach': 20,
        'Chinatown': 22,
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Sunset District': 17
    },
    'Nob Hill': {
        'Union Square': 7,
        'Mission District': 13,
        'Fisherman\'s Wharf': 10,
        'Russian Hill': 5,
        'Marina District': 11,
        'North Beach': 8,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 17,
        'Sunset District': 24
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Russian Hill': 24,
        'Marina District': 21,
        'North Beach': 28,
        'Chinatown': 30,
        'Pacific Heights': 21,
        'The Castro': 17,
        'Nob Hill': 27
    }
}

# Friend availability
friends = {
    'Kevin': {
        'location': 'Mission District',
        'start': 20.75,  # 8:45 PM
        'end': 21.75,    # 9:45 PM
        'duration': 1.0  # 60 minutes
    },
    'Mark': {
        'location': 'Fisherman\'s Wharf',
        'start': 17.25,  # 5:15 PM
        'end': 20.0,     # 8:00 PM
        'duration': 1.5  # 90 minutes
    },
    'Jessica': {
        'location': 'Russian Hill',
        'start': 9.0,    # 9:00 AM
        'end': 15.0,     # 3:00 PM
        'duration': 2.0  # 120 minutes
    },
    'Jason': {
        'location': 'Marina District',
        'start': 15.25, # 3:15 PM
        'end': 21.75,    # 9:45 PM
        'duration': 2.0  # 120 minutes
    },
    'John': {
        'location': 'North Beach',
        'start': 9.75,   # 9:45 AM
        'end': 18.0,     # 6:00 PM
        'duration': 0.25 # 15 minutes
    },
    'Karen': {
        'location': 'Chinatown',
        'start': 16.75,  # 4:45 PM
        'end': 19.0,     # 7:00 PM
        'duration': 1.25 # 75 minutes
    },
    'Sarah': {
        'location': 'Pacific Heights',
        'start': 17.5,   # 5:30 PM
        'end': 18.25,    # 6:15 PM
        'duration': 0.75 # 45 minutes
    },
    'Amanda': {
        'location': 'The Castro',
        'start': 20.0,   # 8:00 PM
        'end': 21.25,    # 9:15 PM
        'duration': 1.0 # 60 minutes
    },
    'Nancy': {
        'location': 'Nob Hill',
        'start': 9.75,   # 9:45 AM
        'end': 13.0,     # 1:00 PM
        'duration': 0.75 # 45 minutes
    },
    'Rebecca': {
        'location': 'Sunset District',
        'start': 8.75,   # 8:45 AM
        'end': 15.0,     # 3:00 PM
        'duration': 1.25 # 75 minutes
    }
}

def time_to_float(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours + minutes / 60.0

def float_to_time(time_float):
    hours = int(time_float)
    minutes = int((time_float - hours) * 60)
    return f"{hours}:{minutes:02d}"

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf')) / 60.0

def is_schedule_valid(schedule):
    current_time = 9.0  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    
    for entry in schedule:
        # Travel to the location
        travel_time = get_travel_time(current_location, entry['location'])
        arrival_time = current_time + travel_time
        
        # Check if we arrive before the meeting window closes
        friend = friends[entry['person']]
        latest_start = friend['end'] - entry['duration']
        
        if arrival_time > latest_start:
            return False
        
        # Start the meeting as soon as possible after arrival
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + entry['duration']
        
        if end_time > friend['end']:
            return False
        
        current_time = end_time
        current_location = entry['location']
    
    return True

def calculate_total_meeting_time(schedule):
    total = 0
    for entry in schedule:
        total += entry['duration']
    return total

def generate_possible_schedules():
    friend_names = list(friends.keys())
    # We'll try permutations of all friends, but limit to reasonable length for performance
    # In reality, we'd need a more sophisticated approach for larger problems
    for perm in permutations(friend_names, min(5, len(friend_names))):
        schedule = []
        for name in perm:
            schedule.append({
                'person': name,
                'location': friends[name]['location'],
                'duration': friends[name]['duration']
            })
        if is_schedule_valid(schedule):
            yield schedule

def find_best_schedule():
    best_schedule = None
    best_time = 0
    
    for schedule in generate_possible_schedules():
        total_time = calculate_total_meeting_time(schedule)
        if total_time > best_time:
            best_time = total_time
            best_schedule = schedule
    
    return best_schedule

def build_itinerary(schedule):
    if not schedule:
        return {"itinerary": []}
    
    itinerary = []
    current_time = 9.0  # Start at Union Square at 9:00 AM
    current_location = 'Union Square'
    
    for entry in schedule:
        # Travel to the location
        travel_time = get_travel_time(current_location, entry['location'])
        arrival_time = current_time + travel_time
        
        # Calculate meeting times
        friend = friends[entry['person']]
        start_time = max(arrival_time, friend['start'])
        end_time = start_time + entry['duration']
        
        # Add travel and meeting to itinerary
        if arrival_time < start_time:
            itinerary.append({
                "action": "travel",
                "from": current_location,
                "to": entry['location'],
                "start_time": float_to_time(current_time),
                "end_time": float_to_time(arrival_time)
            })
            current_time = arrival_time
        
        itinerary.append({
            "action": "meet",
            "location": entry['location'],
            "person": entry['person'],
            "start_time": float_to_time(start_time),
            "end_time": float_to_time(end_time)
        })
        
        current_time = end_time
        current_location = entry['location']
    
    return {"itinerary": itinerary}

best_schedule = find_best_schedule()
result = build_itinerary(best_schedule)
print(json.dumps(result, indent=2))