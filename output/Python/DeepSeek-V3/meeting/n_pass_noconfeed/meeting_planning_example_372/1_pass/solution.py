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
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Golden Gate Park': 11,
        'Mission District': 24
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Golden Gate Park': 9,
        'Mission District': 10
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'Mission District': 16
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Mission District': 17
    },
    'Mission District': {
        'Sunset District': 24,
        'Alamo Square': 11,
        'Russian Hill': 15,
        'Golden Gate Park': 17
    }
}

friends = {
    'Charles': {
        'location': 'Alamo Square',
        'available_start': '18:00',
        'available_end': '20:45',
        'min_duration': 90
    },
    'Margaret': {
        'location': 'Russian Hill',
        'available_start': '9:00',
        'available_end': '16:00',
        'min_duration': 30
    },
    'Daniel': {
        'location': 'Golden Gate Park',
        'available_start': '8:00',
        'available_end': '13:30',
        'min_duration': 15
    },
    'Stephanie': {
        'location': 'Mission District',
        'available_start': '20:30',
        'available_end': '22:00',
        'min_duration': 90
    }
}

current_location = 'Sunset District'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    met_friends = set()
    
    for friend in order:
        info = friends[friend]
        dest = info['location']
        travel = travel_times[loc][dest]
        arrival = time + travel
        
        start_window = time_to_minutes(info['available_start'])
        end_window = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        # Calculate possible meeting time
        meeting_start = max(arrival, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > end_window:
            return None  # Cannot meet this friend
        
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        met_friends.add(friend)
        loc = dest
        time = meeting_end
    
    # Check if we can meet Stephanie after Charles
    if 'Charles' in met_friends and 'Stephanie' not in met_friends:
        info = friends['Stephanie']
        dest = info['location']
        travel = travel_times[loc][dest]
        arrival = time + travel
        
        start_window = time_to_minutes(info['available_start'])
        end_window = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        meeting_start = max(arrival, start_window)
        meeting_end = meeting_start + min_duration
        
        if meeting_end <= end_window:
            schedule.append({
                'action': 'meet',
                'location': dest,
                'person': 'Stephanie',
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            met_friends.add('Stephanie')
    
    return schedule if len(met_friends) >= len(order) else None

# Generate all possible friend orders (excluding Stephanie initially)
friend_names = ['Margaret', 'Daniel', 'Charles']
best_schedule = None
max_meetings = 0

for perm in permutations(friend_names):
    schedule = calculate_schedule(perm)
    if schedule:
        num_meetings = len([item for item in schedule if item['action'] == 'meet'])
        if num_meetings > max_meetings or (num_meetings == max_meetings and len(schedule) > len(best_schedule or [])):
            best_schedule = schedule
            max_meetings = num_meetings

# Output the best schedule
if best_schedule:
    output = {
        "itinerary": best_schedule
    }
else:
    output = {
        "itinerary": []
    }

print(json.dumps(output, indent=2))