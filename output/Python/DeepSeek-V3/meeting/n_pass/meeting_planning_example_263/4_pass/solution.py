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
    'Bayview': {
        'Embarcadero': 19,
        'Fisherman\'s Wharf': 25,
        'Financial District': 19
    },
    'Embarcadero': {
        'Bayview': 21,
        'Fisherman\'s Wharf': 6,
        'Financial District': 5
    },
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Financial District': {
        'Bayview': 19,
        'Embarcadero': 4,
        'Fisherman\'s Wharf': 10
    }
}

friends = {
    'Betty': {
        'location': 'Embarcadero',
        'available_start': '19:45',
        'available_end': '21:45',
        'min_duration': 15
    },
    'Karen': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '8:45',
        'available_end': '15:00',
        'min_duration': 30
    },
    'Anthony': {
        'location': 'Financial District',
        'available_start': '9:15',
        'available_end': '21:30',
        'min_duration': 105
    }
}

current_location = 'Bayview'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    met_friends = set()
    
    for friend in order:
        data = friends[friend]
        dest = data['location']
        travel_time = travel_times[loc][dest]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(data['available_start'])
        available_end = time_to_minutes(data['available_end'])
        min_duration = data['min_duration']
        
        # Calculate meeting window
        start_time = max(arrival_time, available_start)
        end_time = start_time + min_duration
        
        # Check if meeting is possible
        if end_time > available_end:
            continue  # Skip this friend if we can't meet them
            
        if start_time < available_start:
            continue  # Shouldn't happen due to max() above, but just in case
            
        # Ensure we're not trying to meet someone outside their window
        if not (available_start <= start_time <= available_end - min_duration):
            continue
            
        schedule.append({
            'action': 'meet',
            'location': dest,
            'person': friend,
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        met_friends.add(friend)
        time = end_time
        loc = dest
    
    return schedule, met_friends

best_schedule = None
max_met = 0

# Try all possible orders of meeting friends
for order in permutations(friends.keys()):
    schedule, met_friends = calculate_schedule(order)
    if len(met_friends) > max_met or (len(met_friends) == max_met and schedule is not None):
        best_schedule = schedule
        max_met = len(met_friends)
        if max_met == len(friends):
            break  # Found optimal solution

if best_schedule is None:
    best_schedule = []

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))