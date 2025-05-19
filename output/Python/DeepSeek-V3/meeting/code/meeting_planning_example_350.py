import json
from itertools import permutations

def time_to_minutes(time_str):
    if time_str.endswith('AM') or time_str.endswith('PM'):
        time_part, period = time_str[:-2].strip(), time_str[-2:]
        hours, minutes = map(int, time_part.split(':'))
        if period == 'PM' and hours != 12:
            hours += 12
        elif period == 'AM' and hours == 12:
            hours = 0
        return hours * 60 + minutes
    else:
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Bayview': {
        'Pacific Heights': 23,
        'Mission District': 13,
        'Haight-Ashbury': 19,
        'Financial District': 19
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Mission District': 15,
        'Haight-Ashbury': 11,
        'Financial District': 13
    },
    'Mission District': {
        'Bayview': 15,
        'Pacific Heights': 16,
        'Haight-Ashbury': 12,
        'Financial District': 17
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'Pacific Heights': 12,
        'Mission District': 11,
        'Financial District': 21
    },
    'Financial District': {
        'Bayview': 19,
        'Pacific Heights': 13,
        'Mission District': 17,
        'Haight-Ashbury': 19
    }
}

friends = {
    'Mary': {
        'location': 'Pacific Heights',
        'available_start': time_to_minutes('10:00AM'),
        'available_end': time_to_minutes('7:00PM'),
        'duration': 45
    },
    'Lisa': {
        'location': 'Mission District',
        'available_start': time_to_minutes('8:30PM'),
        'available_end': time_to_minutes('10:00PM'),
        'duration': 75
    },
    'Betty': {
        'location': 'Haight-Ashbury',
        'available_start': time_to_minutes('7:15AM'),
        'available_end': time_to_minutes('5:15PM'),
        'duration': 90
    },
    'Charles': {
        'location': 'Financial District',
        'available_start': time_to_minutes('11:15AM'),
        'available_end': time_to_minutes('3:00PM'),
        'duration': 120
    }
}

current_location = 'Bayview'
current_time = time_to_minutes('9:00AM')

# Generate all possible orders to meet friends
friend_names = list(friends.keys())
possible_orders = permutations(friend_names)

best_schedule = None
max_meetings = 0

for order in possible_orders:
    temp_location = current_location
    temp_time = current_time
    schedule = []
    meetings = 0
    
    for friend in order:
        info = friends[friend]
        location = info['location']
        travel_time = travel_times[temp_location][location]
        arrival_time = temp_time + travel_time
        
        # Calculate meeting window
        start_time = max(arrival_time, info['available_start'])
        end_time = min(start_time + info['duration'], info['available_end'])
        
        if end_time > start_time and start_time >= arrival_time:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': friend,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            meetings += 1
            temp_location = location
            temp_time = end_time
    
    if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
        max_meetings = meetings
        best_schedule = schedule

# Output the best schedule
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))