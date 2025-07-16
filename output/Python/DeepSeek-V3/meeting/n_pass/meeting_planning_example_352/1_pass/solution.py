import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

# Input data
travel_times = {
    'Union Square': {
        'Nob Hill': 9,
        'Haight-Ashbury': 18,
        'Chinatown': 7,
        'Marina District': 18
    },
    'Nob Hill': {
        'Union Square': 7,
        'Haight-Ashbury': 13,
        'Chinatown': 6,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Union Square': 17,
        'Nob Hill': 15,
        'Chinatown': 19,
        'Marina District': 17
    },
    'Chinatown': {
        'Union Square': 7,
        'Nob Hill': 8,
        'Haight-Ashbury': 19,
        'Marina District': 12
    },
    'Marina District': {
        'Union Square': 16,
        'Nob Hill': 12,
        'Haight-Ashbury': 16,
        'Chinatown': 16
    }
}

friends = [
    {
        'name': 'Karen',
        'location': 'Nob Hill',
        'available_start': '21:15',
        'available_end': '21:45',
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Haight-Ashbury',
        'available_start': '12:30',
        'available_end': '19:45',
        'duration': 90
    },
    {
        'name': 'Sandra',
        'location': 'Chinatown',
        'available_start': '7:15',
        'available_end': '19:15',
        'duration': 75
    },
    {
        'name': 'Nancy',
        'location': 'Marina District',
        'available_start': '11:00',
        'available_end': '20:15',
        'duration': 105
    }
]

current_location = 'Union Square'
current_time = time_to_minutes('9:00')

def calculate_schedule(order):
    schedule = []
    loc = current_location
    time = current_time
    met_friends = []
    
    for friend_idx in order:
        friend = friends[friend_idx]
        travel_time = travel_times[loc][friend['location']]
        arrival_time = time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > available_end:
            return None  # Can't meet this friend
        
        schedule.append({
            'action': 'travel',
            'location': friend['location'],
            'start_time': minutes_to_time(time),
            'end_time': minutes_to_time(arrival_time)
        })
        
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        met_friends.append(friend['name'])
        loc = friend['location']
        time = meeting_end
    
    return {
        'schedule': schedule,
        'met_friends': met_friends,
        'total_met': len(met_friends)
    }

# Try all possible orders of meeting friends
best_schedule = None
max_met = 0

for perm in permutations(range(len(friends))):
    result = calculate_schedule(perm)
    if result and result['total_met'] > max_met:
        max_met = result['total_met']
        best_schedule = result['schedule']
    elif result and result['total_met'] == max_met:
        # Prefer schedules that end earlier
        if not best_schedule or time_to_minutes(result['schedule'][-1]['end_time']) < time_to_minutes(best_schedule[-1]['end_time']):
            best_schedule = result['schedule']

# Prepare output
if best_schedule:
    output = {
        "itinerary": best_schedule
    }
else:
    output = {
        "itinerary": []
    }

print(json.dumps(output, indent=2))