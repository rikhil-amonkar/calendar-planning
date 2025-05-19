import json
from itertools import permutations

def time_to_minutes(time_str):
    """Convert time string 'H:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string 'H:MM'."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02d}"

# Input parameters
travel_times = {
    'Nob Hill': {
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Bayview': 19
    },
    'North Beach': {
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Bayview': 22
    },
    'Fisherman\'s Wharf': {
        'Nob Hill': 11,
        'North Beach': 6,
        'Bayview': 26
    },
    'Bayview': {
        'Nob Hill': 20,
        'North Beach': 21,
        'Fisherman\'s Wharf': 25
    }
}

friends = {
    'Helen': {
        'location': 'North Beach',
        'available_start': '7:00',
        'available_end': '16:45',
        'duration': 120
    },
    'Kimberly': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '16:30',
        'available_end': '21:00',
        'duration': 45
    },
    'Patricia': {
        'location': 'Bayview',
        'available_start': '18:00',
        'available_end': '21:15',
        'duration': 120
    }
}

current_location = 'Nob Hill'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
max_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings_scheduled = 0
    
    for friend_name in order:
        friend = friends[friend_name]
        location = friend['location']
        travel_time = travel_times[temp_location][location]
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        duration = friend['duration']
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        
        if meeting_end <= available_end:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': friend_name,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings_scheduled += 1
            temp_location = location
            temp_time = meeting_end
        else:
            break  # Can't meet this friend in this order
    
    if meetings_scheduled > max_meetings:
        max_meetings = meetings_scheduled
        best_schedule = schedule
    elif meetings_scheduled == max_meetings and meetings_scheduled > 0:
        # Prefer schedules that end earlier
        if not best_schedule or temp_time < time_to_minutes(best_schedule[-1]['end_time']):
            best_schedule = schedule

# Prepare output
output = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
print(json.dumps(output, indent=2))