import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17
    }
}

# Constraints
friends = [
    {
        'name': 'Sarah',
        'location': 'Sunset District',
        'available_start': '10:45',
        'available_end': '19:00',
        'min_duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Haight-Ashbury',
        'available_start': '11:45',
        'available_end': '15:45',
        'min_duration': 90
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': '11:00',
        'available_end': '17:15',
        'min_duration': 120
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': '18:15',
        'available_end': '20:45',
        'min_duration': 90
    }
]

def calculate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Richmond District'
    schedule = []
    
    for friend_idx in order:
        friend = friends[friend_idx]
        destination = friend['location']
        travel_time = travel_times[current_location][destination]
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate meeting start time
        meeting_start = max(arrival_time, available_start)
        if meeting_start + min_duration > available_end:
            return None  # Not enough time to meet
        
        meeting_end = meeting_start + min_duration
        schedule.append({
            'action': 'meet',
            'location': destination,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = destination
    
    # Check if we can meet Michelle (last constraint)
    michelle = friends[3]
    if current_location != michelle['location']:
        travel_time = travel_times[current_location][michelle['location']]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(michelle['available_start'])
        available_end = time_to_minutes(michelle['available_end'])
        min_duration = michelle['min_duration']
        
        meeting_start = max(arrival_time, available_start)
        if meeting_start + min_duration > available_end:
            return None
        
        meeting_end = meeting_start + min_duration
        schedule.append({
            'action': 'meet',
            'location': michelle['location'],
            'person': michelle['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
    
    return schedule

# Generate all possible orders of meeting Sarah, Richard, Elizabeth (Michelle is last)
possible_orders = permutations([0, 1, 2])
best_schedule = None
max_meetings = 0

for order in possible_orders:
    schedule = calculate_schedule(order)
    if schedule and len(schedule) > max_meetings:
        best_schedule = schedule
        max_meetings = len(schedule)

if not best_schedule:
    # Try meeting just some friends
    for num_meetings in range(3, 0, -1):
        for order in permutations([0, 1, 2], num_meetings):
            schedule = calculate_schedule(order)
            if schedule:
                best_schedule = schedule
                break
        if best_schedule:
            break

output = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
print(json.dumps(output, indent=2))