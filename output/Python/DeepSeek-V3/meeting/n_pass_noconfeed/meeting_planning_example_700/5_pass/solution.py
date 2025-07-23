import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

travel_times = {
    'Presidio': {
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
        'Alamo Square': 19,
        'Sunset District': 15,
        'Nob Hill': 18,
        'North Beach': 18
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Golden Gate Park': 12,
        'Fisherman\'s Wharf': 10,
        'Marina District': 5,
        'Alamo Square': 8,
        'Sunset District': 15,
        'Nob Hill': 7,
        'North Beach': 10
    },
    'Golden Gate Park': {
        'Presidio': 12,
        'Pacific Heights': 12,
        'Fisherman\'s Wharf': 18,
        'Marina District': 15,
        'Alamo Square': 15,
        'Sunset District': 8,
        'Nob Hill': 16,
        'North Beach': 18
    },
    'Fisherman\'s Wharf': {
        'Presidio': 19,
        'Pacific Heights': 10,
        'Golden Gate Park': 18,
        'Marina District': 5,
        'Alamo Square': 15,
        'Sunset District': 20,
        'Nob Hill': 8,
        'North Beach': 5
    },
    'Marina District': {
        'Presidio': 11,
        'Pacific Heights': 5,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 5,
        'Alamo Square': 10,
        'Sunset District': 15,
        'Nob Hill': 5,
        'North Beach': 5
    },
    'Alamo Square': {
        'Presidio': 19,
        'Pacific Heights': 8,
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 15,
        'Marina District': 10,
        'Sunset District': 15,
        'Nob Hill': 10,
        'North Beach': 12
    },
    'Sunset District': {
        'Presidio': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 8,
        'Fisherman\'s Wharf': 20,
        'Marina District': 15,
        'Alamo Square': 15,
        'Nob Hill': 15,
        'North Beach': 18
    },
    'Nob Hill': {
        'Presidio': 18,
        'Pacific Heights': 7,
        'Golden Gate Park': 16,
        'Fisherman\'s Wharf': 8,
        'Marina District': 5,
        'Alamo Square': 10,
        'Sunset District': 15,
        'North Beach': 8
    },
    'North Beach': {
        'Presidio': 18,
        'Pacific Heights': 10,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 5,
        'Marina District': 5,
        'Alamo Square': 12,
        'Sunset District': 18,
        'Nob Hill': 8
    }
}

friends = [
    {'name': 'Alice', 'location': 'Pacific Heights', 'available_start': '9:30', 'available_end': '10:30', 'min_duration': 30, 'met': False},
    {'name': 'Bob', 'location': 'Fisherman\'s Wharf', 'available_start': '10:00', 'available_end': '11:30', 'min_duration': 45, 'met': False},
    {'name': 'Charlie', 'location': 'Nob Hill', 'available_start': '11:00', 'available_end': '12:30', 'min_duration': 30, 'met': False},
    {'name': 'Dana', 'location': 'Golden Gate Park', 'available_start': '10:30', 'available_end': '12:00', 'min_duration': 15, 'met': False},
    {'name': 'Eve', 'location': 'Alamo Square', 'available_start': '11:30', 'available_end': '12:30', 'min_duration': 30, 'met': False}
]

def is_meeting_possible(current_time, friend, current_location):
    travel_time = travel_times[current_location][friend['location']]
    meeting_start = current_time + travel_time
    meeting_end = meeting_start + friend['min_duration']
    
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    
    if meeting_start >= available_start and meeting_end <= available_end:
        return True, meeting_start, meeting_end
    return False, 0, 0

def find_best_schedule():
    best_schedule = []
    max_meetings = 0
    
    # Try all permutations of friends to find the best possible schedule
    for friend_order in permutations(friends):
        current_time = time_to_minutes('9:00')
        current_location = 'Presidio'
        schedule = []
        
        for friend in friend_order:
            possible, start, end = is_meeting_possible(current_time, friend, current_location)
            if possible:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start),
                    'end_time': minutes_to_time(end)
                })
                current_time = end
                current_location = friend['location']
        
        if len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule
            # Early exit if we've found a schedule that meets all friends
            if max_meetings == len(friends):
                break
    
    return best_schedule

best_schedule = find_best_schedule()
output = {
    "itinerary": best_schedule
}
print(json.dumps(output, indent=2))