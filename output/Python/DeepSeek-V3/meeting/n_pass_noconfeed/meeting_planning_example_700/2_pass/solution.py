import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data (same as before)
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
    # ... (rest of the travel_times dictionary remains the same)
}

friends = [
    # ... (friends list remains the same)
]

def is_meeting_possible(current_time, friend, current_location):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    travel_time = travel_times[current_location][friend['location']]
    meeting_start = current_time + travel_time
    meeting_end = meeting_start + friend['min_duration']
    
    if meeting_start >= available_start and meeting_end <= available_end:
        return True, meeting_start, meeting_end
    return False, 0, 0

def find_best_schedule():
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    schedule = []
    remaining_friends = [f for f in friends if not f['met']]
    
    # Sort friends by their available window size (smallest first)
    remaining_friends.sort(key=lambda x: time_to_minutes(x['available_end']) - time_to_minutes(x['available_start']))
    
    while remaining_friends:
        found = False
        for friend in remaining_friends:
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
                remaining_friends.remove(friend)
                found = True
                break
        
        if not found:
            break
    
    return schedule

best_schedule = find_best_schedule()
output = {
    "itinerary": best_schedule
}
print(json.dumps(output, indent=2))