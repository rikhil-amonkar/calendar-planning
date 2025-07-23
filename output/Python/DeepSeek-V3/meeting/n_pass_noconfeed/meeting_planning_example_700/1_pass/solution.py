import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
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
        'Golden Gate Park': 15,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Alamo Square': 10,
        'Sunset District': 21,
        'Nob Hill': 8,
        'North Beach': 9
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Pacific Heights': 16,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Alamo Square': 9,
        'Sunset District': 10,
        'Nob Hill': 20,
        'North Beach': 23
    },
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
        'Marina District': 9,
        'Alamo Square': 21,
        'Sunset District': 27,
        'Nob Hill': 11,
        'North Beach': 6
    },
    'Marina District': {
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Fisherman\'s Wharf': 10,
        'Alamo Square': 15,
        'Sunset District': 19,
        'Nob Hill': 12,
        'North Beach': 11
    },
    'Alamo Square': {
        'Presidio': 17,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Sunset District': 16,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'Sunset District': {
        'Presidio': 16,
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'Fisherman\'s Wharf': 29,
        'Marina District': 21,
        'Alamo Square': 17,
        'Nob Hill': 27,
        'North Beach': 28
    },
    'Nob Hill': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
        'Alamo Square': 11,
        'Sunset District': 24,
        'North Beach': 8
    },
    'North Beach': {
        'Presidio': 17,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
        'Alamo Square': 16,
        'Sunset District': 27,
        'Nob Hill': 7
    }
}

friends = [
    {
        'name': 'Kevin',
        'location': 'Pacific Heights',
        'available_start': '7:15',
        'available_end': '8:45',
        'min_duration': 90,
        'met': False
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': '20:00',
        'available_end': '21:00',
        'min_duration': 15,
        'met': False
    },
    {
        'name': 'Emily',
        'location': 'Fisherman\'s Wharf',
        'available_start': '16:15',
        'available_end': '19:00',
        'min_duration': 30,
        'met': False
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': '18:15',
        'available_end': '19:45',
        'min_duration': 75,
        'met': False
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': '17:00',
        'available_end': '19:00',
        'min_duration': 120,
        'met': False
    },
    {
        'name': 'Laura',
        'location': 'Sunset District',
        'available_start': '19:00',
        'available_end': '21:15',
        'min_duration': 75,
        'met': False
    },
    {
        'name': 'Mary',
        'location': 'Nob Hill',
        'available_start': '17:30',
        'available_end': '19:00',
        'min_duration': 45,
        'met': False
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': '11:00',
        'available_end': '12:15',
        'min_duration': 45,
        'met': False
    }
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
    best_schedule = []
    max_met = 0
    
    # Try all permutations of friends to find the best schedule
    for perm in permutations(friends):
        current_time = time_to_minutes('9:00')
        current_location = 'Presidio'
        schedule = []
        met_count = 0
        
        for friend in perm:
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
                met_count += 1
        
        if met_count > max_met:
            max_met = met_count
            best_schedule = schedule
    
    return best_schedule

best_schedule = find_best_schedule()
output = {
    "itinerary": best_schedule
}
print(json.dumps(output, indent=2))