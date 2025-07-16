import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Travel times dictionary (from -> to -> minutes)
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

# Friend constraints
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

def can_meet_friend(current_time, friend, current_location):
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    min_duration = friend['min_duration']
    
    if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
        return False
    
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    
    if arrival_time > available_end:
        return False
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + min_duration
    
    if end_time > available_end:
        return False
    
    return {
        'start_time': start_time,
        'end_time': end_time,
        'travel_time': travel_time
    }

def find_best_schedule():
    best_schedule = []
    max_met = 0
    
    # Start with Kevin at 7:15 (must meet first)
    kevin = next(f for f in friends if f['name'] == 'Kevin')
    kevin_meeting = {
        'start_time': time_to_minutes('7:15'),
        'end_time': time_to_minutes('7:15') + kevin['min_duration'],
        'travel_time': travel_times['Presidio'][kevin['location']]
    }
    initial_schedule = [{
        'action': 'meet',
        'location': kevin['location'],
        'person': kevin['name'],
        'start_time': minutes_to_time(kevin_meeting['start_time']),
        'end_time': minutes_to_time(kevin_meeting['end_time'])
    }]
    current_time = kevin_meeting['end_time']
    current_location = kevin['location']
    
    # Try to meet Helen next (only available in the morning)
    helen = next(f for f in friends if f['name'] == 'Helen')
    helen_meeting = can_meet_friend(current_time, helen, current_location)
    if helen_meeting:
        initial_schedule.append({
            'action': 'meet',
            'location': helen['location'],
            'person': helen['name'],
            'start_time': minutes_to_time(helen_meeting['start_time']),
            'end_time': minutes_to_time(helen_meeting['end_time'])
        })
        current_time = helen_meeting['end_time']
        current_location = helen['location']
    
    # Now try permutations of the remaining friends (excluding Michelle who will be last)
    other_friends = [f for f in friends if f['name'] not in ['Kevin', 'Michelle', 'Helen']]
    
    # We'll prioritize friends with tighter time windows first
    priority_order = sorted(other_friends, key=lambda x: (
        time_to_minutes(x['available_end']) - time_to_minutes(x['available_start']),
        x['min_duration']
    ))
    
    for friend in priority_order:
        meeting = can_meet_friend(current_time, friend, current_location)
        if meeting:
            initial_schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting['start_time']),
                'end_time': minutes_to_time(meeting['end_time'])
            })
            current_time = meeting['end_time']
            current_location = friend['location']
    
    # Try to meet Michelle last if possible
    michelle = next(f for f in friends if f['name'] == 'Michelle')
    michelle_meeting = can_meet_friend(current_time, michelle, current_location)
    if michelle_meeting:
        initial_schedule.append({
            'action': 'meet',
            'location': michelle['location'],
            'person': michelle['name'],
            'start_time': minutes_to_time(michelle_meeting['start_time']),
            'end_time': minutes_to_time(michelle_meeting['end_time'])
        })
    
    return initial_schedule

best_schedule = find_best_schedule()
output = {
    "itinerary": best_schedule
}
print(json.dumps(output, indent=2))