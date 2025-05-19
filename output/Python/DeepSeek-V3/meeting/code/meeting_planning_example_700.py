import json
from itertools import permutations

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
friends = {
    'Kevin': {
        'location': 'Pacific Heights',
        'available_start': '7:15',
        'available_end': '8:45',
        'min_duration': 90,
        'met': False
    },
    'Michelle': {
        'location': 'Golden Gate Park',
        'available_start': '20:00',
        'available_end': '21:00',
        'min_duration': 15,
        'met': False
    },
    'Emily': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '16:15',
        'available_end': '19:00',
        'min_duration': 30,
        'met': False
    },
    'Mark': {
        'location': 'Marina District',
        'available_start': '18:15',
        'available_end': '19:45',
        'min_duration': 75,
        'met': False
    },
    'Barbara': {
        'location': 'Alamo Square',
        'available_start': '17:00',
        'available_end': '19:00',
        'min_duration': 120,
        'met': False
    },
    'Laura': {
        'location': 'Sunset District',
        'available_start': '19:00',
        'available_end': '21:15',
        'min_duration': 75,
        'met': False
    },
    'Mary': {
        'location': 'Nob Hill',
        'available_start': '17:30',
        'available_end': '19:00',
        'min_duration': 45,
        'met': False
    },
    'Helen': {
        'location': 'North Beach',
        'available_start': '11:00',
        'available_end': '12:15',
        'min_duration': 45,
        'met': False
    }
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(friend, current_time, current_location):
    loc = friend['location']
    travel_time = travel_times[current_location][loc]
    arrival_time = current_time + travel_time
    
    available_start = time_to_minutes(friend['available_start'])
    available_end = time_to_minutes(friend['available_end'])
    min_duration = friend['min_duration']
    
    if arrival_time > available_end:
        return False
    
    start_time = max(arrival_time, available_start)
    end_time = min(start_time + min_duration, available_end)
    
    if end_time - start_time >= min_duration:
        return (start_time, end_time)
    return False

def find_best_schedule():
    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    itinerary = []
    remaining_friends = {name: data for name, data in friends.items() if not data['met']}
    
    # Try to meet Helen first (only available in morning)
    if 'Helen' in remaining_friends:
        helen = remaining_friends['Helen']
        meeting = can_meet(helen, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': helen['location'],
                'person': 'Helen',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = helen['location']
            del remaining_friends['Helen']
    
    # Try to meet Barbara first in the afternoon (longest duration)
    if 'Barbara' in remaining_friends:
        barbara = remaining_friends['Barbara']
        meeting = can_meet(barbara, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': barbara['location'],
                'person': 'Barbara',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = barbara['location']
            del remaining_friends['Barbara']
    
    # Try to meet Mary (short duration, same time as Barbara)
    if 'Mary' in remaining_friends:
        mary = remaining_friends['Mary']
        meeting = can_meet(mary, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': mary['location'],
                'person': 'Mary',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = mary['location']
            del remaining_friends['Mary']
    
    # Try to meet Emily
    if 'Emily' in remaining_friends:
        emily = remaining_friends['Emily']
        meeting = can_meet(emily, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': emily['location'],
                'person': 'Emily',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = emily['location']
            del remaining_friends['Emily']
    
    # Try to meet Mark
    if 'Mark' in remaining_friends:
        mark = remaining_friends['Mark']
        meeting = can_meet(mark, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': mark['location'],
                'person': 'Mark',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = mark['location']
            del remaining_friends['Mark']
    
    # Try to meet Laura
    if 'Laura' in remaining_friends:
        laura = remaining_friends['Laura']
        meeting = can_meet(laura, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': laura['location'],
                'person': 'Laura',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = laura['location']
            del remaining_friends['Laura']
    
    # Try to meet Michelle last
    if 'Michelle' in remaining_friends:
        michelle = remaining_friends['Michelle']
        meeting = can_meet(michelle, current_time, current_location)
        if meeting:
            start, end = meeting
            itinerary.append({
                'action': 'meet',
                'location': michelle['location'],
                'person': 'Michelle',
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
            current_time = end
            current_location = michelle['location']
            del remaining_friends['Michelle']
    
    return {'itinerary': itinerary}

# Calculate and output the schedule
schedule = find_best_schedule()
print(json.dumps(schedule, indent=2))