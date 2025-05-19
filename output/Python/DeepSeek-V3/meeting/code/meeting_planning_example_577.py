import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Fisherman\'s Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Alamo Square': 5,
        'Pacific Heights': 12
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Nob Hill': 5,
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Pacific Heights': 7
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Alamo Square': 20,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'Fisherman\'s Wharf': 11,
        'Golden Gate Park': 17,
        'Alamo Square': 11,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Russian Hill': 19,
        'Fisherman\'s Wharf': 24,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'Pacific Heights': 16
    },
    'Alamo Square': {
        'Haight-Ashbury': 5,
        'Russian Hill': 13,
        'Fisherman\'s Wharf': 19,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Russian Hill': 7,
        'Fisherman\'s Wharf': 13,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Alamo Square': 10
    }
}

# Friend constraints
friends = [
    {
        'name': 'Stephanie',
        'location': 'Russian Hill',
        'available_start': '20:00',
        'available_end': '20:45',
        'min_duration': 15
    },
    {
        'name': 'Kevin',
        'location': 'Fisherman\'s Wharf',
        'available_start': '19:15',
        'available_end': '21:45',
        'min_duration': 75
    },
    {
        'name': 'Robert',
        'location': 'Nob Hill',
        'available_start': '7:45',
        'available_end': '10:30',
        'min_duration': 90
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'available_start': '8:30',
        'available_end': '17:00',
        'min_duration': 75
    },
    {
        'name': 'Anthony',
        'location': 'Alamo Square',
        'available_start': '7:45',
        'available_end': '19:45',
        'min_duration': 15
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': '14:45',
        'available_end': '21:45',
        'min_duration': 45
    }
]

def calculate_schedule():
    current_time = time_to_minutes('9:00')
    current_location = 'Haight-Ashbury'
    itinerary = []
    met_friends = set()

    # First, meet Robert (only available in the morning)
    robert = next(f for f in friends if f['name'] == 'Robert')
    travel_time = travel_times[current_location][robert['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(robert['available_start'])
    available_end = time_to_minutes(robert['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + robert['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': robert['location'],
            'person': robert['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = robert['location']
        met_friends.add(robert['name'])

    # Next, meet Steven (available all day)
    steven = next(f for f in friends if f['name'] == 'Steven')
    travel_time = travel_times[current_location][steven['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(steven['available_start'])
    available_end = time_to_minutes(steven['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + steven['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': steven['location'],
            'person': steven['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = steven['location']
        met_friends.add(steven['name'])

    # Next, meet Anthony (available all day)
    anthony = next(f for f in friends if f['name'] == 'Anthony')
    travel_time = travel_times[current_location][anthony['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(anthony['available_start'])
    available_end = time_to_minutes(anthony['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + anthony['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': anthony['location'],
            'person': anthony['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = anthony['location']
        met_friends.add(anthony['name'])

    # Next, meet Sandra (afternoon/evening)
    sandra = next(f for f in friends if f['name'] == 'Sandra')
    travel_time = travel_times[current_location][sandra['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(sandra['available_start'])
    available_end = time_to_minutes(sandra['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + sandra['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': sandra['location'],
            'person': sandra['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = sandra['location']
        met_friends.add(sandra['name'])

    # Next, meet Kevin (evening)
    kevin = next(f for f in friends if f['name'] == 'Kevin')
    travel_time = travel_times[current_location][kevin['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(kevin['available_start'])
    available_end = time_to_minutes(kevin['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + kevin['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': kevin['location'],
            'person': kevin['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = kevin['location']
        met_friends.add(kevin['name'])

    # Finally, meet Stephanie (evening)
    stephanie = next(f for f in friends if f['name'] == 'Stephanie')
    travel_time = travel_times[current_location][stephanie['location']]
    arrival_time = current_time + travel_time
    available_start = time_to_minutes(stephanie['available_start'])
    available_end = time_to_minutes(stephanie['available_end'])
    
    start_time = max(arrival_time, available_start)
    end_time = start_time + stephanie['min_duration']
    
    if end_time <= available_end:
        itinerary.append({
            'action': 'meet',
            'location': stephanie['location'],
            'person': stephanie['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        met_friends.add(stephanie['name'])

    return {'itinerary': itinerary}

schedule = calculate_schedule()
print(json.dumps(schedule, indent=2))