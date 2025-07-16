import json
from itertools import permutations

# Travel times in minutes
travel_times = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Bayview': 18,
        'Pacific Heights': 12,
        'Russian Hill': 17,
        'Fisherman\'s Wharf': 23
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Bayview': 15,
        'Pacific Heights': 16,
        'Russian Hill': 15,
        'Fisherman\'s Wharf': 22
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Pacific Heights': 23,
        'Russian Hill': 23,
        'Fisherman\'s Wharf': 25
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Bayview': 22,
        'Russian Hill': 7,
        'Fisherman\'s Wharf': 13
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Bayview': 23,
        'Pacific Heights': 7,
        'Fisherman\'s Wharf': 7
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Russian Hill': 7
    }
}

# Friend constraints
friends = {
    'Stephanie': {
        'location': 'Mission District',
        'available_start': (8, 15),
        'available_end': (13, 45),
        'min_duration': 90
    },
    'Sandra': {
        'location': 'Bayview',
        'available_start': (13, 0),
        'available_end': (19, 30),
        'min_duration': 15
    },
    'Richard': {
        'location': 'Pacific Heights',
        'available_start': (7, 15),
        'available_end': (10, 15),
        'min_duration': 75
    },
    'Brian': {
        'location': 'Russian Hill',
        'available_start': (12, 15),
        'available_end': (16, 0),
        'min_duration': 120
    },
    'Jason': {
        'location': 'Fisherman\'s Wharf',
        'available_start': (8, 30),
        'available_end': (17, 45),
        'min_duration': 60
    }
}

def time_to_minutes(time_tuple):
    return time_tuple[0] * 60 + time_tuple[1]

def minutes_to_time(minutes):
    return (minutes // 60, minutes % 60)

def format_time(time_tuple):
    return f"{time_tuple[0]}:{time_tuple[1]:02d}"

def is_valid_schedule(schedule):
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes((9, 0))
    
    for entry in schedule:
        person = entry['person']
        friend = friends[person]
        location = friend['location']
        
        # Travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Check if arrival is within friend's availability
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        if arrival_time > available_end:
            return False
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + friend['min_duration']
        
        if end_time > available_end:
            return False
        
        current_time = end_time
        current_location = location
    
    return True

def calculate_schedule(schedule_order):
    itinerary = []
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes((9, 0))
    
    for person in schedule_order:
        friend = friends[person]
        location = friend['location']
        
        # Travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Calculate meeting time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + friend['min_duration']
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': format_time(minutes_to_time(start_time)),
            'end_time': format_time(minutes_to_time(end_time))
        })
        
        current_time = end_time
        current_location = location
    
    return itinerary

def main():
    best_schedule = None
    max_meetings = 0
    
    # Try all possible permutations of friends
    for perm in permutations(friends.keys()):
        if is_valid_schedule([{'person': p} for p in perm]):
            num_meetings = len(perm)
            if num_meetings > max_meetings:
                max_meetings = num_meetings
                best_schedule = perm
    
    if best_schedule is None:
        # Try subsets if full permutation fails
        for size in range(len(friends), 0, -1):
            for perm in permutations(friends.keys(), size):
                if is_valid_schedule([{'person': p} for p in perm]):
                    best_schedule = perm
                    break
            if best_schedule is not None:
                break
    
    if best_schedule:
        itinerary = calculate_schedule(best_schedule)
        result = {'itinerary': itinerary}
    else:
        result = {'itinerary': []}
    
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()