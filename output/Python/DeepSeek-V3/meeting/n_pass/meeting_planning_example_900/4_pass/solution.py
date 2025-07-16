import json
from itertools import permutations, combinations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Input data
travel_times = {
    'Richmond District': {
        'The Castro': 16, 'Nob Hill': 17, 'Marina District': 9, 'Pacific Heights': 10,
        'Haight-Ashbury': 10, 'Mission District': 20, 'Chinatown': 20, 'Russian Hill': 13,
        'Alamo Square': 13, 'Bayview': 27
    },
    'The Castro': {
        'Richmond District': 16, 'Nob Hill': 12, 'Marina District': 20, 'Pacific Heights': 14,
        'Haight-Ashbury': 6, 'Mission District': 8, 'Chinatown': 14, 'Russian Hill': 12,
        'Alamo Square': 10, 'Bayview': 18
    },
    'Nob Hill': {
        'Richmond District': 17, 'The Castro': 12, 'Marina District': 10, 'Pacific Heights': 5,
        'Haight-Ashbury': 10, 'Mission District': 15, 'Chinatown': 5, 'Russian Hill': 5,
        'Alamo Square': 10, 'Bayview': 22
    },
    'Marina District': {
        'Richmond District': 9, 'The Castro': 20, 'Nob Hill': 10, 'Pacific Heights': 5,
        'Haight-Ashbury': 15, 'Mission District': 22, 'Chinatown': 15, 'Russian Hill': 8,
        'Alamo Square': 15, 'Bayview': 30
    },
    'Pacific Heights': {
        'Richmond District': 10, 'The Castro': 14, 'Nob Hill': 5, 'Marina District': 5,
        'Haight-Ashbury': 10, 'Mission District': 17, 'Chinatown': 10, 'Russian Hill': 5,
        'Alamo Square': 10, 'Bayview': 25
    },
    'Haight-Ashbury': {
        'Richmond District': 10, 'The Castro': 6, 'Nob Hill': 10, 'Marina District': 15,
        'Pacific Heights': 10, 'Mission District': 12, 'Chinatown': 12, 'Russian Hill': 10,
        'Alamo Square': 8, 'Bayview': 20
    },
    'Mission District': {
        'Richmond District': 20, 'The Castro': 8, 'Nob Hill': 15, 'Marina District': 22,
        'Pacific Heights': 17, 'Haight-Ashbury': 12, 'Chinatown': 12, 'Russian Hill': 15,
        'Alamo Square': 10, 'Bayview': 15
    },
    'Chinatown': {
        'Richmond District': 20, 'The Castro': 14, 'Nob Hill': 5, 'Marina District': 15,
        'Pacific Heights': 10, 'Haight-Ashbury': 12, 'Mission District': 12, 'Russian Hill': 5,
        'Alamo Square': 12, 'Bayview': 22
    },
    'Russian Hill': {
        'Richmond District': 13, 'The Castro': 12, 'Nob Hill': 5, 'Marina District': 8,
        'Pacific Heights': 5, 'Haight-Ashbury': 10, 'Mission District': 15, 'Chinatown': 5,
        'Alamo Square': 10, 'Bayview': 25
    },
    'Alamo Square': {
        'Richmond District': 13, 'The Castro': 10, 'Nob Hill': 10, 'Marina District': 15,
        'Pacific Heights': 10, 'Haight-Ashbury': 8, 'Mission District': 10, 'Chinatown': 12,
        'Russian Hill': 10, 'Bayview': 20
    },
    'Bayview': {
        'Richmond District': 27, 'The Castro': 18, 'Nob Hill': 22, 'Marina District': 30,
        'Pacific Heights': 25, 'Haight-Ashbury': 20, 'Mission District': 15, 'Chinatown': 22,
        'Russian Hill': 25, 'Alamo Square': 20
    }
}

friends = [
    {'name': 'William', 'location': 'The Castro', 'start': '10:00', 'end': '12:00', 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': '10:30', 'end': '12:00', 'duration': 45},
    {'name': 'James', 'location': 'Russian Hill', 'start': '11:00', 'end': '12:30', 'duration': 30},
    {'name': 'Emma', 'location': 'Mission District', 'start': '9:30', 'end': '11:30', 'duration': 30},
    {'name': 'Olivia', 'location': 'Pacific Heights', 'start': '11:00', 'end': '13:00', 'duration': 30},
    {'name': 'Liam', 'location': 'Marina District', 'start': '11:30', 'end': '13:30', 'duration': 45},
    {'name': 'Ava', 'location': 'Chinatown', 'start': '10:00', 'end': '12:30', 'duration': 30}
]

current_location = 'Richmond District'
current_time = time_to_minutes('9:00')

def calculate_schedule(schedule):
    loc = current_location
    time = current_time
    itinerary = []
    for meet in schedule:
        travel_time = travel_times[loc][meet['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, time_to_minutes(meet['start']))
        end_time = start_time + meet['duration']
        if end_time > time_to_minutes(meet['end']):
            return None
        itinerary.append({
            'action': 'meet',
            'location': meet['location'],
            'person': meet['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        loc = meet['location']
        time = end_time
    return itinerary

def generate_best_schedule():
    mandatory = [f for f in friends if f['name'] in ['William', 'Elizabeth', 'James']]
    optional = [f for f in friends if f['name'] not in ['William', 'Elizabeth', 'James']]
    
    best_itinerary = []
    
    # Try all permutations of mandatory friends first
    for mandatory_order in permutations(mandatory):
        itinerary = calculate_schedule(mandatory_order)
        if not itinerary:
            continue
            
        # Now try adding optional friends in all possible positions
        for num_optional in range(1, len(optional)+1):
            for opt_combo in combinations(optional, num_optional):
                for opt_order in permutations(opt_combo):
                    # Try inserting optional friends at all possible positions
                    for i in range(len(mandatory_order)+1):
                        test_schedule = list(mandatory_order)
                        for friend in opt_order:
                            test_schedule.insert(i, friend)
                            new_itinerary = calculate_schedule(test_schedule)
                            if new_itinerary and len(new_itinerary) > len(best_itinerary):
                                best_itinerary = new_itinerary
                            test_schedule.remove(friend)
        
        # Early exit if we've scheduled all friends
        if len(best_itinerary) == len(friends):
            break
    
    return best_itinerary if best_itinerary else []

best_itinerary = generate_best_schedule()

output = {'itinerary': best_itinerary}
print(json.dumps(output, indent=2))