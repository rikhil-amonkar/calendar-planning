import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Input data (same as before)
travel_times = {
    'Richmond District': {
        'The Castro': 16, 'Nob Hill': 17, 'Marina District': 9, 'Pacific Heights': 10,
        'Haight-Ashbury': 10, 'Mission District': 20, 'Chinatown': 20, 'Russian Hill': 13,
        'Alamo Square': 13, 'Bayview': 27
    },
    # ... (rest of travel_times remains the same)
}

friends = [
    # ... (friends list remains the same)
]

current_location = 'Richmond District'
current_time = time_to_minutes('9:00')

def is_valid_schedule(schedule):
    loc = current_location
    time = current_time
    for meet in schedule:
        travel_time = travel_times[loc][meet['location']]
        arrival_time = time + travel_time
        start_time = max(arrival_time, time_to_minutes(meet['start']))
        end_time = start_time + meet['duration']
        if end_time > time_to_minutes(meet['end']):
            return False
        loc = meet['location']
        time = end_time
    return True

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
    # Separate mandatory and optional friends
    mandatory = [f for f in friends if f['name'] in ['William', 'Elizabeth', 'James']]
    optional = [f for f in friends if f['name'] not in ['William', 'Elizabeth', 'James']]
    
    best_itinerary = []
    
    # Try different combinations of mandatory + optional friends
    for optional_count in range(len(optional), 0, -1):
        for optional_selection in permutations(optional, optional_count):
            for mandatory_perm in permutations(mandatory):
                # Try different orders of mandatory friends
                test_schedule = list(mandatory_perm) + list(optional_selection)
                itinerary = calculate_schedule(test_schedule)
                if itinerary and len(itinerary) > len(best_itinerary):
                    best_itinerary = itinerary
                    if len(best_itinerary) == len(friends):
                        return best_itinerary
                    
                # Also try interleaving mandatory and optional
                test_schedule = list(optional_selection) + list(mandatory_perm)
                itinerary = calculate_schedule(test_schedule)
                if itinerary and len(itinerary) > len(best_itinerary):
                    best_itinerary = itinerary
                    if len(best_itinerary) == len(friends):
                        return best_itinerary
    return best_itinerary

# Generate the best possible itinerary
best_itinerary = generate_best_schedule()

output = {'itinerary': best_itinerary}
print(json.dumps(output, indent=2))