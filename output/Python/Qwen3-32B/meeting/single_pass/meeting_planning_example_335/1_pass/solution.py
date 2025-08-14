import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

travel_times = {
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Mission District'): 15,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Mission District'): 18,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Mission District'): 17,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Mission District'): 10,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Alamo Square'): 11,
}

friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': '9:00',
        'available_end': '17:00',
        'required_duration': 15
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'available_start': '10:45',
        'available_end': '14:45',
        'required_duration': 45
    },
    {
        'name': 'Amanda',
        'location': 'Alamo Square',
        'available_start': '19:45',
        'available_end': '21:00',
        'required_duration': 60
    },
    {
        'name': 'Betty',
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'required_duration': 90
    }
]

best_itinerary = []
best_length = 0

for r in range(4, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Pacific Heights'
        itinerary = []
        valid = True
        
        for friend in perm:
            # Calculate travel time
            from_loc = current_location
            to_loc = friend['location']
            travel_time = travel_times.get((from_loc, to_loc))
            if travel_time is None:
                valid = False
                break
            current_time += travel_time
            
            # Check if friend can be met
            available_start = time_str_to_minutes(friend['available_start'])
            available_end = time_str_to_minutes(friend['available_end'])
            required = friend['required_duration']
            
            latest_start = available_end - required
            earliest_start = max(current_time, available_start)
            
            if earliest_start > latest_start:
                valid = False
                break
            
            # Schedule the meeting
            start_time = earliest_start
            end_time = start_time + required
            
            itinerary.append({
                'action': 'meet',
                'location': to_loc,
                'person': friend['name'],
                'start_time': minutes_to_time_str(start_time),
                'end_time': minutes_to_time_str(end_time)
            })
            
            # Update current time and location
            current_time = end_time
            current_location = to_loc
        
        if valid:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == best_length:
                # Tie-breaker: earliest end time?
                # For simplicity, just keep the first one found
                pass

# Output the best itinerary as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))