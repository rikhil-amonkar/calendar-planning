import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times
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

# Define friends
friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': 540,  # 9:00 AM
        'available_end': 1020,   # 5:00 PM
        'min_duration': 15
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'available_start': 645,  # 10:45 AM
        'available_end': 885,    # 2:45 PM
        'min_duration': 45
    },
    {
        'name': 'Amanda',
        'location': 'Alamo Square',
        'available_start': 1185, # 7:45 PM
        'available_end': 1260,   # 9:00 PM
        'min_duration': 60
    },
    {
        'name': 'Betty',
        'location': 'Financial District',
        'available_start': 1140, # 7:00 PM
        'available_end': 1305,   # 9:45 PM
        'min_duration': 90
    }
]

best_itinerary = []
max_count = 0

# Generate all possible permutations of friends (non-empty)
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        current_time = 540  # start at 9:00 AM
        current_location = 'Pacific Heights'
        itinerary = []
        valid = True
        
        for friend in perm:
            # Get travel time
            try:
                travel_time = travel_times[(current_location, friend['location'])]
            except KeyError:
                valid = False
                break
            
            arrival_time = current_time + travel_time
            start_time = max(arrival_time, friend['available_start'])
            end_time = start_time + friend['min_duration']
            
            if end_time > friend['available_end']:
                valid = False
                break
            
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(start_time),
                'end_time': minutes_to_time_str(end_time)
            })
            
            # Update current state
            current_time = end_time
            current_location = friend['location']
        
        if valid and len(itinerary) > max_count:
            max_count = len(itinerary)
            best_itinerary = itinerary
        elif valid and len(itinerary) == max_count:
            # In case of tie, we can choose the first one found or the one that ends earliest
            # For simplicity, we'll keep the first one found
            pass

# Output the result as JSON
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))