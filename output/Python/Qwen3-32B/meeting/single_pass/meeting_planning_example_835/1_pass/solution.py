import itertools
import json

# Define friends with their details
friends = [
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'available_start': 9 * 60 + 30,  # 570
        'available_end': 12 * 60 + 15,    # 735
        'required_duration': 45
    },
    {
        'name': 'Steven',
        'location': 'The Castro',
        'available_start': 20 * 60 + 15,  # 1215
        'available_end': 22 * 60 + 0,     # 1320
        'required_duration': 105
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'available_start': 8 * 60 + 30,   # 510
        'available_end': 12 * 60 + 0,     # 720
        'required_duration': 30
    },
    {
        'name': 'Matthew',
        'location': 'Marina District',
        'available_start': 9 * 60 + 15,   # 555
        'available_end': 14 * 60 + 15,    # 855
        'required_duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'available_start': 14 * 60 + 15,  # 855
        'available_end': 18 * 60 + 45,    # 1125
        'required_duration': 120
    },
    {
        'name': 'Ronald',
        'location': 'Sunset District',
        'available_start': 16 * 60 + 0,   # 960
        'available_end': 20 * 60 + 45,    # 1245
        'required_duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'available_start': 18 * 60 + 30,  # 1110
        'available_end': 21 * 60 + 15,    # 1275
        'required_duration': 120
    },
    {
        'name': 'Rebecca',
        'location': 'Financial District',
        'available_start': 14 * 60 + 45,  # 885
        'available_end': 16 * 60 + 15,    # 975
        'required_duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': 18 * 60 + 30,  # 1110
        'available_end': 21 * 60 + 0,     # 1260
        'required_duration': 120
    }
]

# Define travel times between locations
travel_times = {
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15,
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17,
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7,
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13,
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20,
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14,
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25,
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10,
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 15,
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15,
    },
}

best_itinerary = None
best_length = 0

# Try permutations from largest to smallest
for k in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, k):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Pacific Heights'
        itinerary = []
        valid = True
        
        for friend in perm:
            # Calculate travel time to friend's location
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Determine meeting start and end times
            friend_start = friend['available_start']
            friend_end = friend['available_end']
            required = friend['required_duration']
            
            start = max(arrival_time, friend_start)
            end = start + required
            
            if end > friend_end:
                valid = False
                break
            
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': f"{start//60}:{start%60:02d}",
                'end_time': f"{end//60}:{end%60:02d}"
            })
            
            # Update current time and location
            current_time = end
            current_location = friend['location']
        
        if valid:
            if k > best_length:
                best_length = k
                best_itinerary = itinerary
            elif k == best_length:
                # For simplicity, we'll just keep the first valid one found for this k
                pass
    if best_length >= k:
        break  # No need to check smaller k if we've found the maximum

# Output the result as JSON
result = {
    "itinerary": best_itinerary or []
}
print(json.dumps(result, indent=2))