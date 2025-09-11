import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Travel times between locations (in minutes)
travel_times = {
    'Bayview': {
        'Russian Hill': 23,
        'Alamo Square': 16,
        'North Beach': 21,
        'Financial District': 19
    },
    'Russian Hill': {
        'Bayview': 23,
        'Alamo Square': 15,
        'North Beach': 5,
        'Financial District': 11
    },
    'Alamo Square': {
        'Bayview': 16,
        'Russian Hill': 13,
        'North Beach': 15,
        'Financial District': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Russian Hill': 4,
        'Alamo Square': 16,
        'Financial District': 8
    },
    'Financial District': {
        'Bayview': 19,
        'Russian Hill': 10,
        'Alamo Square': 17,
        'North Beach': 7
    }
}

# Friends' constraints
friends = [
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start_min': 510,  # 8:30 AM
        'available_end_min': 1155,   # 7:15 PM
        'min_duration': 60
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'available_start_min': 660,  # 11:00 AM
        'available_end_min': 960,    # 4:00 PM
        'min_duration': 90
    },
    {
        'name': 'Jason',
        'location': 'North Beach',
        'available_start_min': 1005, # 4:45 PM
        'available_end_min': 1305,   # 9:45 PM
        'min_duration': 15
    },
    {
        'name': 'Jeffrey',
        'location': 'Financial District',
        'available_start_min': 630,  # 10:30 AM
        'available_end_min': 945,    # 3:45 PM
        'min_duration': 45
    }
]

best_itinerary = []
max_friends = 0

# Check all permutations of friends with different lengths
for r in range(1, 5):  # lengths from 1 to 4
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # Start at 9:00 AM (540 min)
        current_location = 'Bayview'
        valid = True
        itinerary = []
        
        for friend in perm:
            # Get friend's location
            friend_location = friend['location']
            
            # Calculate travel time
            travel_time = travel_times[current_location][friend_location]
            arrival_time = current_time + travel_time
            
            # Friend's available time and min duration
            friend_start = friend['available_start_min']
            friend_end = friend['available_end_min']
            min_duration = friend['min_duration']
            
            # Determine possible meeting start and end
            meeting_start = max(arrival_time, friend_start)
            meeting_end = meeting_start + min_duration
            
            # Check if meeting is possible
            if meeting_end > friend_end:
                valid = False
                break
            
            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend_location,
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            
            # Update current time and location
            current_time = meeting_end
            current_location = friend_location
        
        # If this permutation is valid, check if it's better
        if valid:
            if len(itinerary) > max_friends:
                max_friends = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == max_friends and max_friends > 0:
                # In case of tie, check which itinerary ends earlier
                current_best_end = best_itinerary[-1]['end_time']
                this_end = itinerary[-1]['end_time']
                # Convert to minutes for comparison
                current_best_end_min = time_to_minutes(current_best_end)
                this_end_min = time_to_minutes(this_end)
                if this_end_min < current_best_end_min:
                    best_itinerary = itinerary

# Output the best itinerary as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))