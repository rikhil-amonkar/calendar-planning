import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Input parameters
travel_times = {
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Presidio'): 31,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Union Square'): 22,
}

friends = [
    {
        'name': 'Richard',
        'location': 'Union Square',
        'available_start': '8:45',
        'available_end': '13:00',
        'required_duration': 120,
    },
    {
        'name': 'Charles',
        'location': 'Presidio',
        'available_start': '9:45',
        'available_end': '13:00',
        'required_duration': 120,
    },
]

start_location = 'Bayview'
start_time_minutes = time_to_minutes('9:00')

best_itinerary = []
max_friends = 0

for perm in itertools.permutations(friends):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    friends_met = 0
    
    for friend in perm:
        # Calculate travel time
        travel_key = (current_location, friend['location'])
        travel_time = travel_times.get(travel_key, float('inf'))
        arrival_time = current_time + travel_time
        
        # Friend's available times
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        required = friend['required_duration']
        
        # Determine possible start time
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        
        if earliest_start > latest_start:
            # Cannot meet this friend, break
            break
        
        # Schedule the meeting at earliest possible
        start = earliest_start
        end = start + required
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
        })
        friends_met += 1
        current_time = end
        current_location = friend['location']
    
    # Check if this itinerary is better
    if friends_met > max_friends:
        max_friends = friends_met
        best_itinerary = itinerary
    elif friends_met == max_friends and len(itinerary) > 0:
        # In case of tie, keep the first one found
        pass

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))