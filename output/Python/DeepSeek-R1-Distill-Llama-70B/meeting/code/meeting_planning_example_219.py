from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('Castro', 'Alamo Square'): 8,
    ('Castro', 'Union Square'): 19,
    ('Castro', 'Chinatown'): 20,
    ('Alamo Square', 'Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'start': '11:45',
        'end': '15:15',
        'duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'start': '16:45',
        'end': '18:15',
        'duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'start': '17:15',
        'end': '19:00',
        'duration': 105
    }
]

best_itinerary = []

for num_friends in range(3, 0, -1):
    for perm in permutations(friends, num_friends):
        current_time = 540  # 9:00 AM
        current_location = 'Castro'
        itinerary = []
        valid = True
        for friend in perm:
            # Calculate travel time
            travel = travel_times.get((current_location, friend['location']), None)
            if travel is None:
                valid = False
                break
            current_time += travel
            # Convert friend's times to minutes
            friend_start = time_to_minutes(friend['start'])
            friend_end = time_to_minutes(friend['end'])
            # Calculate earliest possible start time
            earliest_start = max(current_time, friend_start)
            # Calculate latest possible start time
            latest_start = friend_end - friend['duration']
            if earliest_start > latest_start:
                valid = False
                break
            # Schedule the meeting
            meeting_start = earliest_start
            meeting_end = meeting_start + friend['duration']
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            # Update current time and location
            current_time = meeting_end
            current_location = friend['location']
        if valid:
            if len(itinerary) > len(best_itinerary):
                best_itinerary = itinerary
            elif len(itinerary) == len(best_itinerary):
                # If same number, choose the one with earlier end time
                # Compare the end time of the last meeting
                if current_time < time_to_minutes(best_itinerary[-1]['end_time']):
                    best_itinerary = itinerary
            break  # Found a valid schedule with max possible friends

print('SOLUTION:')
print(json.dumps({'itinerary': best_itinerary}))