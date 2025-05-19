def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary
travel_times = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4
}

# Friends data
friends = [
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'start': '13:15',
        'end': '14:30',
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Russian Hill',
        'start': '19:30',
        'end': '21:15',
        'duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start': '8:15',
        'end': '13:30',
        'duration': 105
    }
]

current_time = time_to_minutes('9:00')  # Starting at 9:00 AM
current_location = 'Sunset District'
itinerary = []
remaining_friends = friends.copy()

while remaining_friends:
    best_friend = None
    best_end = float('inf')
    
    for friend in remaining_friends:
        # Calculate travel time from current location to friend's location
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            continue  # No known travel time, skip
        
        arrival = current_time + travel_time
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        # Calculate meeting start and end times
        meeting_start = max(arrival, friend_start)
        meeting_end = meeting_start + friend['duration']
        
        # Check if the meeting can fit within the friend's available time
        if meeting_end > friend_end:
            continue
        
        # Update best friend if this meeting ends earlier
        if meeting_end < best_end:
            best_end = meeting_end
            best_friend = friend
    
    if best_friend is not None:
        # Calculate start and end times for the itinerary
        travel = travel_times[(current_location, best_friend['location'])]
        arrival = current_time + travel
        meeting_start = max(arrival, time_to_minutes(best_friend['start']))
        meeting_end = meeting_start + best_friend['duration']
        
        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        
        itinerary.append({
            'action': 'meet',
            'location': best_friend['location'],
            'person': best_friend['name'],
            'start_time': start_time,
            'end_time': end_time
        })
        
        current_time = meeting_end
        current_location = best_friend['location']
        remaining_friends.remove(best_friend)
    else:
        break  # No more friends can be scheduled

# Output the result
print('SOLUTION:')
print({
    "itinerary": itinerary
})