def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary
travel_times = {
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Fishermans Wharf'): 8,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'The Castro'): 22,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fishermans Wharf'): 6,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'The Castro'): 25,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Fishermans Wharf'): 13,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'The Castro'): 16,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Fishermans Wharf'): 7,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'The Castro'): 21,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Fishermans Wharf'): 23,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Fishermans Wharf'): 24,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Fishermans Wharf', 'Chinatown'): 12,
    ('Fishermans Wharf', 'Embarcadero'): 8,
    ('Fishermans Wharf', 'Pacific Heights'): 12,
    ('Fishermans Wharf', 'Russian Hill'): 7,
    ('Fishermans Wharf', 'Haight-Ashbury'): 22,
    ('Fishermans Wharf', 'Golden Gate Park'): 25,
    ('Fishermans Wharf', 'Sunset District'): 27,
    ('Fishermans Wharf', 'The Castro'): 27,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Fishermans Wharf'): 29,
    ('Sunset District', 'The Castro'): 17,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Fishermans Wharf'): 24,
    ('The Castro', 'Sunset District'): 17
}

# Friends data
friends = [
    {
        'name': 'Richard',
        'location': 'Embarcadero',
        'start': '15:15',
        'end': '18:45',
        'duration': 90
    },
    {
        'name': 'Mark',
        'location': 'Pacific Heights',
        'start': '15:00',
        'end': '17:00',
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Russian Hill',
        'start': '17:30',
        'end': '21:00',
        'duration': 90
    },
    {
        'name': 'Rebecca',
        'location': 'Haight-Ashbury',
        'start': '14:45',
        'end': '18:00',
        'duration': 60
    },
    {
        'name': 'Melissa',
        'location': 'Golden Gate Park',
        'start': '13:45',
        'end': '17:30',
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Fishermans Wharf',
        'start': '14:45',
        'end': '20:15',
        'duration': 15
    },
    {
        'name': 'Emily',
        'location': 'Sunset District',
        'start': '15:45',
        'end': '17:00',
        'duration': 45
    },
    {
        'name': 'George',
        'location': 'The Castro',
        'start': '14:00',
        'end': '16:15',
        'duration': 75
    }
]

current_time = time_to_minutes('9:00')  # Starting at 9:00 AM
current_location = 'Chinatown'
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