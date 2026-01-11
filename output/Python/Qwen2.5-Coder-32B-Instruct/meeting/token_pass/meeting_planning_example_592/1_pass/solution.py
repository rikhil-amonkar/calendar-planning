import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    'North Beach': {'Pacific Heights': 8, 'Chinatown': 6, 'Union Square': 7, 'Mission District': 18, 'Golden Gate Park': 22, 'Nob Hill': 7},
    'Pacific Heights': {'North Beach': 9, 'Chinatown': 11, 'Union Square': 12, 'Mission District': 15, 'Golden Gate Park': 15, 'Nob Hill': 8},
    'Chinatown': {'North Beach': 3, 'Pacific Heights': 10, 'Union Square': 7, 'Mission District': 18, 'Golden Gate Park': 23, 'Nob Hill': 8},
    'Union Square': {'North Beach': 10, 'Pacific Heights': 15, 'Chinatown': 7, 'Mission District': 14, 'Golden Gate Park': 22, 'Nob Hill': 9},
    'Mission District': {'North Beach': 17, 'Pacific Heights': 16, 'Chinatown': 16, 'Union Square': 15, 'Golden Gate Park': 17, 'Nob Hill': 12},
    'Golden Gate Park': {'North Beach': 24, 'Pacific Heights': 16, 'Chinatown': 23, 'Union Square': 22, 'Mission District': 17, 'Nob Hill': 20},
    'Nob Hill': {'North Beach': 8, 'Pacific Heights': 8, 'Chinatown': 6, 'Union Square': 7, 'Mission District': 13, 'Golden Gate Park': 17}
}

# Define friends' availability
friends = [
    {'name': 'James', 'location': 'Pacific Heights', 'start': '20:00', 'end': '22:00', 'duration': 120},
    {'name': 'Robert', 'location': 'Chinatown', 'start': '12:15', 'end': '16:45', 'duration': 90},
    {'name': 'Jeffrey', 'location': 'Union Square', 'start': '09:30', 'end': '15:30', 'duration': 120},
    {'name': 'Carol', 'location': 'Mission District', 'start': '18:15', 'end': '21:15', 'duration': 15},
    {'name': 'Mark', 'location': 'Golden Gate Park', 'start': '11:30', 'end': '17:45', 'duration': 15},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start': '08:00', 'end': '15:30', 'duration': 15}
]

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def add_minutes_to_time(time, minutes):
    return (time + timedelta(minutes=minutes)).strftime('%H:%M')

def is_available(start, end, meeting_start, meeting_duration):
    meeting_end = add_minutes_to_time(meeting_start, meeting_duration)
    return start <= meeting_start and meeting_end <= end

def find_schedule(friends, travel_times):
    itinerary = []
    current_time = '09:00'
    current_location = 'North Beach'
    
    # Sort friends by start time to try scheduling them in order of availability
    friends.sort(key=lambda x: parse_time(x['start']))
    
    for friend in friends:
        friend_start = friend['start']
        friend_end = friend['end']
        friend_location = friend['location']
        friend_duration = friend['duration']
        friend_name = friend['name']
        
        # Calculate travel time to the friend's location
        travel_time = travel_times[current_location][friend_location]
        potential_start = add_minutes_to_time(current_time, travel_time)
        
        # Check if we can meet the friend within their availability
        if is_available(friend_start, friend_end, potential_start, friend_duration):
            itinerary.append({
                'action': 'meet',
                'location': friend_location,
                'person': friend_name,
                'start_time': potential_start,
                'end_time': add_minutes_to_time(potential_start, friend_duration)
            })
            current_time = add_minutes_to_time(potential_start, friend_duration)
            current_location = friend_location
    
    return itinerary

# Generate the schedule
schedule = find_schedule(friends, travel_times)

# Output the result as JSON
output = {
    "itinerary": schedule
}

print(json.dumps(output, indent=2))