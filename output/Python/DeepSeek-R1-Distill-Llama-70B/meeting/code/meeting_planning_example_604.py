from itertools import permutations
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('Fishermans Wharf', 'The Castro'): 26,
    ('Fishermans Wharf', 'Golden Gate Park'): 25,
    ('Fishermans Wharf', 'Embarcadero'): 8,
    ('Fishermans Wharf', 'Russian Hill'): 7,
    ('Fishermans Wharf', 'Nob Hill'): 11,
    ('Fishermans Wharf', 'Alamo Square'): 20,
    ('Fishermans Wharf', 'North Beach'): 6,
    ('The Castro', 'Fishermans Wharf'): 24,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'North Beach'): 20,
    ('Golden Gate Park', 'Fishermans Wharf'): 24,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Embarcadero', 'Fishermans Wharf'): 6,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'North Beach'): 5,
    ('Russian Hill', 'Fishermans Wharf'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'North Beach'): 5,
    ('Nob Hill', 'Fishermans Wharf'): 11,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Alamo Square', 'Fishermans Wharf'): 19,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'North Beach'): 16,
    ('North Beach', 'Fishermans Wharf'): 5,
    ('North Beach', 'The Castro'): 22,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Alamo Square'): 16,
}

friends = [
    {
        'name': 'Laura',
        'location': 'The Castro',
        'start': '19:45',
        'end': '21:30',
        'duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'start': '21:15',
        'end': '21:45',
        'duration': 15
    },
    {
        'name': 'William',
        'location': 'Embarcadero',
        'start': '7:00',
        'end': '9:00',
        'duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': '14:30',
        'end': '19:45',
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'start': '7:30',
        'end': '9:30',
        'duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'start': '11:30',
        'end': '12:45',
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'start': '15:45',
        'end': '19:15',
        'duration': 30
    },
]

best_itinerary = []

for num_friends in range(7, 0, -1):
    for perm in permutations(friends, num_friends):
        current_time = 540  # 9:00 AM
        current_location = 'Fishermans Wharf'
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