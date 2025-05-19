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
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Financial District'): 21,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Haight-Ashbury'): 18,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Financial District'): 8,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'North Beach'): 19,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Financial District'): 22,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Financial District'): 9,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Financial District'): 17,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Union Square'): 24,
    ('Presidio', 'Financial District'): 23,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Financial District'): 9,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
}

friends = [
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start': '17:30',
        'end': '20:30',
        'duration': 15
    },
    {
        'name': 'Sarah',
        'location': 'Golden Gate Park',
        'start': '17:00',
        'end': '19:15',
        'duration': 75
    },
    {
        'name': 'Brian',
        'location': 'Embarcadero',
        'start': '14:15',
        'end': '16:00',
        'duration': 105
    },
    {
        'name': 'Stephanie',
        'location': 'Haight-Ashbury',
        'start': '10:15',
        'end': '12:15',
        'duration': 75
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start': '14:00',
        'end': '19:30',
        'duration': 30
    },
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'start': '8:15',
        'end': '12:45',
        'duration': 90
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'start': '11:15',
        'end': '13:15',
        'duration': 120
    },
    {
        'name': 'James',
        'location': 'Presidio',
        'start': '15:00',
        'end': '18:15',
        'duration': 120
    },
    {
        'name': 'Elizabeth',
        'location': 'Union Square',
        'start': '11:30',
        'end': '21:00',
        'duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Financial District',
        'start': '13:15',
        'end': '15:15',
        'duration': 45
    }
]

best_itinerary = []

for num_friends in range(9, 0, -1):
    for perm in permutations(friends, num_friends):
        current_time = 540  # 9:00 AM
        current_location = 'The Castro'
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