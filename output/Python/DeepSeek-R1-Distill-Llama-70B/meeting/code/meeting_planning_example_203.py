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
    ('Financial District', 'Fishermans Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fishermans Wharf', 'Financial District'): 11,
    ('Fishermans Wharf', 'Pacific Heights'): 12,
    ('Fishermans Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fishermans Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fishermans Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

friends = [
    {
        'name': 'David',
        'location': 'Fishermans Wharf',
        'start': '10:45',
        'end': '15:30',
        'duration': 15
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start': '9:00',
        'end': '15:30',
        'duration': 75
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'start': '12:15',
        'end': '19:45',
        'duration': 90
    }
]

best_itinerary = []

for num_friends in range(3, 0, -1):
    for perm in permutations(friends, num_friends):
        current_time = 540  # 9:00 AM
        current_location = 'Financial District'
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