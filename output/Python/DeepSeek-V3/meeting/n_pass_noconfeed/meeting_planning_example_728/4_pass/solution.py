import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def can_meet(start_time, end_time, travel_time, prev_end_time, meeting_duration):
    arrival_time = prev_end_time + travel_time
    meeting_end = arrival_time + meeting_duration
    return arrival_time >= start_time and meeting_end <= end_time

def calculate_schedule():
    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Marina District': {
            'Mission District': 20,
            'Fisherman\'s Wharf': 10,
            'Presidio': 10,
            'Union Square': 16,
            'Sunset District': 19,
            'Financial District': 17,
            'Haight-Ashbury': 16,
            'Russian Hill': 8
        },
        'Mission District': {
            'Marina District': 19,
            'Fisherman\'s Wharf': 22,
            'Presidio': 25,
            'Union Square': 15,
            'Sunset District': 24,
            'Financial District': 15,
            'Haight-Ashbury': 12,
            'Russian Hill': 15
        },
        'Fisherman\'s Wharf': {
            'Marina District': 9,
            'Mission District': 22,
            'Presidio': 17,
            'Union Square': 13,
            'Sunset District': 27,
            'Financial District': 11,
            'Haight-Ashbury': 22,
            'Russian Hill': 7
        },
        'Presidio': {
            'Marina District': 11,
            'Mission District': 26,
            'Fisherman\'s Wharf': 19,
            'Union Square': 22,
            'Sunset District': 15,
            'Financial District': 23,
            'Haight-Ashbury': 15,
            'Russian Hill': 14
        },
        'Union Square': {
            'Marina District': 18,
            'Mission District': 14,
            'Fisherman\'s Wharf': 15,
            'Presidio': 24,
            'Sunset District': 27,
            'Financial District': 9,
            'Haight-Ashbury': 18,
            'Russian Hill': 13
        },
        'Sunset District': {
            'Marina District': 21,
            'Mission District': 25,
            'Fisherman\'s Wharf': 29,
            'Presidio': 16,
            'Union Square': 30,
            'Financial District': 30,
            'Haight-Ashbury': 15,
            'Russian Hill': 24
        },
        'Financial District': {
            'Marina District': 15,
            'Mission District': 17,
            'Fisherman\'s Wharf': 10,
            'Presidio': 22,
            'Union Square': 9,
            'Sunset District': 30,
            'Haight-Ashbury': 19,
            'Russian Hill': 11
        },
        'Haight-Ashbury': {
            'Marina District': 17,
            'Mission District': 11,
            'Fisherman\'s Wharf': 23,
            'Presidio': 15,
            'Union Square': 19,
            'Sunset District': 15,
            'Financial District': 21,
            'Russian Hill': 17
        },
        'Russian Hill': {
            'Marina District': 7,
            'Mission District': 16,
            'Fisherman\'s Wharf': 7,
            'Presidio': 14,
            'Union Square': 10,
            'Sunset District': 23,
            'Financial District': 11,
            'Haight-Ashbury': 17
        }
    }

    # Friend constraints
    friends = [
        {
            'name': 'Karen',
            'location': 'Mission District',
            'start': time_to_minutes('14:15'),
            'end': time_to_minutes('22:00'),
            'duration': 30
        },
        {
            'name': 'Richard',
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes('14:30'),
            'end': time_to_minutes('17:30'),
            'duration': 30
        },
        {
            'name': 'Robert',
            'location': 'Presidio',
            'start': time_to_minutes('21:45'),
            'end': time_to_minutes('22:45'),
            'duration': 60
        },
        {
            'name': 'Joseph',
            'location': 'Union Square',
            'start': time_to_minutes('11:45'),
            'end': time_to_minutes('14:45'),
            'duration': 120
        },
        {
            'name': 'Helen',
            'location': 'Sunset District',
            'start': time_to_minutes('14:45'),
            'end': time_to_minutes('20:45'),
            'duration': 105
        },
        {
            'name': 'Elizabeth',
            'location': 'Financial District',
            'start': time_to_minutes('10:00'),
            'end': time_to_minutes('12:45'),
            'duration': 75
        },
        {
            'name': 'Kimberly',
            'location': 'Haight-Ashbury',
            'start': time_to_minutes('14:15'),
            'end': time_to_minutes('17:30'),
            'duration': 105
        },
        {
            'name': 'Ashley',
            'location': 'Russian Hill',
            'start': time_to_minutes('11:30'),
            'end': time_to_minutes('21:30'),
            'duration': 45
        }
    ]

    # First try to schedule friends with earliest end times (more constrained first)
    friends_sorted = sorted(friends, key=lambda x: x['end'])
    
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    schedule = []
    
    for friend in friends_sorted:
        travel_time = travel_times[current_location].get(friend['location'], float('inf'))
        if can_meet(friend['start'], friend['end'], travel_time, current_time, friend['duration']):
            arrival_time = current_time + travel_time
            meeting_end = arrival_time + friend['duration']
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(arrival_time),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end
    
    if schedule:
        return {'itinerary': schedule}
    
    # If no schedule found, try with friends who have the smallest time windows first
    friends_sorted = sorted(friends, key=lambda x: x['end'] - x['start'])
    
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    schedule = []
    
    for friend in friends_sorted:
        travel_time = travel_times[current_location].get(friend['location'], float('inf'))
        if can_meet(friend['start'], friend['end'], travel_time, current_time, friend['duration']):
            arrival_time = current_time + travel_time
            meeting_end = arrival_time + friend['duration']
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(arrival_time),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end
    
    if schedule:
        return {'itinerary': schedule}
    
    # If still no schedule, try to meet at least some friends
    friends_sorted = sorted(friends, key=lambda x: x['start'])
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    schedule = []
    
    for friend in friends_sorted:
        travel_time = travel_times[current_location].get(friend['location'], float('inf'))
        if can_meet(friend['start'], friend['end'], travel_time, current_time, friend['duration']):
            arrival_time = current_time + travel_time
            meeting_end = arrival_time + friend['duration']
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(arrival_time),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end
    
    return {'itinerary': schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))