import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: from_location -> to_location -> minutes
    travel_times = {
        'Alamo Square': {
            'Russian Hill': 13,
            'Presidio': 18,
            'Chinatown': 16,
            'Sunset District': 16,
            'The Castro': 8,
            'Embarcadero': 17,
            'Golden Gate Park': 9
        },
        'Russian Hill': {
            'Alamo Square': 15,
            'Presidio': 14,
            'Chinatown': 9,
            'Sunset District': 23,
            'The Castro': 21,
            'Embarcadero': 8,
            'Golden Gate Park': 21
        },
        'Presidio': {
            'Alamo Square': 18,
            'Russian Hill': 14,
            'Chinatown': 21,
            'Sunset District': 15,
            'The Castro': 21,
            'Embarcadero': 20,
            'Golden Gate Park': 12
        },
        'Chinatown': {
            'Alamo Square': 17,
            'Russian Hill': 7,
            'Presidio': 19,
            'Sunset District': 29,
            'The Castro': 22,
            'Embarcadero': 5,
            'Golden Gate Park': 23
        },
        'Sunset District': {
            'Alamo Square': 17,
            'Russian Hill': 24,
            'Presidio': 16,
            'Chinatown': 30,
            'The Castro': 17,
            'Embarcadero': 31,
            'Golden Gate Park': 11
        },
        'The Castro': {
            'Alamo Square': 8,
            'Russian Hill': 18,
            'Presidio': 20,
            'Chinatown': 20,
            'Sunset District': 17,
            'Embarcadero': 22,
            'Golden Gate Park': 11
        },
        'Embarcadero': {
            'Alamo Square': 19,
            'Russian Hill': 8,
            'Presidio': 20,
            'Chinatown': 7,
            'Sunset District': 30,
            'The Castro': 25,
            'Golden Gate Park': 25
        },
        'Golden Gate Park': {
            'Alamo Square': 10,
            'Russian Hill': 19,
            'Presidio': 11,
            'Chinatown': 23,
            'Sunset District': 10,
            'The Castro': 13,
            'Embarcadero': 25
        }
    }

    # Friend constraints
    friends = [
        {
            'name': 'Emily',
            'location': 'Russian Hill',
            'available_start': '12:15',
            'available_end': '14:15',
            'min_duration': 105
        },
        {
            'name': 'Mark',
            'location': 'Presidio',
            'available_start': '14:45',
            'available_end': '19:30',
            'min_duration': 60
        },
        {
            'name': 'Deborah',
            'location': 'Chinatown',
            'available_start': '7:30',
            'available_end': '15:30',
            'min_duration': 45
        },
        {
            'name': 'Margaret',
            'location': 'Sunset District',
            'available_start': '21:30',
            'available_end': '22:30',
            'min_duration': 60
        },
        {
            'name': 'George',
            'location': 'The Castro',
            'available_start': '7:30',
            'available_end': '14:15',
            'min_duration': 60
        },
        {
            'name': 'Andrew',
            'location': 'Embarcadero',
            'available_start': '20:15',
            'available_end': '22:00',
            'min_duration': 75
        },
        {
            'name': 'Steven',
            'location': 'Golden Gate Park',
            'available_start': '11:15',
            'available_end': '21:15',
            'min_duration': 105
        }
    ]

    # Filter friends that can't be met due to time constraints
    feasible_friends = []
    for friend in friends:
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        if available_end - available_start >= friend['min_duration']:
            feasible_friends.append(friend)

    best_schedule = []
    max_meetings = 0

    # Try all permutations of feasible friends (limited to first few for performance)
    for perm in permutations(feasible_friends, min(len(feasible_friends), 5)):
        current_location = 'Alamo Square'
        current_time = time_to_minutes('9:00')
        schedule = []
        valid = True

        for friend in perm:
            if friend['location'] not in travel_times[current_location]:
                valid = False
                break
                
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])

            # Calculate meeting time
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + friend['min_duration']

            if meeting_end > available_end:
                valid = False
                break

            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })

            current_location = friend['location']
            current_time = meeting_end

        if valid and len(schedule) > max_meetings:
            max_meetings = len(schedule)
            best_schedule = schedule

    # After trying permutations, check if we can add more meetings
    remaining_friends = [f for f in feasible_friends if f['name'] not in [s['person'] for s in best_schedule]]
    for friend in remaining_friends:
        if friend['location'] not in travel_times[current_location]:
            continue
            
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])

        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['min_duration']

        if meeting_end <= available_end:
            best_schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end

    return {'itinerary': best_schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))