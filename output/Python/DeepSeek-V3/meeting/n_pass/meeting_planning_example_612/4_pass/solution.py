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

    # Sort friends by available_end time to maximize number of meetings
    friends.sort(key=lambda x: time_to_minutes(x['available_end']))

    current_location = 'Alamo Square'
    current_time = time_to_minutes('9:00')
    schedule = []

    for friend in friends:
        if friend['location'] not in travel_times[current_location]:
            continue
            
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])

        # Calculate meeting time
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['min_duration']

        if meeting_end <= available_end:
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })

            current_location = friend['location']
            current_time = meeting_end

    # Try to optimize the schedule by checking if we can fit more meetings
    remaining_friends = [f for f in friends if f['name'] not in [s['person'] for s in schedule]]
    optimized = True
    
    while optimized and remaining_friends:
        optimized = False
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
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_location = friend['location']
                current_time = meeting_end
                remaining_friends.remove(friend)
                optimized = True
                break

    return {'itinerary': schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))