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
        'Golden Gate Park': {
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'The Castro': 13,
            'Chinatown': 23,
            'Alamo Square': 10,
            'North Beach': 24,
            'Russian Hill': 19
        },
        'Haight-Ashbury': {
            'Golden Gate Park': 7,
            'Fisherman\'s Wharf': 23,
            'The Castro': 6,
            'Chinatown': 19,
            'Alamo Square': 5,
            'North Beach': 19,
            'Russian Hill': 17
        },
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Haight-Ashbury': 22,
            'The Castro': 26,
            'Chinatown': 12,
            'Alamo Square': 20,
            'North Beach': 6,
            'Russian Hill': 7
        },
        'The Castro': {
            'Golden Gate Park': 11,
            'Haight-Ashbury': 6,
            'Fisherman\'s Wharf': 24,
            'Chinatown': 20,
            'Alamo Square': 8,
            'North Beach': 20,
            'Russian Hill': 18
        },
        'Chinatown': {
            'Golden Gate Park': 23,
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 8,
            'The Castro': 22,
            'Alamo Square': 17,
            'North Beach': 3,
            'Russian Hill': 7
        },
        'Alamo Square': {
            'Golden Gate Park': 9,
            'Haight-Ashbury': 5,
            'Fisherman\'s Wharf': 19,
            'The Castro': 8,
            'Chinatown': 16,
            'North Beach': 15,
            'Russian Hill': 13
        },
        'North Beach': {
            'Golden Gate Park': 22,
            'Haight-Ashbury': 18,
            'Fisherman\'s Wharf': 5,
            'The Castro': 22,
            'Chinatown': 6,
            'Alamo Square': 16,
            'Russian Hill': 4
        },
        'Russian Hill': {
            'Golden Gate Park': 21,
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'The Castro': 21,
            'Chinatown': 9,
            'Alamo Square': 15,
            'North Beach': 5
        }
    }

    # Friend constraints
    friends = [
        {
            'name': 'Carol',
            'location': 'Haight-Ashbury',
            'available_start': '21:30',
            'available_end': '22:30',
            'duration': 60
        },
        {
            'name': 'Laura',
            'location': 'Fisherman\'s Wharf',
            'available_start': '11:45',
            'available_end': '21:30',
            'duration': 60
        },
        {
            'name': 'Karen',
            'location': 'The Castro',
            'available_start': '7:15',
            'available_end': '14:00',
            'duration': 75
        },
        {
            'name': 'Elizabeth',
            'location': 'Chinatown',
            'available_start': '12:15',
            'available_end': '21:30',
            'duration': 75
        },
        {
            'name': 'Deborah',
            'location': 'Alamo Square',
            'available_start': '12:00',
            'available_end': '15:00',
            'duration': 105
        },
        {
            'name': 'Jason',
            'location': 'North Beach',
            'available_start': '14:45',
            'available_end': '19:00',
            'duration': 90
        },
        {
            'name': 'Steven',
            'location': 'Russian Hill',
            'available_start': '14:45',
            'available_end': '18:30',
            'duration': 120
        }
    ]

    # Filter friends that are impossible to meet (duration > available time)
    possible_friends = [f for f in friends if 
                        (time_to_minutes(f['available_end']) - time_to_minutes(f['available_start'])) >= f['duration']]

    best_schedule = []
    max_meetings = 0

    # Try all permutations of possible friends (up to 4 for performance)
    for friend_order in permutations(possible_friends, min(len(possible_friends), 4)):
        current_location = 'Golden Gate Park'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0

        for friend in friend_order:
            # Skip Carol in the main permutation since she's handled separately
            if friend['name'] == 'Carol':
                continue
                
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(friend['available_start'])
            available_end = time_to_minutes(friend['available_end'])
            duration = friend['duration']

            # Calculate possible meeting time
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + duration

            if meeting_end <= available_end:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                current_time = meeting_end
                current_location = friend['location']
            else:
                break  # Can't meet this friend, skip this permutation

        if meetings > max_meetings:
            max_meetings = meetings
            best_schedule = schedule

    # Try to add Carol (late night meeting) if possible
    carol = next((f for f in friends if f['name'] == 'Carol'), None)
    if carol and best_schedule:  # Only try to add Carol if we have at least one meeting
        last_meeting_end = time_to_minutes(best_schedule[-1]['end_time'])
        travel_time = travel_times[best_schedule[-1]['location']][carol['location']]
        arrival_time = last_meeting_end + travel_time
        available_start = time_to_minutes(carol['available_start'])
        available_end = time_to_minutes(carol['available_end'])
        duration = carol['duration']

        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration

        if meeting_end <= available_end:
            best_schedule.append({
                'action': 'meet',
                'location': carol['location'],
                'person': carol['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })

    return {'itinerary': best_schedule}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))