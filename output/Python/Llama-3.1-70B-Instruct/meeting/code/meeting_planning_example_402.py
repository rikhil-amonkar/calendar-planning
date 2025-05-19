import json

# Define travel times between locations
travel_times = {
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Sunset District': 10, 'Marina District': 16, 'Financial District': 26, 'Union Square': 22},
    'Haight-Ashbury': {'Golden Gate Park': 7, 'Sunset District': 15, 'Marina District': 17, 'Financial District': 21, 'Union Square': 17},
    'Sunset District': {'Golden Gate Park': 11, 'Haight-Ashbury': 15, 'Marina District': 21, 'Financial District': 30, 'Union Square': 30},
    'Marina District': {'Golden Gate Park': 18, 'Haight-Ashbury': 16, 'Sunset District': 19, 'Financial District': 17, 'Union Square': 16},
    'Financial District': {'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Sunset District': 31, 'Marina District': 15, 'Union Square': 9},
    'Union Square': {'Golden Gate Park': 22, 'Haight-Ashbury': 18, 'Sunset District': 26, 'Marina District': 18, 'Financial District': 9}
}

# Define meeting constraints
meetings = {
    'Sarah': {'location': 'Haight-Ashbury','start_time': '17:00', 'end_time': '21:30', 'duration': 105},
    'Patricia': {'location': 'Sunset District','start_time': '17:00', 'end_time': '19:45', 'duration': 45},
    'Matthew': {'location': 'Marina District','start_time': '09:15', 'end_time': '12:00', 'duration': 15},
    'Joseph': {'location': 'Financial District','start_time': '14:15', 'end_time': '18:45', 'duration': 30},
    'Robert': {'location': 'Union Square','start_time': '10:15', 'end_time': '21:45', 'duration': 15}
}

def calculate_meeting_time(current_time, travel_time, meeting_duration):
    meeting_start_time = add_time(current_time, travel_time)
    meeting_end_time = add_time(meeting_start_time, meeting_duration)
    return meeting_start_time, meeting_end_time

def add_time(time, minutes):
    hours, mins = map(int, time.split(':'))
    mins += minutes
    hours += mins // 60
    mins %= 60
    return f'{hours}:{mins:02d}'

def is_meeting_possible(current_time, meeting_start_time, meeting_end_time):
    return meeting_start_time <= current_time < meeting_end_time

def plan_meetings():
    current_time = '09:00'
    current_location = 'Golden Gate Park'
    itinerary = []

    for person, meeting in meetings.items():
        travel_time = travel_times[current_location][meeting['location']]
        meeting_start_time, meeting_end_time = calculate_meeting_time(current_time, travel_time, meeting['duration'])
        if is_meeting_possible(meeting_start_time, meeting['start_time'], meeting['end_time']):
            itinerary.append({
                'action':'meet',
                'location': meeting['location'],
                'person': person,
           'start_time': meeting_start_time,
                'end_time': meeting_end_time
            })
            current_time = meeting_end_time
            current_location = meeting['location']

    return itinerary

def main():
    itinerary = plan_meetings()
    print(json.dumps({'itinerary': itinerary}, indent=4))

if __name__ == '__main__':
    main()