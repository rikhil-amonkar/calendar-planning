import json

# Define travel times between locations
travel_times = {
    'Sunset District': {'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 29},
    'Chinatown': {'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3},
    'Russian Hill': {'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5},
    'North Beach': {'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4}
}

# Define meeting constraints
meetings = {
    'Anthony': {'location': 'Chinatown','start_time': '13:15', 'end_time': '14:30', 'duration': 60},
    'Rebecca': {'location': 'Russian Hill','start_time': '19:30', 'end_time': '21:15', 'duration': 105},
    'Melissa': {'location': 'North Beach','start_time': '08:15', 'end_time': '13:30', 'duration': 105}
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
    current_location = 'Sunset District'
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