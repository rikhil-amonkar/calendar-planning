import json

# Define travel times between locations
travel_times = {
    'Union Square': {'Golden Gate Park': 22, 'Pacific Heights': 15, 'Presidio': 24, 'Chinatown': 7, 'The Castro': 19},
    'Golden Gate Park': {'Union Square': 22, 'Pacific Heights': 16, 'Presidio': 11, 'Chinatown': 23, 'The Castro': 13},
    'Pacific Heights': {'Union Square': 12, 'Golden Gate Park': 15, 'Presidio': 11, 'Chinatown': 11, 'The Castro': 16},
    'Presidio': {'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11, 'Chinatown': 21, 'The Castro': 21},
    'Chinatown': {'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10, 'Presidio': 19, 'The Castro': 22},
    'The Castro': {'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16, 'Presidio': 20, 'Chinatown': 20}
}

# Define meeting constraints
meetings = {
    'Andrew': {'location': 'Golden Gate Park','start_time': '11:45', 'end_time': '14:30', 'duration': 75},
    'Sarah': {'location': 'Pacific Heights','start_time': '16:15', 'end_time': '18:45', 'duration': 15},
    'Nancy': {'location': 'Presidio','start_time': '17:30', 'end_time': '19:15', 'duration': 60},
    'Rebecca': {'location': 'Chinatown','start_time': '09:45', 'end_time': '21:30', 'duration': 90},
    'Robert': {'location': 'The Castro','start_time': '08:30', 'end_time': '14:15', 'duration': 30}
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
    current_location = 'Union Square'
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