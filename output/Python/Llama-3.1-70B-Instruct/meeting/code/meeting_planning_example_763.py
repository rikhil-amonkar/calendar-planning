import json

# Define travel times between locations
travel_times = {
    'Chinatown': {'Embarcadero': 5, 'Pacific Heights': 10, 'Russian Hill': 7, 'Haight-Ashbury': 19, 'Golden Gate Park': 23, 'Fisherman\'s Wharf': 8, 'Sunset District': 29, 'The Castro': 22},
    'Embarcadero': {'Chinatown': 7, 'Pacific Heights': 11, 'Russian Hill': 8, 'Haight-Ashbury': 21, 'Golden Gate Park': 25, 'Fisherman\'s Wharf': 6, 'Sunset District': 30, 'The Castro': 25},
    'Pacific Heights': {'Chinatown': 11, 'Embarcadero': 10, 'Russian Hill': 7, 'Haight-Ashbury': 11, 'Golden Gate Park': 15, 'Fisherman\'s Wharf': 13, 'Sunset District': 21, 'The Castro': 16},
    'Russian Hill': {'Chinatown': 9, 'Embarcadero': 8, 'Pacific Heights': 7, 'Haight-Ashbury': 17, 'Golden Gate Park': 21, 'Fisherman\'s Wharf': 7, 'Sunset District': 23, 'The Castro': 21},
    'Haight-Ashbury': {'Chinatown': 19, 'Embarcadero': 20, 'Pacific Heights': 12, 'Russian Hill': 17, 'Golden Gate Park': 7, 'Fisherman\'s Wharf': 23, 'Sunset District': 15, 'The Castro': 6},
    'Golden Gate Park': {'Chinatown': 23, 'Embarcadero': 25, 'Pacific Heights': 16, 'Russian Hill': 19, 'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'Sunset District': 10, 'The Castro': 13},
    'Fisherman\'s Wharf': {'Chinatown': 12, 'Embarcadero': 8, 'Pacific Heights': 12, 'Russian Hill': 7, 'Haight-Ashbury': 22, 'Golden Gate Park': 25, 'Sunset District': 27, 'The Castro': 27},
    'Sunset District': {'Chinatown': 30, 'Embarcadero': 30, 'Pacific Heights': 21, 'Russian Hill': 24, 'Haight-Ashbury': 15, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 29, 'The Castro': 17},
    'The Castro': {'Chinatown': 22, 'Embarcadero': 22, 'Pacific Heights': 16, 'Russian Hill': 18, 'Haight-Ashbury': 6, 'Golden Gate Park': 11, 'Fisherman\'s Wharf': 24, 'Sunset District': 17}
}

# Define meeting constraints
meetings = {
    'Richard': {'location': 'Embarcadero','start_time': '15:15', 'end_time': '18:45', 'duration': 90},
    'Mark': {'location': 'Pacific Heights','start_time': '15:00', 'end_time': '17:00', 'duration': 45},
    'Matthew': {'location': 'Russian Hill','start_time': '17:30', 'end_time': '21:00', 'duration': 90},
    'Rebecca': {'location': 'Haight-Ashbury','start_time': '14:45', 'end_time': '18:00', 'duration': 60},
    'Melissa': {'location': 'Golden Gate Park','start_time': '13:45', 'end_time': '17:30', 'duration': 90},
    'Margaret': {'location': 'Fisherman\'s Wharf','start_time': '14:45', 'end_time': '20:15', 'duration': 15},
    'Emily': {'location': 'Sunset District','start_time': '15:45', 'end_time': '17:00', 'duration': 45},
    'George': {'location': 'The Castro','start_time': '14:00', 'end_time': '16:15', 'duration': 75}
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
    current_location = 'Chinatown'
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