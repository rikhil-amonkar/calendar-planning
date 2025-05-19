import json

# Define travel times between locations
travel_times = {
    'Russian Hill': {'Marina District': 7, 'Financial District': 11, 'Alamo Square': 15, 'Golden Gate Park': 21, 'The Castro': 21, 'Bayview': 23, 'Sunset District': 23, 'Haight-Ashbury': 17, 'Nob Hill': 5},
    'Marina District': {'Russian Hill': 8, 'Financial District': 17, 'Alamo Square': 15, 'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27, 'Sunset District': 19, 'Haight-Ashbury': 16, 'Nob Hill': 12},
    'Financial District': {'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17, 'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Nob Hill': 8},
    'Alamo Square': {'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17, 'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Sunset District': 16, 'Haight-Ashbury': 5, 'Nob Hill': 11},
    'Golden Gate Park': {'Russian Hill': 19, 'Marina District': 16, 'Financial District': 26, 'Alamo Square': 9, 'The Castro': 13, 'Bayview': 23, 'Sunset District': 10, 'Haight-Ashbury': 7, 'Nob Hill': 20},
    'The Castro': {'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21, 'Alamo Square': 8, 'Golden Gate Park': 11, 'Bayview': 19, 'Sunset District': 17, 'Haight-Ashbury': 6, 'Nob Hill': 16},
    'Bayview': {'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19, 'Alamo Square': 16, 'Golden Gate Park': 22, 'The Castro': 19, 'Sunset District': 23, 'Haight-Ashbury': 19, 'Nob Hill': 20},
    'Sunset District': {'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30, 'Alamo Square': 17, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Haight-Ashbury': 15, 'Nob Hill': 27},
    'Haight-Ashbury': {'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21, 'Alamo Square': 5, 'Golden Gate Park': 7, 'The Castro': 6, 'Bayview': 18, 'Sunset District': 15, 'Nob Hill': 15},
    'Nob Hill': {'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9, 'Alamo Square': 11, 'Golden Gate Park': 17, 'The Castro': 17, 'Bayview': 19, 'Sunset District': 24, 'Haight-Ashbury': 13}
}

# Define meeting constraints
meetings = {
    'Mark': {'location': 'Marina District','start_time': '18:45', 'end_time': '21:00', 'duration': 90},
    'Karen': {'location': 'Financial District','start_time': '09:30', 'end_time': '12:45', 'duration': 90},
    'Barbara': {'location': 'Alamo Square','start_time': '10:00', 'end_time': '19:30', 'duration': 90},
    'Nancy': {'location': 'Golden Gate Park','start_time': '16:45', 'end_time': '20:00', 'duration': 105},
    'David': {'location': 'The Castro','start_time': '09:00', 'end_time': '18:00', 'duration': 120},
    'Linda': {'location': 'Bayview','start_time': '18:15', 'end_time': '19:45', 'duration': 45},
    'Kevin': {'location': 'Sunset District','start_time': '10:00', 'end_time': '17:45', 'duration': 120},
    'Matthew': {'location': 'Haight-Ashbury','start_time': '10:15', 'end_time': '15:30', 'duration': 45},
    'Andrew': {'location': 'Nob Hill','start_time': '11:45', 'end_time': '16:45', 'duration': 105}
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
    current_location = 'Russian Hill'
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