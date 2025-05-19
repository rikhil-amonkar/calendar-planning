import json

# Define travel times between locations
travel_times = {
    'Sunset District': {'Presidio': 16, 'Nob Hill': 27, 'Pacific Heights': 21, 'Mission District': 25, 'Marina District': 21, 'North Beach': 28, 'Russian Hill': 24, 'Richmond District': 12, 'Embarcadero': 30, 'Alamo Square': 17},
    'Presidio': {'Sunset District': 15, 'Nob Hill': 18, 'Pacific Heights': 11, 'Mission District': 26, 'Marina District': 11, 'North Beach': 18, 'Russian Hill': 14, 'Richmond District': 7, 'Embarcadero': 20, 'Alamo Square': 19},
    'Nob Hill': {'Sunset District': 24, 'Presidio': 17, 'Pacific Heights': 8, 'Mission District': 13, 'Marina District': 11, 'North Beach': 8, 'Russian Hill': 5, 'Richmond District': 14, 'Embarcadero': 9, 'Alamo Square': 11},
    'Pacific Heights': {'Sunset District': 21, 'Presidio': 11, 'Nob Hill': 8, 'Mission District': 15, 'Marina District': 6, 'North Beach': 9, 'Russian Hill': 7, 'Richmond District': 12, 'Embarcadero': 10, 'Alamo Square': 10},
    'Mission District': {'Sunset District': 24, 'Presidio': 25, 'Nob Hill': 12, 'Pacific Heights': 16, 'Marina District': 19, 'North Beach': 17, 'Russian Hill': 15, 'Richmond District': 20, 'Embarcadero': 19, 'Alamo Square': 10},
    'Marina District': {'Sunset District': 19, 'Presidio': 10, 'Nob Hill': 12, 'Pacific Heights': 7, 'Mission District': 20, 'North Beach': 11, 'Russian Hill': 8, 'Richmond District': 11, 'Embarcadero': 14, 'Alamo Square': 15},
    'North Beach': {'Sunset District': 27, 'Presidio': 17, 'Nob Hill': 7, 'Pacific Heights': 8, 'Mission District': 18, 'Marina District': 9, 'Russian Hill': 4, 'Richmond District': 18, 'Embarcadero': 6, 'Alamo Square': 16},
    'Russian Hill': {'Sunset District': 23, 'Presidio': 14, 'Nob Hill': 5, 'Pacific Heights': 7, 'Mission District': 16, 'Marina District': 7, 'North Beach': 5, 'Richmond District': 14, 'Embarcadero': 8, 'Alamo Square': 15},
    'Richmond District': {'Sunset District': 11, 'Presidio': 7, 'Nob Hill': 17, 'Pacific Heights': 10, 'Mission District': 20, 'Marina District': 9, 'North Beach': 17, 'Russian Hill': 13, 'Embarcadero': 19, 'Alamo Square': 11},
    'Embarcadero': {'Sunset District': 30, 'Presidio': 20, 'Nob Hill': 10, 'Pacific Heights': 11, 'Mission District': 20, 'Marina District': 12, 'North Beach': 5, 'Russian Hill': 8, 'Richmond District': 21, 'Alamo Square': 16},
    'Alamo Square': {'Sunset District': 16, 'Presidio': 17, 'Nob Hill': 11, 'Pacific Heights': 10, 'Mission District': 10, 'Marina District': 15, 'North Beach': 15, 'Russian Hill': 13, 'Richmond District': 11, 'Embarcadero': 16}
}

# Define meeting constraints
meetings = {
    'Charles': {'location': 'Presidio','start_time': '13:15', 'end_time': '15:00', 'duration': 105},
    'Robert': {'location': 'Nob Hill','start_time': '13:15', 'end_time': '17:30', 'duration': 90},
    'Nancy': {'location': 'Pacific Heights','start_time': '14:45', 'end_time': '22:00', 'duration': 105},
    'Brian': {'location': 'Mission District','start_time': '15:30', 'end_time': '22:00', 'duration': 60},
    'Kimberly': {'location': 'Marina District','start_time': '17:00', 'end_time': '19:45', 'duration': 75},
    'David': {'location': 'North Beach','start_time': '14:45', 'end_time': '16:30', 'duration': 75},
    'William': {'location': 'Russian Hill','start_time': '12:30', 'end_time': '19:15', 'duration': 120},
    'Jeffrey': {'location': 'Richmond District','start_time': '12:00', 'end_time': '19:15', 'duration': 45},
    'Karen': {'location': 'Embarcadero','start_time': '14:15', 'end_time': '20:45', 'duration': 60},
    'Joshua': {'location': 'Alamo Square','start_time': '18:45', 'end_time': '22:00', 'duration': 60}
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