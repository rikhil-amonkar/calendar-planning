import json

# Define travel times between locations
travel_times = {
    'Bayview': {'Russian Hill': 23, 'Alamo Square': 16, 'North Beach': 21, 'Financial District': 19},
    'Russian Hill': {'Bayview': 23, 'Alamo Square': 15, 'North Beach': 5, 'Financial District': 11},
    'Alamo Square': {'Bayview': 16, 'Russian Hill': 13, 'North Beach': 15, 'Financial District': 17},
    'North Beach': {'Bayview': 22, 'Russian Hill': 4, 'Alamo Square': 16, 'Financial District': 8},
    'Financial District': {'Bayview': 19, 'Russian Hill': 10, 'Alamo Square': 17, 'North Beach': 7}
}

# Define meeting constraints
meetings = {
    'Joseph': {'location': 'Russian Hill','start_time': '08:30', 'end_time': '19:15', 'duration': 60},
    'Nancy': {'location': 'Alamo Square','start_time': '11:00', 'end_time': '16:00', 'duration': 90},
    'Jason': {'location': 'North Beach','start_time': '16:45', 'end_time': '21:45', 'duration': 15},
    'Jeffrey': {'location': 'Financial District','start_time': '10:30', 'end_time': '15:45', 'duration': 45}
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
    current_location = 'Bayview'
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