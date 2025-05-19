import json

# Define travel times between locations
travel_times = {
    'Embarcadero': {'Financial District': 5, 'Alamo Square': 19},
    'Financial District': {'Embarcadero': 4, 'Alamo Square': 17},
    'Alamo Square': {'Embarcadero': 17, 'Financial District': 17}
}

# Define meeting constraints
meetings = {
    'Stephanie': {'location': 'Financial District','start_time': '08:15', 'end_time': '11:30', 'duration': 90},
    'John': {'location': 'Alamo Square','start_time': '10:15', 'end_time': '20:45', 'duration': 30}
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
    current_location = 'Embarcadero'
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