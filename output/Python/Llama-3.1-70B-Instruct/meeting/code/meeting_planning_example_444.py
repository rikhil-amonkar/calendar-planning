import json

# Travel distances (in minutes)
travel_distances = {
    'Financial District': {'Russian Hill': 10, 'Sunset District': 31, 'North Beach': 7, 'The Castro': 23, 'Golden Gate Park': 23},
    'Russian Hill': {'Financial District': 11, 'Sunset District': 23, 'North Beach': 5, 'The Castro': 21, 'Golden Gate Park': 21},
    'Sunset District': {'Financial District': 30, 'Russian Hill': 24, 'North Beach': 29, 'The Castro': 17, 'Golden Gate Park': 11},
    'North Beach': {'Financial District': 8, 'Russian Hill': 4, 'Sunset District': 27, 'The Castro': 22, 'Golden Gate Park': 22},
    'The Castro': {'Financial District': 20, 'Russian Hill': 18, 'Sunset District': 17, 'North Beach': 20, 'Golden Gate Park': 11},
    'Golden Gate Park': {'Financial District': 26, 'Russian Hill': 19, 'Sunset District': 10, 'North Beach': 24, 'The Castro': 13}
}

# Meeting constraints
meeting_constraints = {
    'Ronald': {'location': 'Russian Hill','start_time': '13:45', 'end_time': '17:15','min_duration': 105},
    'Patricia': {'location': 'Sunset District','start_time': '09:15', 'end_time': '22:00','min_duration': 60},
    'Laura': {'location': 'North Beach','start_time': '12:30', 'end_time': '12:45','min_duration': 15},
    'Emily': {'location': 'The Castro','start_time': '16:15', 'end_time': '18:30','min_duration': 60},
    'Mary': {'location': 'Golden Gate Park','start_time': '15:00', 'end_time': '16:30','min_duration': 60}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Financial District'

    # Sort meeting constraints by start time
    sorted_meetings = sorted(meeting_constraints.items(), key=lambda x: x[1]['start_time'])

    for person, meeting in sorted_meetings:
        travel_time = travel_distances[current_location][meeting['location']]
        arrival_time = add_time(current_time, travel_time)

        if arrival_time > meeting['start_time']:
            start_time = arrival_time
        else:
            start_time = meeting['start_time']

        end_time = add_time(start_time, meeting['min_duration'])

        if end_time > meeting['end_time']:
            end_time = meeting['end_time']

        itinerary.append({
            'action':'meet',
            'location': meeting['location'],
            'person': person,
          'start_time': start_time,
            'end_time': end_time
        })

        current_time = end_time
        current_location = meeting['location']

    return itinerary

def add_time(time, minutes):
    hours, mins = map(int, time.split(':'))
    mins += minutes
    hours += mins // 60
    mins %= 60
    return f'{hours}:{mins:02d}'

def main():
    meeting_schedule = calculate_meeting_schedule(travel_distances, meeting_constraints)
    print(json.dumps({'itinerary': meeting_schedule}, indent=4))

if __name__ == '__main__':
    main()