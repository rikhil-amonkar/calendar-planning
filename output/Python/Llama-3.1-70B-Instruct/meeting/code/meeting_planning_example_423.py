import json

# Travel distances (in minutes)
travel_distances = {
    'Presidio': {'Richmond District': 7, 'North Beach': 18, 'Financial District': 23, 'Golden Gate Park': 12, 'Union Square': 22},
    'Richmond District': {'Presidio': 7, 'North Beach': 17, 'Financial District': 22, 'Golden Gate Park': 9, 'Union Square': 21},
    'North Beach': {'Presidio': 17, 'Richmond District': 18, 'Financial District': 8, 'Golden Gate Park': 22, 'Union Square': 7},
    'Financial District': {'Presidio': 22, 'Richmond District': 21, 'North Beach': 7, 'Golden Gate Park': 23, 'Union Square': 9},
    'Golden Gate Park': {'Presidio': 11, 'Richmond District': 7, 'North Beach': 24, 'Financial District': 26, 'Union Square': 22},
    'Union Square': {'Presidio': 24, 'Richmond District': 20, 'North Beach': 10, 'Financial District': 9, 'Golden Gate Park': 22}
}

# Meeting constraints
meeting_constraints = {
    'Jason': {'location': 'Richmond District','start_time': '13:00', 'end_time': '20:45','min_duration': 90},
    'Melissa': {'location': 'North Beach','start_time': '18:45', 'end_time': '20:15','min_duration': 45},
    'Brian': {'location': 'Financial District','start_time': '09:45', 'end_time': '21:45','min_duration': 15},
    'Elizabeth': {'location': 'Golden Gate Park','start_time': '08:45', 'end_time': '21:30','min_duration': 105},
    'Laura': {'location': 'Union Square','start_time': '14:15', 'end_time': '19:30','min_duration': 75}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Presidio'

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