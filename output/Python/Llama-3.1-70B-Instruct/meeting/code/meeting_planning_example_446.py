import json

# Travel distances (in minutes)
travel_distances = {
    'Richmond District': {'Marina District': 9, 'Chinatown': 20, 'Financial District': 22, 'Bayview': 26, 'Union Square': 21},
    'Marina District': {'Richmond District': 11, 'Chinatown': 16, 'Financial District': 17, 'Bayview': 27, 'Union Square': 16},
    'Chinatown': {'Richmond District': 20, 'Marina District': 12, 'Financial District': 5, 'Bayview': 22, 'Union Square': 7},
    'Financial District': {'Richmond District': 21, 'Marina District': 15, 'Chinatown': 5, 'Bayview': 19, 'Union Square': 9},
    'Bayview': {'Richmond District': 25, 'Marina District': 25, 'Chinatown': 18, 'Financial District': 19, 'Union Square': 17},
    'Union Square': {'Richmond District': 20, 'Marina District': 18, 'Chinatown': 7, 'Financial District': 9, 'Bayview': 15}
}

# Meeting constraints
meeting_constraints = {
    'Kimberly': {'location': 'Marina District','start_time': '13:15', 'end_time': '16:45','min_duration': 15},
    'Robert': {'location': 'Chinatown','start_time': '12:15', 'end_time': '20:15','min_duration': 15},
    'Rebecca': {'location': 'Financial District','start_time': '13:15', 'end_time': '16:45','min_duration': 75},
    'Margaret': {'location': 'Bayview','start_time': '09:30', 'end_time': '13:30','min_duration': 30},
    'Kenneth': {'location': 'Union Square','start_time': '19:30', 'end_time': '21:15','min_duration': 75}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Richmond District'

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