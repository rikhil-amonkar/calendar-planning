import json

# Travel distances (in minutes)
travel_distances = {
    'Marina District': {'Mission District': 20, 'Fisherman\'s Wharf': 10, 'Presidio': 10, 'Union Square': 16, 'Sunset District': 19, 'Financial District': 17, 'Haight-Ashbury': 16, 'Russian Hill': 8},
    'Mission District': {'Marina District': 19, 'Fisherman\'s Wharf': 22, 'Presidio': 25, 'Union Square': 15, 'Sunset District': 24, 'Financial District': 15, 'Haight-Ashbury': 12, 'Russian Hill': 15},
    'Fisherman\'s Wharf': {'Marina District': 9, 'Mission District': 22, 'Presidio': 17, 'Union Square': 13, 'Sunset District': 27, 'Financial District': 11, 'Haight-Ashbury': 22, 'Russian Hill': 7},
    'Presidio': {'Marina District': 11, 'Mission District': 26, 'Fisherman\'s Wharf': 19, 'Union Square': 22, 'Sunset District': 15, 'Financial District': 23, 'Haight-Ashbury': 15, 'Russian Hill': 14},
    'Union Square': {'Marina District': 18, 'Mission District': 14, 'Fisherman\'s Wharf': 15, 'Presidio': 24, 'Sunset District': 27, 'Financial District': 9, 'Haight-Ashbury': 18, 'Russian Hill': 13},
    'Sunset District': {'Marina District': 21, 'Mission District': 25, 'Fisherman\'s Wharf': 29, 'Presidio': 16, 'Union Square': 30, 'Financial District': 30, 'Haight-Ashbury': 15, 'Russian Hill': 24},
    'Financial District': {'Marina District': 15, 'Mission District': 17, 'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Union Square': 9, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Russian Hill': 11},
    'Haight-Ashbury': {'Marina District': 17, 'Mission District': 11, 'Fisherman\'s Wharf': 23, 'Presidio': 15, 'Union Square': 19, 'Sunset District': 15, 'Financial District': 21, 'Russian Hill': 17},
    'Russian Hill': {'Marina District': 7, 'Mission District': 16, 'Fisherman\'s Wharf': 7, 'Presidio': 14, 'Union Square': 10, 'Sunset District': 23, 'Financial District': 11, 'Haight-Ashbury': 17}
}

# Meeting constraints
meeting_constraints = {
    'Karen': {'location': 'Mission District','start_time': '14:15', 'end_time': '22:00','min_duration': 30},
    'Richard': {'location': 'Fisherman\'s Wharf','start_time': '14:30', 'end_time': '17:30','min_duration': 30},
    'Robert': {'location': 'Presidio','start_time': '21:45', 'end_time': '22:45','min_duration': 60},
    'Joseph': {'location': 'Union Square','start_time': '11:45', 'end_time': '14:45','min_duration': 120},
    'Helen': {'location': 'Sunset District','start_time': '14:45', 'end_time': '20:45','min_duration': 105},
    'Elizabeth': {'location': 'Financial District','start_time': '10:00', 'end_time': '12:45','min_duration': 75},
    'Kimberly': {'location': 'Haight-Ashbury','start_time': '14:15', 'end_time': '17:30','min_duration': 105},
    'Ashley': {'location': 'Russian Hill','start_time': '11:30', 'end_time': '21:30','min_duration': 45}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Marina District'

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