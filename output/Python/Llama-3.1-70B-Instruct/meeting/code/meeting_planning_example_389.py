import json

# Travel distances (in minutes)
travel_distances = {
    'Haight-Ashbury': {'Fisherman\'s Wharf': 23, 'Richmond District': 10, 'Mission District': 11, 'Bayview': 18},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Richmond District': 18, 'Mission District': 22, 'Bayview': 26},
    'Richmond District': {'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 'Bayview': 26},
    'Mission District': {'Haight-Ashbury': 12, 'Fisherman\'s Wharf': 22, 'Richmond District': 20, 'Bayview': 15},
    'Bayview': {'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 25, 'Richmond District': 25, 'Mission District': 13}
}

# Meeting constraints
meeting_constraints = {
    'Sarah': {'location': 'Fisherman\'s Wharf','start_time': '14:45', 'end_time': '17:30','min_duration': 105},
    'Mary': {'location': 'Richmond District','start_time': '13:00', 'end_time': '19:15','min_duration': 75},
    'Helen': {'location': 'Mission District','start_time': '21:45', 'end_time': '22:30','min_duration': 30},
    'Thomas': {'location': 'Bayview','start_time': '15:15', 'end_time': '18:45','min_duration': 120}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Haight-Ashbury'

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