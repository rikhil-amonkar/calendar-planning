import json

# Travel distances (in minutes)
travel_distances = {
    'Bayview': {'Pacific Heights': 23, 'Mission District': 13, 'Haight-Ashbury': 19, 'Financial District': 19},
    'Pacific Heights': {'Bayview': 22, 'Mission District': 15, 'Haight-Ashbury': 11, 'Financial District': 13},
    'Mission District': {'Bayview': 15, 'Pacific Heights': 16, 'Haight-Ashbury': 12, 'Financial District': 17},
    'Haight-Ashbury': {'Bayview': 18, 'Pacific Heights': 12, 'Mission District': 11, 'Financial District': 21},
    'Financial District': {'Bayview': 19, 'Pacific Heights': 13, 'Mission District': 17, 'Haight-Ashbury': 19}
}

# Meeting constraints
meeting_constraints = {
    'Mary': {'location': 'Pacific Heights','start_time': '10:00', 'end_time': '19:00','min_duration': 45},
    'Lisa': {'location': 'Mission District','start_time': '20:30', 'end_time': '22:00','min_duration': 75},
    'Betty': {'location': 'Haight-Ashbury','start_time': '07:15', 'end_time': '17:15','min_duration': 90},
    'Charles': {'location': 'Financial District','start_time': '11:15', 'end_time': '15:00','min_duration': 120}
}

def calculate_meeting_schedule(travel_distances, meeting_constraints):
    itinerary = []
    current_time = '09:00'
    current_location = 'Bayview'

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