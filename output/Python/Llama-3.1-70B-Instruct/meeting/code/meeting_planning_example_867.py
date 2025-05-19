import json

# Travel distances (in minutes)
travel_distances = {
    'Haight-Ashbury': {'Mission District': 11, 'Union Square': 19, 'Pacific Heights': 12, 'Bayview': 18, 'Fisherman\'s Wharf': 23, 'Marina District': 17, 'Richmond District': 10, 'Sunset District': 15, 'Golden Gate Park': 7},
    'Mission District': {'Haight-Ashbury': 12, 'Union Square': 15, 'Pacific Heights': 16, 'Bayview': 14, 'Fisherman\'s Wharf': 22, 'Marina District': 19, 'Richmond District': 20, 'Sunset District': 24, 'Golden Gate Park': 17},
    'Union Square': {'Haight-Ashbury': 18, 'Mission District': 14, 'Pacific Heights': 15, 'Bayview': 15, 'Fisherman\'s Wharf': 15, 'Marina District': 18, 'Richmond District': 20, 'Sunset District': 27, 'Golden Gate Park': 22},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Mission District': 15, 'Union Square': 12, 'Bayview': 22, 'Fisherman\'s Wharf': 13, 'Marina District': 6, 'Richmond District': 12, 'Sunset District': 21, 'Golden Gate Park': 15},
    'Bayview': {'Haight-Ashbury': 19, 'Mission District': 13, 'Union Square': 18, 'Pacific Heights': 23, 'Fisherman\'s Wharf': 25, 'Marina District': 27, 'Richmond District': 25, 'Sunset District': 23, 'Golden Gate Park': 22},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Mission District': 22, 'Union Square': 13, 'Pacific Heights': 12, 'Bayview': 26, 'Marina District': 9, 'Richmond District': 18, 'Sunset District': 27, 'Golden Gate Park': 25},
    'Marina District': {'Haight-Ashbury': 16, 'Mission District': 20, 'Union Square': 16, 'Pacific Heights': 7, 'Bayview': 27, 'Fisherman\'s Wharf': 10, 'Richmond District': 11, 'Sunset District': 19, 'Golden Gate Park': 18},
    'Richmond District': {'Haight-Ashbury': 10, 'Mission District': 20, 'Union Square': 21, 'Pacific Heights': 10, 'Bayview': 27, 'Fisherman\'s Wharf': 18, 'Marina District': 9, 'Sunset District': 11, 'Golden Gate Park': 9},
    'Sunset District': {'Haight-Ashbury': 15, 'Mission District': 25, 'Union Square': 30, 'Pacific Heights': 21, 'Bayview': 22, 'Fisherman\'s Wharf': 29, 'Marina District': 21, 'Richmond District': 12, 'Golden Gate Park': 11},
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Mission District': 17, 'Union Square': 22, 'Pacific Heights': 16, 'Bayview': 23, 'Fisherman\'s Wharf': 24, 'Marina District': 16, 'Richmond District': 7, 'Sunset District': 10}
}

# Meeting constraints
meeting_constraints = {
    'Elizabeth': {'location': 'Mission District','start_time': '10:30', 'end_time': '20:00','min_duration': 90},
    'David': {'location': 'Union Square','start_time': '15:15', 'end_time': '19:00','min_duration': 45},
    'Sandra': {'location': 'Pacific Heights','start_time': '07:00', 'end_time': '20:00','min_duration': 120},
    'Thomas': {'location': 'Bayview','start_time': '19:30', 'end_time': '20:30','min_duration': 30},
    'Robert': {'location': 'Fisherman\'s Wharf','start_time': '10:00', 'end_time': '15:00','min_duration': 15},
    'Kenneth': {'location': 'Marina District','start_time': '10:45', 'end_time': '13:00','min_duration': 45},
    'Melissa': {'location': 'Richmond District','start_time': '18:15', 'end_time': '20:00','min_duration': 15},
    'Kimberly': {'location': 'Sunset District','start_time': '10:15', 'end_time': '18:15','min_duration': 105},
    'Amanda': {'location': 'Golden Gate Park','start_time': '07:45', 'end_time': '18:45','min_duration': 15}
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