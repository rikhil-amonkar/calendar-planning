import json

# Travel distances (in minutes)
travel_distances = {
    'Haight-Ashbury': {'Russian Hill': 17, 'Fisherman\'s Wharf': 23, 'Nob Hill': 15, 'Golden Gate Park': 7, 'Alamo Square': 5, 'Pacific Heights': 12},
    'Russian Hill': {'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Nob Hill': 5, 'Golden Gate Park': 21, 'Alamo Square': 15, 'Pacific Heights': 7},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Russian Hill': 7, 'Nob Hill': 11, 'Golden Gate Park': 25, 'Alamo Square': 20, 'Pacific Heights': 12},
    'Nob Hill': {'Haight-Ashbury': 13, 'Russian Hill': 5, 'Fisherman\'s Wharf': 11, 'Golden Gate Park': 17, 'Alamo Square': 11, 'Pacific Heights': 8},
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Russian Hill': 19, 'Fisherman\'s Wharf': 24, 'Nob Hill': 20, 'Alamo Square': 10, 'Pacific Heights': 16},
    'Alamo Square': {'Haight-Ashbury': 5, 'Russian Hill': 13, 'Fisherman\'s Wharf': 19, 'Nob Hill': 11, 'Golden Gate Park': 9, 'Pacific Heights': 10},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Russian Hill': 7, 'Fisherman\'s Wharf': 13, 'Nob Hill': 8, 'Golden Gate Park': 15, 'Alamo Square': 10}
}

# Meeting constraints
meeting_constraints = {
    'Stephanie': {'location': 'Russian Hill','start_time': '20:00', 'end_time': '20:45','min_duration': 15},
    'Kevin': {'location': 'Fisherman\'s Wharf','start_time': '19:15', 'end_time': '21:45','min_duration': 75},
    'Robert': {'location': 'Nob Hill','start_time': '07:45', 'end_time': '10:30','min_duration': 90},
    'Steven': {'location': 'Golden Gate Park','start_time': '08:30', 'end_time': '17:00','min_duration': 75},
    'Anthony': {'location': 'Alamo Square','start_time': '07:45', 'end_time': '19:45','min_duration': 15},
    'Sandra': {'location': 'Pacific Heights','start_time': '14:45', 'end_time': '21:45','min_duration': 45}
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