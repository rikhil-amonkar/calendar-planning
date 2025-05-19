import json

# Travel distances (in minutes)
travel_distances = {
    'Presidio': {'Marina District': 11, 'The Castro': 21, 'Fisherman\'s Wharf': 19, 'Bayview': 31, 'Pacific Heights': 11, 'Mission District': 26, 'Alamo Square': 19, 'Golden Gate Park': 12},
    'Marina District': {'Presidio': 10, 'The Castro': 22, 'Fisherman\'s Wharf': 10, 'Bayview': 27, 'Pacific Heights': 7, 'Mission District': 20, 'Alamo Square': 15, 'Golden Gate Park': 18},
    'The Castro': {'Presidio': 20, 'Marina District': 21, 'Fisherman\'s Wharf': 24, 'Bayview': 19, 'Pacific Heights': 16, 'Mission District': 7, 'Alamo Square': 8, 'Golden Gate Park': 11},
    'Fisherman\'s Wharf': {'Presidio': 17, 'Marina District': 9, 'The Castro': 27, 'Bayview': 26, 'Pacific Heights': 12, 'Mission District': 22, 'Alamo Square': 21, 'Golden Gate Park': 25},
    'Bayview': {'Presidio': 32, 'Marina District': 27, 'The Castro': 19, 'Fisherman\'s Wharf': 25, 'Pacific Heights': 23, 'Mission District': 13, 'Alamo Square': 16, 'Golden Gate Park': 22},
    'Pacific Heights': {'Presidio': 11, 'Marina District': 6, 'The Castro': 16, 'Fisherman\'s Wharf': 13, 'Bayview': 22, 'Mission District': 15, 'Alamo Square': 10, 'Golden Gate Park': 15},
    'Mission District': {'Presidio': 25, 'Marina District': 19, 'The Castro': 7, 'Fisherman\'s Wharf': 22, 'Bayview': 14, 'Pacific Heights': 16, 'Alamo Square': 11, 'Golden Gate Park': 17},
    'Alamo Square': {'Presidio': 17, 'Marina District': 15, 'The Castro': 8, 'Fisherman\'s Wharf': 19, 'Bayview': 16, 'Pacific Heights': 10, 'Mission District': 10, 'Golden Gate Park': 9},
    'Golden Gate Park': {'Presidio': 11, 'Marina District': 16, 'The Castro': 13, 'Fisherman\'s Wharf': 24, 'Bayview': 23, 'Pacific Heights': 16, 'Mission District': 17, 'Alamo Square': 9}
}

# Meeting constraints
meeting_constraints = {
    'Amanda': {'location': 'Marina District','start_time': '14:45', 'end_time': '19:30','min_duration': 105},
    'Melissa': {'location': 'The Castro','start_time': '09:30', 'end_time': '17:00','min_duration': 30},
    'Jeffrey': {'location': 'Fisherman\'s Wharf','start_time': '12:45', 'end_time': '18:45','min_duration': 120},
    'Matthew': {'location': 'Bayview','start_time': '10:15', 'end_time': '13:15','min_duration': 30},
    'Nancy': {'location': 'Pacific Heights','start_time': '17:00', 'end_time': '21:30','min_duration': 105},
    'Karen': {'location': 'Mission District','start_time': '17:30', 'end_time': '20:30','min_duration': 105},
    'Robert': {'location': 'Alamo Square','start_time': '11:15', 'end_time': '17:30','min_duration': 120},
    'Joseph': {'location': 'Golden Gate Park','start_time': '08:30', 'end_time': '21:15','min_duration': 105}
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