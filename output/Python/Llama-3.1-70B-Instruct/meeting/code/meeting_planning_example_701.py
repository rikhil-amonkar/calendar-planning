import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Mission District': {'The Castro': 7, 'Nob Hill': 12, 'Presidio': 25, 'Marina District': 19, 'Pacific Heights': 16, 'Golden Gate Park': 17, 'Chinatown': 16, 'Richmond District': 20},
    'The Castro': {'Mission District': 7, 'Nob Hill': 16, 'Presidio': 20, 'Marina District': 21, 'Pacific Heights': 16, 'Golden Gate Park': 11, 'Chinatown': 22, 'Richmond District': 16},
    'Nob Hill': {'Mission District': 13, 'The Castro': 17, 'Presidio': 17, 'Marina District': 11, 'Pacific Heights': 8, 'Golden Gate Park': 17, 'Chinatown': 6, 'Richmond District': 14},
    'Presidio': {'Mission District': 26, 'The Castro': 21, 'Nob Hill': 18, 'Marina District': 11, 'Pacific Heights': 11, 'Golden Gate Park': 12, 'Chinatown': 21, 'Richmond District': 7},
    'Marina District': {'Mission District': 20, 'The Castro': 22, 'Nob Hill': 12, 'Presidio': 10, 'Pacific Heights': 7, 'Golden Gate Park': 18, 'Chinatown': 15, 'Richmond District': 11},
    'Pacific Heights': {'Mission District': 15, 'The Castro': 16, 'Nob Hill': 8, 'Presidio': 11, 'Marina District': 6, 'Golden Gate Park': 15, 'Chinatown': 11, 'Richmond District': 12},
    'Golden Gate Park': {'Mission District': 17, 'The Castro': 13, 'Nob Hill': 20, 'Presidio': 11, 'Marina District': 16, 'Pacific Heights': 16, 'Chinatown': 23, 'Richmond District': 7},
    'Chinatown': {'Mission District': 17, 'The Castro': 22, 'Nob Hill': 9, 'Presidio': 19, 'Marina District': 12, 'Pacific Heights': 10, 'Golden Gate Park': 23, 'Richmond District': 20},
    'Richmond District': {'Mission District': 20, 'The Castro': 16, 'Nob Hill': 17, 'Presidio': 7, 'Marina District': 9, 'Pacific Heights': 10, 'Golden Gate Park': 9, 'Chinatown': 20}
}

# Define meeting constraints
meeting_constraints = {
    'Lisa': {'location': 'The Castro','start_time': '19:15', 'end_time': '21:15', 'duration': 120},
    'Daniel': {'location': 'Nob Hill','start_time': '08:15', 'end_time': '11:00', 'duration': 15},
    'Elizabeth': {'location': 'Presidio','start_time': '21:15', 'end_time': '22:15', 'duration': 45},
    'Steven': {'location': 'Marina District','start_time': '16:30', 'end_time': '20:45', 'duration': 90},
    'Timothy': {'location': 'Pacific Heights','start_time': '12:00', 'end_time': '18:00', 'duration': 90},
    'Ashley': {'location': 'Golden Gate Park','start_time': '20:45', 'end_time': '21:45', 'duration': 60},
    'Kevin': {'location': 'Chinatown','start_time': '12:00', 'end_time': '19:00', 'duration': 30},
    'Betty': {'location': 'Richmond District','start_time': '13:15', 'end_time': '15:45', 'duration': 30}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Mission District'
    current_time = '9:00'

    # Sort the meeting constraints by start time
    sorted_constraints = sorted(meeting_constraints.items(), key=lambda x: x[1]['start_time'])

    # Calculate the schedule for each person
    for person, constraint in sorted_constraints:
        # Calculate the travel time to the person's location
        travel_time = travel_distances[current_location][constraint['location']]
        arrival_time = add_time(current_time, travel_time)

        # Check if we can meet the person within their available time
        if arrival_time < constraint['start_time']:
            # Wait until the person is available
            start_time = constraint['start_time']
        else:
            start_time = arrival_time

        # Calculate the end time of the meeting
        end_time = add_time(start_time, constraint['duration'])

        # Check if the meeting ends within the person's available time
        if end_time > constraint['end_time']:
            # We cannot meet the person within their available time
            continue

        # Add the meeting to the schedule
        schedule.append({
            'action':'meet',
            'location': constraint['location'],
            'person': person,
        'start_time': start_time,
            'end_time': end_time
        })

        # Update the current location and time
        current_location = constraint['location']
        current_time = end_time

    return schedule

def add_time(time, minutes):
    dt = datetime.strptime(time, '%H:%M')
    dt += timedelta(minutes=minutes)
    return dt.strftime('%H:%M')

def main():
    schedule = calculate_meeting_schedule()
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == '__main__':
    main()