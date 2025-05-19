import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Pacific Heights': {'Golden Gate Park': 15, 'The Castro': 16, 'Bayview': 22, 'Marina District': 6, 'Union Square': 12, 'Sunset District': 21, 'Alamo Square': 10, 'Financial District': 13, 'Mission District': 15},
    'Golden Gate Park': {'Pacific Heights': 16, 'The Castro': 13, 'Bayview': 23, 'Marina District': 16, 'Union Square': 22, 'Sunset District': 10, 'Alamo Square': 9, 'Financial District': 26, 'Mission District': 17},
    'The Castro': {'Pacific Heights': 16, 'Golden Gate Park': 11, 'Bayview': 19, 'Marina District': 21, 'Union Square': 19, 'Sunset District': 17, 'Alamo Square': 8, 'Financial District': 21, 'Mission District': 7},
    'Bayview': {'Pacific Heights': 23, 'Golden Gate Park': 22, 'The Castro': 19, 'Marina District': 27, 'Union Square': 18, 'Sunset District': 23, 'Alamo Square': 16, 'Financial District': 19, 'Mission District': 13},
    'Marina District': {'Pacific Heights': 7, 'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27, 'Union Square': 16, 'Sunset District': 19, 'Alamo Square': 15, 'Financial District': 17, 'Mission District': 20},
    'Union Square': {'Pacific Heights': 15, 'Golden Gate Park': 22, 'The Castro': 17, 'Bayview': 15, 'Marina District': 18, 'Sunset District': 27, 'Alamo Square': 15, 'Financial District': 9, 'Mission District': 14},
    'Sunset District': {'Pacific Heights': 21, 'Golden Gate Park': 11, 'The Castro': 17, 'Bayview': 22, 'Marina District': 21, 'Union Square': 30, 'Alamo Square': 17, 'Financial District': 30, 'Mission District': 25},
    'Alamo Square': {'Pacific Heights': 10, 'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16, 'Marina District': 15, 'Union Square': 14, 'Sunset District': 16, 'Financial District': 17, 'Mission District': 10},
    'Financial District': {'Pacific Heights': 13, 'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19, 'Marina District': 15, 'Union Square': 9, 'Sunset District': 30, 'Alamo Square': 17, 'Mission District': 17},
    'Mission District': {'Pacific Heights': 16, 'Golden Gate Park': 17, 'The Castro': 7, 'Bayview': 14, 'Marina District': 19, 'Union Square': 15, 'Sunset District': 24, 'Alamo Square': 11, 'Financial District': 15}
}

# Define meeting constraints
meeting_constraints = {
    'Helen': {'location': 'Golden Gate Park','start_time': '09:30', 'end_time': '12:15', 'duration': 45},
    'Steven': {'location': 'The Castro','start_time': '20:15', 'end_time': '22:00', 'duration': 105},
    'Deborah': {'location': 'Bayview','start_time': '08:30', 'end_time': '12:00', 'duration': 30},
    'Matthew': {'location': 'Marina District','start_time': '09:15', 'end_time': '14:15', 'duration': 45},
    'Joseph': {'location': 'Union Square','start_time': '14:15', 'end_time': '18:45', 'duration': 120},
    'Ronald': {'location': 'Sunset District','start_time': '16:00', 'end_time': '20:45', 'duration': 60},
    'Robert': {'location': 'Alamo Square','start_time': '18:30', 'end_time': '21:15', 'duration': 120},
    'Rebecca': {'location': 'Financial District','start_time': '14:45', 'end_time': '16:15', 'duration': 30},
    'Elizabeth': {'location': 'Mission District','start_time': '18:30', 'end_time': '21:00', 'duration': 120}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Pacific Heights'
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