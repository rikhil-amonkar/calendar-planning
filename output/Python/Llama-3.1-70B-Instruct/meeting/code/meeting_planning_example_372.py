import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Sunset District': {'Alamo Square': 17, 'Russian Hill': 24, 'Golden Gate Park': 11, 'Mission District': 24},
    'Alamo Square': {'Sunset District': 16, 'Russian Hill': 13, 'Golden Gate Park': 9, 'Mission District': 10},
    'Russian Hill': {'Sunset District': 23, 'Alamo Square': 15, 'Golden Gate Park': 21, 'Mission District': 16},
    'Golden Gate Park': {'Sunset District': 10, 'Alamo Square': 10, 'Russian Hill': 19, 'Mission District': 17},
    'Mission District': {'Sunset District': 24, 'Alamo Square': 11, 'Russian Hill': 15, 'Golden Gate Park': 17}
}

# Define meeting constraints
meeting_constraints = {
    'Charles': {'location': 'Alamo Square','start_time': '18:00', 'end_time': '20:45', 'duration': 90},
    'Margaret': {'location': 'Russian Hill','start_time': '09:00', 'end_time': '16:00', 'duration': 30},
    'Daniel': {'location': 'Golden Gate Park','start_time': '08:00', 'end_time': '13:30', 'duration': 15},
    'Stephanie': {'location': 'Mission District','start_time': '20:30', 'end_time': '22:00', 'duration': 90}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Sunset District'
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