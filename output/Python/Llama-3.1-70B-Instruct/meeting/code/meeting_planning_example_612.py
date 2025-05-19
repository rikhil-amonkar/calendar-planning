import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Alamo Square': {'Russian Hill': 13, 'Presidio': 18, 'Chinatown': 16, 'Sunset District': 16, 'The Castro': 8, 'Embarcadero': 17, 'Golden Gate Park': 9},
    'Russian Hill': {'Alamo Square': 15, 'Presidio': 14, 'Chinatown': 9, 'Sunset District': 23, 'The Castro': 21, 'Embarcadero': 8, 'Golden Gate Park': 21},
    'Presidio': {'Alamo Square': 18, 'Russian Hill': 14, 'Chinatown': 21, 'Sunset District': 15, 'The Castro': 21, 'Embarcadero': 20, 'Golden Gate Park': 12},
    'Chinatown': {'Alamo Square': 17, 'Russian Hill': 7, 'Presidio': 19, 'Sunset District': 29, 'The Castro': 22, 'Embarcadero': 5, 'Golden Gate Park': 23},
    'Sunset District': {'Alamo Square': 17, 'Russian Hill': 24, 'Presidio': 16, 'Chinatown': 30, 'The Castro': 17, 'Embarcadero': 31, 'Golden Gate Park': 11},
    'The Castro': {'Alamo Square': 8, 'Russian Hill': 18, 'Presidio': 20, 'Chinatown': 20, 'Sunset District': 17, 'Embarcadero': 22, 'Golden Gate Park': 11},
    'Embarcadero': {'Alamo Square': 19, 'Russian Hill': 8, 'Presidio': 20, 'Chinatown': 7, 'Sunset District': 30, 'The Castro': 25, 'Golden Gate Park': 25},
    'Golden Gate Park': {'Alamo Square': 10, 'Russian Hill': 19, 'Presidio': 11, 'Chinatown': 23, 'Sunset District': 10, 'The Castro': 13, 'Embarcadero': 25}
}

# Define meeting constraints
meeting_constraints = {
    'Emily': {'location': 'Russian Hill','start_time': '12:15', 'end_time': '14:15', 'duration': 105},
    'Mark': {'location': 'Presidio','start_time': '14:45', 'end_time': '19:30', 'duration': 60},
    'Deborah': {'location': 'Chinatown','start_time': '07:30', 'end_time': '15:30', 'duration': 45},
    'Margaret': {'location': 'Sunset District','start_time': '21:30', 'end_time': '22:30', 'duration': 60},
    'George': {'location': 'The Castro','start_time': '07:30', 'end_time': '14:15', 'duration': 60},
    'Andrew': {'location': 'Embarcadero','start_time': '20:15', 'end_time': '22:00', 'duration': 75},
    'Steven': {'location': 'Golden Gate Park','start_time': '11:15', 'end_time': '21:15', 'duration': 105}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Alamo Square'
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