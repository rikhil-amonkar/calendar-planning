import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Russian Hill': {'Pacific Heights': 7, 'North Beach': 5, 'Golden Gate Park': 21, 'Embarcadero': 8, 'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Mission District': 16, 'Alamo Square': 15, 'Bayview': 23, 'Richmond District': 14},
    'Pacific Heights': {'Russian Hill': 7, 'North Beach': 9, 'Golden Gate Park': 15, 'Embarcadero': 10, 'Haight-Ashbury': 11, 'Fisherman\'s Wharf': 13, 'Mission District': 15, 'Alamo Square': 10, 'Bayview': 22, 'Richmond District': 12},
    'North Beach': {'Russian Hill': 4, 'Pacific Heights': 8, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Haight-Ashbury': 18, 'Fisherman\'s Wharf': 5, 'Mission District': 18, 'Alamo Square': 16, 'Bayview': 25, 'Richmond District': 18},
    'Golden Gate Park': {'Russian Hill': 19, 'Pacific Heights': 16, 'North Beach': 23, 'Embarcadero': 25, 'Haight-Ashbury': 7, 'Fisherman\'s Wharf': 24, 'Mission District': 17, 'Alamo Square': 9, 'Bayview': 23, 'Richmond District': 7},
    'Embarcadero': {'Russian Hill': 8, 'Pacific Heights': 11, 'North Beach': 5, 'Golden Gate Park': 25, 'Haight-Ashbury': 21, 'Fisherman\'s Wharf': 6, 'Mission District': 20, 'Alamo Square': 19, 'Bayview': 21, 'Richmond District': 21},
    'Haight-Ashbury': {'Russian Hill': 17, 'Pacific Heights': 12, 'North Beach': 19, 'Golden Gate Park': 7, 'Embarcadero': 20, 'Fisherman\'s Wharf': 23, 'Mission District': 11, 'Alamo Square': 5, 'Bayview': 18, 'Richmond District': 10},
    'Fisherman\'s Wharf': {'Russian Hill': 7, 'Pacific Heights': 12, 'North Beach': 6, 'Golden Gate Park': 25, 'Embarcadero': 8, 'Haight-Ashbury': 22, 'Mission District': 22, 'Alamo Square': 21, 'Bayview': 26, 'Richmond District': 18},
    'Mission District': {'Russian Hill': 15, 'Pacific Heights': 16, 'North Beach': 17, 'Golden Gate Park': 17, 'Embarcadero': 19, 'Haight-Ashbury': 12, 'Fisherman\'s Wharf': 22, 'Alamo Square': 11, 'Bayview': 14, 'Richmond District': 20},
    'Alamo Square': {'Russian Hill': 13, 'Pacific Heights': 10, 'North Beach': 15, 'Golden Gate Park': 9, 'Embarcadero': 16, 'Haight-Ashbury': 5, 'Fisherman\'s Wharf': 19, 'Mission District': 10, 'Bayview': 16, 'Richmond District': 11},
    'Bayview': {'Russian Hill': 23, 'Pacific Heights': 23, 'North Beach': 22, 'Golden Gate Park': 22, 'Embarcadero': 19, 'Haight-Ashbury': 19, 'Fisherman\'s Wharf': 25, 'Mission District': 13, 'Alamo Square': 16, 'Richmond District': 25},
    'Richmond District': {'Russian Hill': 13, 'Pacific Heights': 10, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Haight-Ashbury': 10, 'Fisherman\'s Wharf': 18, 'Mission District': 20, 'Alamo Square': 13, 'Bayview': 27}
}

# Define meeting constraints
meeting_constraints = {
    'Emily': {'location': 'Pacific Heights','start_time': '09:15', 'end_time': '13:45', 'duration': 120},
    'Helen': {'location': 'North Beach','start_time': '13:45', 'end_time': '18:45', 'duration': 30},
    'Kimberly': {'location': 'Golden Gate Park','start_time': '18:45', 'end_time': '21:15', 'duration': 75},
    'James': {'location': 'Embarcadero','start_time': '10:30', 'end_time': '11:30', 'duration': 30},
    'Linda': {'location': 'Haight-Ashbury','start_time': '07:30', 'end_time': '19:15', 'duration': 15},
    'Paul': {'location': 'Fisherman\'s Wharf','start_time': '14:45', 'end_time': '18:45', 'duration': 90},
    'Anthony': {'location': 'Mission District','start_time': '08:00', 'end_time': '14:45', 'duration': 105},
    'Nancy': {'location': 'Alamo Square','start_time': '08:30', 'end_time': '13:45', 'duration': 120},
    'William': {'location': 'Bayview','start_time': '17:30', 'end_time': '20:30', 'duration': 120},
    'Margaret': {'location': 'Richmond District','start_time': '15:15', 'end_time': '18:15', 'duration': 45}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Russian Hill'
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