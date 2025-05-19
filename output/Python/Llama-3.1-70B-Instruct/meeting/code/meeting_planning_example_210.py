import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Fisherman\'s Wharf': {'Presidio': 17, 'Richmond District': 18, 'Financial District': 11},
    'Presidio': {'Fisherman\'s Wharf': 19, 'Richmond District': 7, 'Financial District': 23},
    'Richmond District': {'Fisherman\'s Wharf': 18, 'Presidio': 7, 'Financial District': 22},
    'Financial District': {'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Richmond District': 21}
}

# Define meeting constraints
meeting_constraints = {
    'Emily': {'location': 'Presidio','start_time': '16:15', 'end_time': '21:00', 'duration': 105},
    'Joseph': {'location': 'Richmond District','start_time': '17:15', 'end_time': '22:00', 'duration': 120},
    'Melissa': {'location': 'Financial District','start_time': '15:45', 'end_time': '21:45', 'duration': 75}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Fisherman\'s Wharf'
    current_time = '9:00'

    # Calculate the schedule for each person
    for person, constraint in meeting_constraints.items():
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

        # Add travel time to the next location
        next_person = next((p for p, c in meeting_constraints.items() if c['location']!= current_location), None)
        if next_person:
            next_location = meeting_constraints[next_person]['location']
            travel_time = travel_distances[current_location][next_location]
            current_time = add_time(current_time, travel_time)

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