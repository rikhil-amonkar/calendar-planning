import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Financial District': {'Golden Gate Park': 23, 'Chinatown': 5, 'Union Square': 9, 'Fisherman\'s Wharf': 10, 'Pacific Heights': 13, 'North Beach': 7},
    'Golden Gate Park': {'Financial District': 26, 'Chinatown': 23, 'Union Square': 22, 'Fisherman\'s Wharf': 24, 'Pacific Heights': 16, 'North Beach': 24},
    'Chinatown': {'Financial District': 5, 'Golden Gate Park': 23, 'Union Square': 7, 'Fisherman\'s Wharf': 8, 'Pacific Heights': 10, 'North Beach': 3},
    'Union Square': {'Financial District': 9, 'Golden Gate Park': 22, 'Chinatown': 7, 'Fisherman\'s Wharf': 15, 'Pacific Heights': 15, 'North Beach': 10},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Golden Gate Park': 25, 'Chinatown': 12, 'Union Square': 13, 'Pacific Heights': 12, 'North Beach': 6},
    'Pacific Heights': {'Financial District': 13, 'Golden Gate Park': 15, 'Chinatown': 11, 'Union Square': 12, 'Fisherman\'s Wharf': 13, 'North Beach': 9},
    'North Beach': {'Financial District': 8, 'Golden Gate Park': 22, 'Chinatown': 6, 'Union Square': 7, 'Fisherman\'s Wharf': 5, 'Pacific Heights': 8}
}

# Define meeting constraints
meeting_constraints = {
    'Stephanie': {'location': 'Golden Gate Park','start_time': '11:00', 'end_time': '15:00', 'duration': 105},
    'Karen': {'location': 'Chinatown','start_time': '13:45', 'end_time': '16:30', 'duration': 15},
    'Brian': {'location': 'Union Square','start_time': '15:00', 'end_time': '17:15', 'duration': 30},
    'Rebecca': {'location': 'Fisherman\'s Wharf','start_time': '08:00', 'end_time': '11:15', 'duration': 30},
    'Joseph': {'location': 'Pacific Heights','start_time': '08:15', 'end_time': '09:30', 'duration': 60},
    'Steven': {'location': 'North Beach','start_time': '14:30', 'end_time': '20:45', 'duration': 120}
}

def calculate_meeting_schedule():
    # Initialize the schedule
    schedule = []
    current_location = 'Financial District'
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