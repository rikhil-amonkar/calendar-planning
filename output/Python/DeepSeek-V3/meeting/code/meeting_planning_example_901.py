import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%I:%M%p')

def format_time(dt):
    return dt.strftime('%-H:%M')

def calculate_schedule():
    # Initialize travel times as a dictionary of dictionaries
    travel_times = {
        'Russian Hill': {
            'Pacific Heights': 7,
            'North Beach': 5,
            'Golden Gate Park': 21,
            'Embarcadero': 8,
            'Haight-Ashbury': 17,
            'Fisherman\'s Wharf': 7,
            'Mission District': 16,
            'Alamo Square': 15,
            'Bayview': 23,
            'Richmond District': 14
        },
        'Pacific Heights': {
            'Russian Hill': 7,
            'North Beach': 9,
            'Golden Gate Park': 15,
            'Embarcadero': 10,
            'Haight-Ashbury': 11,
            'Fisherman\'s Wharf': 13,
            'Mission District': 15,
            'Alamo Square': 10,
            'Bayview': 22,
            'Richmond District': 12
        },
        'North Beach': {
            'Russian Hill': 4,
            'Pacific Heights': 8,
            'Golden Gate Park': 22,
            'Embarcadero': 6,
            'Haight-Ashbury': 18,
            'Fisherman\'s Wharf': 5,
            'Mission District': 18,
            'Alamo Square': 16,
            'Bayview': 25,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Russian Hill': 19,
            'Pacific Heights': 16,
            'North Beach': 23,
            'Embarcadero': 25,
            'Haight-Ashbury': 7,
            'Fisherman\'s Wharf': 24,
            'Mission District': 17,
            'Alamo Square': 9,
            'Bayview': 23,
            'Richmond District': 7
        },
        'Embarcadero': {
            'Russian Hill': 8,
            'Pacific Heights': 11,
            'North Beach': 5,
            'Golden Gate Park': 25,
            'Haight-Ashbury': 21,
            'Fisherman\'s Wharf': 6,
            'Mission District': 20,
            'Alamo Square': 19,
            'Bayview': 21,
            'Richmond District': 21
        },
        'Haight-Ashbury': {
            'Russian Hill': 17,
            'Pacific Heights': 12,
            'North Beach': 19,
            'Golden Gate Park': 7,
            'Embarcadero': 20,
            'Fisherman\'s Wharf': 23,
            'Mission District': 11,
            'Alamo Square': 5,
            'Bayview': 18,
            'Richmond District': 10
        },
        'Fisherman\'s Wharf': {
            'Russian Hill': 7,
            'Pacific Heights': 12,
            'North Beach': 6,
            'Golden Gate Park': 25,
            'Embarcadero': 8,
            'Haight-Ashbury': 22,
            'Mission District': 22,
            'Alamo Square': 21,
            'Bayview': 26,
            'Richmond District': 18
        },
        'Mission District': {
            'Russian Hill': 15,
            'Pacific Heights': 16,
            'North Beach': 17,
            'Golden Gate Park': 17,
            'Embarcadero': 19,
            'Haight-Ashbury': 12,
            'Fisherman\'s Wharf': 22,
            'Alamo Square': 11,
            'Bayview': 14,
            'Richmond District': 20
        },
        'Alamo Square': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 15,
            'Golden Gate Park': 9,
            'Embarcadero': 16,
            'Haight-Ashbury': 5,
            'Fisherman\'s Wharf': 19,
            'Mission District': 10,
            'Bayview': 16,
            'Richmond District': 11
        },
        'Bayview': {
            'Russian Hill': 23,
            'Pacific Heights': 23,
            'North Beach': 22,
            'Golden Gate Park': 22,
            'Embarcadero': 19,
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 25,
            'Mission District': 13,
            'Alamo Square': 16,
            'Richmond District': 27
        },
        'Richmond District': {
            'Russian Hill': 13,
            'Pacific Heights': 10,
            'North Beach': 17,
            'Golden Gate Park': 9,
            'Embarcadero': 19,
            'Haight-Ashbury': 10,
            'Fisherman\'s Wharf': 18,
            'Mission District': 20,
            'Alamo Square': 13,
            'Bayview': 27
        }
    }

    # Initialize meeting constraints
    constraints = [
        {'person': 'Emily', 'location': 'Pacific Heights', 'start': parse_time('9:15AM'), 'end': parse_time('1:45PM'), 'duration': 120},
        {'person': 'Helen', 'location': 'North Beach', 'start': parse_time('1:45PM'), 'end': parse_time('6:45PM'), 'duration': 30},
        {'person': 'Kimberly', 'location': 'Golden Gate Park', 'start': parse_time('6:45PM'), 'end': parse_time('9:15PM'), 'duration': 75},
        {'person': 'James', 'location': 'Embarcadero', 'start': parse_time('10:30AM'), 'end': parse_time('11:30AM'), 'duration': 30},
        {'person': 'Linda', 'location': 'Haight-Ashbury', 'start': parse_time('7:30AM'), 'end': parse_time('7:15PM'), 'duration': 15},
        {'person': 'Paul', 'location': 'Fisherman\'s Wharf', 'start': parse_time('2:45PM'), 'end': parse_time('6:45PM'), 'duration': 90},
        {'person': 'Anthony', 'location': 'Mission District', 'start': parse_time('8:00AM'), 'end': parse_time('2:45PM'), 'duration': 105},
        {'person': 'Nancy', 'location': 'Alamo Square', 'start': parse_time('8:30AM'), 'end': parse_time('1:45PM'), 'duration': 120},
        {'person': 'William', 'location': 'Bayview', 'start': parse_time('5:30PM'), 'end': parse_time('8:30PM'), 'duration': 120},
        {'person': 'Margaret', 'location': 'Richmond District', 'start': parse_time('3:15PM'), 'end': parse_time('6:15PM'), 'duration': 45}
    ]

    # Current time and location
    current_time = parse_time('9:00AM')
    current_location = 'Russian Hill'
    itinerary = []

    # Sort constraints by priority (earlier meetings first, then longer durations)
    constraints.sort(key=lambda x: (x['start'], -x['duration']))

    for constraint in constraints:
        person = constraint['person']
        location = constraint['location']
        start = constraint['start']
        end = constraint['end']
        duration = constraint['duration']

        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + timedelta(minutes=travel_time)

        # Check if we can make it before the meeting window closes
        if arrival_time > end:
            continue  # Can't make it in time

        # Determine the actual meeting start time
        meeting_start = max(arrival_time, start)
        meeting_end = meeting_start + timedelta(minutes=duration)

        # Check if the meeting can fit within the window
        if meeting_end > end:
            continue  # Not enough time for this meeting

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        })

        # Update current time and location
        current_time = meeting_end
        current_location = location

    return {'itinerary': itinerary}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))