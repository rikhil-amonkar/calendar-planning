import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%I:%M%p')

def format_time(dt):
    return dt.strftime('%-I:%M%p')

def add_minutes(time_str, minutes):
    dt = parse_time(time_str)
    dt += timedelta(minutes=minutes)
    return format_time(dt)

def calculate_schedule():
    # Travel times dictionary
    travel_times = {
        'Financial District': {
            'Golden Gate Park': 23,
            'Chinatown': 5,
            'Union Square': 9,
            'Fisherman\'s Wharf': 10,
            'Pacific Heights': 13,
            'North Beach': 7
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Chinatown': 23,
            'Union Square': 22,
            'Fisherman\'s Wharf': 24,
            'Pacific Heights': 16,
            'North Beach': 24
        },
        'Chinatown': {
            'Financial District': 5,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Fisherman\'s Wharf': 8,
            'Pacific Heights': 10,
            'North Beach': 3
        },
        'Union Square': {
            'Financial District': 9,
            'Golden Gate Park': 22,
            'Chinatown': 7,
            'Fisherman\'s Wharf': 15,
            'Pacific Heights': 15,
            'North Beach': 10
        },
        'Fisherman\'s Wharf': {
            'Financial District': 11,
            'Golden Gate Park': 25,
            'Chinatown': 12,
            'Union Square': 13,
            'Pacific Heights': 12,
            'North Beach': 6
        },
        'Pacific Heights': {
            'Financial District': 13,
            'Golden Gate Park': 15,
            'Chinatown': 11,
            'Union Square': 12,
            'Fisherman\'s Wharf': 13,
            'North Beach': 9
        },
        'North Beach': {
            'Financial District': 8,
            'Golden Gate Park': 22,
            'Chinatown': 6,
            'Union Square': 7,
            'Fisherman\'s Wharf': 5,
            'Pacific Heights': 8
        }
    }

    # Constraints
    constraints = [
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': '11:00AM', 'end': '3:00PM', 'duration': 105},
        {'name': 'Karen', 'location': 'Chinatown', 'start': '1:45PM', 'end': '4:30PM', 'duration': 15},
        {'name': 'Brian', 'location': 'Union Square', 'start': '3:00PM', 'end': '5:15PM', 'duration': 30},
        {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': '8:00AM', 'end': '11:15AM', 'duration': 30},
        {'name': 'Joseph', 'location': 'Pacific Heights', 'start': '8:15AM', 'end': '9:30AM', 'duration': 60},
        {'name': 'Steven', 'location': 'North Beach', 'start': '2:30PM', 'end': '8:45PM', 'duration': 120}
    ]

    current_location = 'Financial District'
    current_time = '9:00AM'
    schedule = [{'action': 'start', 'location': current_location, 'time': current_time}]

    # Sort constraints by start time
    constraints.sort(key=lambda x: parse_time(x['start']))

    # Process each constraint
    for constraint in constraints:
        location = constraint['location']
        start_time = constraint['start']
        end_time = constraint['end']
        duration = constraint['duration']

        # Travel to the location
        travel_duration = travel_times[current_location][location]
        arrival_time = add_minutes(current_time, travel_duration)
        schedule.append({
            'action': 'travel',
            'location': current_location,
            'duration': travel_duration,
            'time': current_time,
            'to': location
        })

        # Check if we arrive before the start time
        if parse_time(arrival_time) < parse_time(start_time):
            # Wait until start time
            schedule.append({
                'action': 'wait',
                'location': location,
                'time': arrival_time
            })
            meeting_start = start_time
        else:
            meeting_start = arrival_time

        # Check if we can meet for the duration
        meeting_end = add_minutes(meeting_start, duration)
        if parse_time(meeting_end) > parse_time(end_time):
            # Can't meet for full duration, adjust
            meeting_end = end_time
            actual_duration = (parse_time(meeting_end) - parse_time(meeting_start)).total_seconds() / 60
            if actual_duration <= 0:
                continue  # Skip if no time to meet
            duration = int(actual_duration)

        # Add meeting to schedule
        schedule.append({
            'action': 'meet',
            'location': location,
            'duration': duration,
            'time': meeting_start
        })

        current_location = location
        current_time = meeting_end

    return {'schedule': schedule}

# Calculate and output the schedule
result = calculate_schedule()
print(json.dumps(result, indent=2))