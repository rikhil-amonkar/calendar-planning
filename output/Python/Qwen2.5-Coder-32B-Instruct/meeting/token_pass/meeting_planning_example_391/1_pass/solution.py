import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    'Sunset District': {'Alamo Square': 17, 'Russian Hill': 24, 'Presidio': 16, 'Financial District': 30},
    'Alamo Square': {'Sunset District': 16, 'Russian Hill': 13, 'Presidio': 18, 'Financial District': 17},
    'Russian Hill': {'Sunset District': 23, 'Alamo Square': 15, 'Presidio': 14, 'Financial District': 11},
    'Presidio': {'Sunset District': 15, 'Alamo Square': 18, 'Russian Hill': 14, 'Financial District': 23},
    'Financial District': {'Sunset District': 31, 'Alamo Square': 17, 'Russian Hill': 10, 'Presidio': 22}
}

# Define friends' availability and required meeting times
friends_availability = {
    'Kevin': {'start': '8:15', 'end': '21:30', 'duration': 75},
    'Kimberly': {'start': '8:45', 'end': '12:30', 'duration': 30},
    'Joseph': {'start': '18:30', 'end': '19:15', 'duration': 45},
    'Thomas': {'start': '19:00', 'end': '21:45', 'duration': 45}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')  # Remove leading zero for hours

def can_meet(start_time, end_time, required_duration):
    return (end_time - start_time).total_seconds() / 60 >= required_duration

def find_optimal_schedule():
    current_location = 'Sunset District'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort friends by their earliest availability to prioritize earlier meetings
    sorted_friends = sorted(friends_availability.items(), key=lambda x: parse_time(x[1]['start']))

    for friend, details in sorted_friends:
        friend_start = parse_time(details['start'])
        friend_end = parse_time(details['end'])
        required_duration = details['duration']

        # Calculate the earliest possible meeting time considering travel time
        travel_time = travel_times[current_location][details['start'].split()[0]]
        earliest_meeting_start = current_time + timedelta(minutes=travel_time)

        # Check if we can meet the friend within their availability
        if earliest_meeting_start < friend_start:
            earliest_meeting_start = friend_start

        meeting_end = earliest_meeting_start + timedelta(minutes=required_duration)

        # Ensure the meeting ends before the friend's availability ends
        if meeting_end <= friend_end:
            itinerary.append({
                "action": "meet",
                "location": details['start'].split()[0],
                "person": friend,
                "start_time": format_time(earliest_meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = details['start'].split()[0]

    return itinerary

optimal_itinerary = find_optimal_schedule()
result = {"itinerary": optimal_itinerary}
print(json.dumps(result, indent=2))