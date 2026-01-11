import json
from datetime import datetime, timedelta

# Travel times between locations
travel_times = {
    'Fisherman\'s Wharf': {'Golden Gate Park': 25, 'Presidio': 17, 'Richmond District': 18},
    'Golden Gate Park': {'Fisherman\'s Wharf': 24, 'Presidio': 11, 'Richmond District': 7},
    'Presidio': {'Fisherman\'s Wharf': 19, 'Golden Gate Park': 12, 'Richmond District': 7},
    'Richmond District': {'Fisherman\'s Wharf': 18, 'Golden Gate Park': 9, 'Presidio': 7}
}

# Friends' availability and meeting durations
friends_availability = {
    'Melissa': {'start': '8:30', 'end': '20:00', 'min_duration': 15},
    'Nancy': {'start': '19:45', 'end': '22:00', 'min_duration': 105},
    'Emily': {'start': '16:45', 'end': '22:00', 'min_duration': 120}
}

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def format_time(time_obj):
    return time_obj.strftime('%H:%M').lstrip('0')

def can_meet(current_time, friend_info):
    friend_start = parse_time(friend_info['start'])
    friend_end = parse_time(friend_info['end'])
    min_duration = friend_info['min_duration']
    return current_time + timedelta(minutes=min_duration) <= friend_end

def find_optimal_schedule():
    current_location = 'Fisherman\'s Wharf'
    current_time = parse_time('9:00')
    itinerary = []

    # Sort friends by their earliest availability
    sorted_friends = sorted(friends_availability.items(), key=lambda x: parse_time(x[1]['start']))

    for friend_name, friend_info in sorted_friends:
        friend_start = parse_time(friend_info['start'])
        friend_end = parse_time(friend_info['end'])
        min_duration = friend_info['min_duration']

        # Calculate the earliest possible start time for meeting this friend
        travel_time = travel_times[current_location][friend_info.get('location', friend_name)]
        proposed_start_time = max(current_time + timedelta(minutes=travel_time), friend_start)

        if can_meet(proposed_start_time, friend_info):
            meeting_start = proposed_start_time
            meeting_end = meeting_start + timedelta(minutes=min_duration)
            itinerary.append({
                "action": "meet",
                "location": friend_name.replace(' ', '\'s ') + ' District' if friend_name == 'Emily' else friend_name.replace(' ', ' ') + ' Park' if friend_name == 'Melissa' else friend_name + ' District',
                "person": friend_name,
                "start_time": format_time(meeting_start),
                "end_time": format_time(meeting_end)
            })
            current_location = friend_name.replace(' ', '\'s ') + ' District' if friend_name == 'Emily' else friend_name.replace(' ', ' ') + ' Park' if friend_name == 'Melissa' else friend_name + ' District'
            current_time = meeting_end

    return itinerary

optimal_schedule = find_optimal_schedule()
result = {"itinerary": optimal_schedule}
print(json.dumps(result, indent=2))