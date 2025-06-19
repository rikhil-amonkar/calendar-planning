import itertools
import json

def time_to_minutes(time_str):
    if time_str.endswith("AM") or time_str.endswith("PM"):
        time_part = time_str[:-2]
        period = time_str[-2:]
        hour, minute = map(int, time_part.split(':'))
        if period == "PM" and hour != 12:
            hour += 12
        if period == "AM" and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        hour, minute = map(int, time_str.split(':'))
        return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times dictionary
travel_times = {
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Fisherman\'s Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Alamo Square': 5,
        'Pacific Heights': 12
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Nob Hill': 5,
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Pacific Heights': 7
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Alamo Square': 20,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'Fisherman\'s Wharf': 11,
        'Golden Gate Park': 17,
        'Alamo Square': 11,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Russian Hill': 19,
        'Fisherman\'s Wharf': 24,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'Pacific Heights': 16
    },
    'Alamo Square': {
        'Haight-Ashbury': 5,
        'Russian Hill': 13,
        'Fisherman\'s Wharf': 19,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Russian Hill': 7,
        'Fisherman\'s Wharf': 13,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Alamo Square': 10
    }
}

# Define friends with constraints
friends = [
    {'name': 'Stephanie', 'location': 'Russian Hill', 'available_start': time_to_minutes("8:00PM"), 'available_end': time_to_minutes("8:45PM"), 'min_duration': 15},
    {'name': 'Kevin', 'location': 'Fisherman\'s Wharf', 'available_start': time_to_minutes("7:15PM"), 'available_end': time_to_minutes("9:45PM"), 'min_duration': 75},
    {'name': 'Robert', 'location': 'Nob Hill', 'available_start': time_to_minutes("7:45AM"), 'available_end': time_to_minutes("10:30AM"), 'min_duration': 90},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'available_start': time_to_minutes("8:30AM"), 'available_end': time_to_minutes("5:00PM"), 'min_duration': 75},
    {'name': 'Anthony', 'location': 'Alamo Square', 'available_start': time_to_minutes("7:45AM"), 'available_end': time_to_minutes("7:45PM"), 'min_duration': 15},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'available_start': time_to_minutes("2:45PM"), 'available_end': time_to_minutes("9:45PM"), 'min_duration': 45}
]

start_time = time_to_minutes("9:00AM")
start_location = 'Haight-Ashbury'

best_count = 0
best_itinerary = None

for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    count = 0
    for friend in perm:
        travel = travel_times[current_location][friend.location]
        current_time += travel
        start_meeting = max(current_time, friend.available_start)
        if start_meeting + friend.min_duration <= friend.available_end:
            end_meeting = start_meeting + friend.min_duration
            itinerary.append({
                'action': 'meet',
                'location': friend.location,
                'person': friend.name,
                'start_time': minutes_to_time(start_meeting),
                'end_time': minutes_to_time(end_meeting)
            })
            current_time = end_meeting
            current_location = friend.location
            count += 1
        else:
            # Skip meeting, but we are at the friend's location
            pass
    if count > best_count:
        best_count = count
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result))