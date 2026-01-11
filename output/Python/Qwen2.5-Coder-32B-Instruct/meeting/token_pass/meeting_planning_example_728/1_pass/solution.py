import json
from datetime import datetime, timedelta

# Define travel times as a graph
travel_times = {
    'Marina District': {'Mission District': 20, 'Fisherman\'s Wharf': 10, 'Presidio': 10, 'Union Square': 16, 'Sunset District': 19, 'Financial District': 17, 'Haight-Ashbury': 16, 'Russian Hill': 8},
    'Mission District': {'Marina District': 19, 'Fisherman\'s Wharf': 22, 'Presidio': 25, 'Union Square': 15, 'Sunset District': 24, 'Financial District': 15, 'Haight-Ashbury': 12, 'Russian Hill': 15},
    'Fisherman\'s Wharf': {'Marina District': 9, 'Mission District': 22, 'Presidio': 17, 'Union Square': 13, 'Sunset District': 27, 'Financial District': 11, 'Haight-Ashbury': 22, 'Russian Hill': 7},
    'Presidio': {'Marina District': 11, 'Mission District': 26, 'Fisherman\'s Wharf': 19, 'Union Square': 22, 'Sunset District': 15, 'Financial District': 23, 'Haight-Ashbury': 15, 'Russian Hill': 14},
    'Union Square': {'Marina District': 18, 'Mission District': 14, 'Fisherman\'s Wharf': 15, 'Presidio': 24, 'Sunset District': 27, 'Financial District': 9, 'Haight-Ashbury': 18, 'Russian Hill': 13},
    'Sunset District': {'Marina District': 21, 'Mission District': 25, 'Fisherman\'s Wharf': 29, 'Presidio': 16, 'Union Square': 30, 'Financial District': 30, 'Haight-Ashbury': 15, 'Russian Hill': 24},
    'Financial District': {'Marina District': 15, 'Mission District': 17, 'Fisherman\'s Wharf': 10, 'Presidio': 22, 'Union Square': 9, 'Sunset District': 30, 'Haight-Ashbury': 19, 'Russian Hill': 11},
    'Haight-Ashbury': {'Marina District': 17, 'Mission District': 11, 'Fisherman\'s Wharf': 23, 'Presidio': 15, 'Union Square': 19, 'Sunset District': 15, 'Financial District': 21, 'Russian Hill': 17},
    'Russian Hill': {'Marina District': 7, 'Mission District': 16, 'Fisherman\'s Wharf': 7, 'Presidio': 14, 'Union Square': 10, 'Sunset District': 23, 'Financial District': 11, 'Haight-Ashbury': 17}
}

# Define constraints
constraints = {
    'Karen': {'location': 'Mission District', 'start': '14:15', 'end': '22:00', 'min_duration': 30},
    'Richard': {'location': 'Fisherman\'s Wharf', 'start': '14:30', 'end': '17:30', 'min_duration': 30},
    'Robert': {'location': 'Presidio', 'start': '21:45', 'end': '22:45', 'min_duration': 60},
    'Joseph': {'location': 'Union Square', 'start': '11:45', 'end': '14:45', 'min_duration': 120},
    'Helen': {'location': 'Sunset District', 'start': '14:45', 'end': '20:45', 'min_duration': 105},
    'Elizabeth': {'location': 'Financial District', 'start': '10:00', 'end': '12:45', 'min_duration': 75},
    'Kimberly': {'location': 'Haight-Ashbury', 'start': '14:15', 'end': '17:30', 'min_duration': 105},
    'Ashley': {'location': 'Russian Hill', 'start': '11:30', 'end': '21:30', 'min_duration': 45}
}

# Convert time strings to minutes since midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Generate possible meeting slots for each person
def generate_meeting_slots(constraints):
    slots = []
    for name, data in constraints.items():
        start = time_to_minutes(data['start'])
        end = time_to_minutes(data['end'])
        min_duration = data['min_duration']
        location = data['location']
        for t in range(start, end - min_duration + 1):
            slots.append((name, location, t, t + min_duration))
    return slots

# Check if a meeting can be added to the current schedule
def can_add_meeting(current_schedule, new_meeting, travel_times):
    if not current_schedule:
        return True
    last_meeting = current_schedule[-1]
    last_end_time = last_meeting[2] + last_meeting[3]
    travel_time = travel_times[last_meeting[1]][new_meeting[1]]
    if last_end_time + travel_time > new_meeting[2]:
        return False
    return True

# Recursive function to find the best schedule
def find_best_schedule(slots, current_schedule, best_schedule, travel_times):
    if len(current_schedule) > len(best_schedule):
        best_schedule[:] = current_schedule[:]
    for slot in slots:
        if can_add_meeting(current_schedule, slot, travel_times):
            current_schedule.append(slot)
            find_best_schedule(slots, current_schedule, best_schedule, travel_times)
            current_schedule.pop()

# Main function to compute the optimal schedule
def compute_optimal_schedule(travel_times, constraints):
    slots = generate_meeting_slots(constraints)
    slots.sort(key=lambda x: x[2])  # Sort slots by start time
    best_schedule = []
    find_best_schedule(slots, [], best_schedule, travel_times)
    
    # Convert best schedule to the required JSON format
    itinerary = []
    current_time = time_to_minutes('9:00')
    for meeting in best_schedule:
        name, location, start, duration = meeting
        if current_time != start:
            itinerary.append({"action": "travel", "location": location, "start_time": f"{current_time // 60}:{current_time % 60:02}", "end_time": f"{start // 60}:{start % 60:02}"})
        itinerary.append({"action": "meet", "location": location, "person": name, "start_time": f"{start // 60}:{start % 60:02}", "end_time": f"{(start + duration) // 60}:{(start + duration) % 60:02}"})
        current_time = start + duration
    
    return json.dumps({"itinerary": itinerary}, indent=2)

# Compute and print the optimal schedule
optimal_schedule = compute_optimal_schedule(travel_times, constraints)
print(optimal_schedule)