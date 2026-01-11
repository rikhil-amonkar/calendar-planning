import json
from datetime import datetime, timedelta

# Define the travel graph
travel_times = {
    'Union Square': {'The Castro': 17, 'North Beach': 10, 'Embarcadero': 11, 'Alamo Square': 15, 'Nob Hill': 9, 'Presidio': 24, 'Fisherman\'s Wharf': 15, 'Mission District': 14, 'Haight-Ashbury': 18},
    'The Castro': {'Union Square': 19, 'North Beach': 20, 'Embarcadero': 22, 'Alamo Square': 8, 'Nob Hill': 16, 'Presidio': 20, 'Fisherman\'s Wharf': 24, 'Mission District': 7, 'Haight-Ashbury': 6},
    'North Beach': {'Union Square': 7, 'The Castro': 23, 'Embarcadero': 6, 'Alamo Square': 16, 'Nob Hill': 7, 'Presidio': 17, 'Fisherman\'s Wharf': 5, 'Mission District': 18, 'Haight-Ashbury': 18},
    'Embarcadero': {'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Alamo Square': 19, 'Nob Hill': 10, 'Presidio': 20, 'Fisherman\'s Wharf': 6, 'Mission District': 20, 'Haight-Ashbury': 21},
    'Alamo Square': {'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Embarcadero': 16, 'Nob Hill': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 19, 'Mission District': 10, 'Haight-Ashbury': 5},
    'Nob Hill': {'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Embarcadero': 9, 'Alamo Square': 11, 'Presidio': 17, 'Fisherman\'s Wharf': 10, 'Mission District': 13, 'Haight-Ashbury': 13},
    'Presidio': {'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Embarcadero': 20, 'Alamo Square': 19, 'Nob Hill': 18, 'Fisherman\'s Wharf': 19, 'Mission District': 26, 'Haight-Ashbury': 15},
    'Fisherman\'s Wharf': {'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Embarcadero': 8, 'Alamo Square': 21, 'Nob Hill': 11, 'Presidio': 17, 'Mission District': 22, 'Haight-Ashbury': 22},
    'Mission District': {'Union Square': 15, 'The Castro': 7, 'North Beach': 17, 'Embarcadero': 19, 'Alamo Square': 11, 'Nob Hill': 12, 'Presidio': 25, 'Fisherman\'s Wharf': 22, 'Haight-Ashbury': 12},
    'Haight-Ashbury': {'Union Square': 19, 'The Castro': 6, 'North Beach': 19, 'Embarcadero': 20, 'Alamo Square': 5, 'Nob Hill': 15, 'Presidio': 15, 'Fisherman\'s Wharf': 23, 'Mission District': 11}
}

# Define constraints
constraints = [
    {'name': 'Kimberly', 'location': 'North Beach', 'start': '7:00', 'end': '10:30', 'duration': 15},
    {'name': 'Brian', 'location': 'Fisherman\'s Wharf', 'start': '9:30', 'end': '13:30', 'duration': 45},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': '12:15', 'end': '17:15', 'duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'start': '16:30', 'end': '18:15', 'duration': 105},
    {'name': 'Joseph', 'location': 'Embarcadero', 'start': '15:30', 'end': '19:30', 'duration': 75},
    {'name': 'Steven', 'location': 'Mission District', 'start': '19:30', 'end': '21:00', 'duration': 90},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'start': '19:00', 'end': '20:30', 'duration': 90},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': '20:45', 'end': '21:45', 'duration': 15},
    {'name': 'Melissa', 'location': 'The Castro', 'start': '20:15', 'end': '21:15', 'duration': 30}
]

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def can_meet(schedule, constraint, current_time):
    start = parse_time(constraint['start'])
    end = parse_time(constraint['end'])
    required_duration = timedelta(minutes=constraint['duration'])
    if current_time + required_duration > end:
        return False
    return True

def dfs(current_location, current_time, visited, schedule):
    global best_schedule
    if len(visited) == len(constraints):
        if len(schedule) > len(best_schedule):
            best_schedule = schedule[:]
        return
    
    for constraint in constraints:
        if constraint['name'] in visited:
            continue
        if constraint['location'] == current_location and can_meet(schedule, constraint, current_time):
            new_time = current_time + timedelta(minutes=constraint['duration'])
            schedule.append({
                'action': 'meet',
                'location': constraint['location'],
                'person': constraint['name'],
                'start_time': current_time.strftime('%H:%M'),
                'end_time': new_time.strftime('%H:%M')
            })
            visited.add(constraint['name'])
            dfs(constraint['location'], new_time, visited, schedule)
            visited.remove(constraint['name'])
            schedule.pop()
    
    for next_location, travel_time in travel_times[current_location].items():
        new_time = current_time + timedelta(minutes=travel_time)
        if new_time.hour >= 21:  # Stop exploring after 9 PM
            continue
        dfs(next_location, new_time, visited, schedule)

# Initialize best schedule
best_schedule = []

# Start DFS from Union Square at 9:00 AM
dfs('Union Square', parse_time('9:00'), set(), [])

# Output the best schedule as JSON
output = {'itinerary': best_schedule}
print(json.dumps(output, indent=2))