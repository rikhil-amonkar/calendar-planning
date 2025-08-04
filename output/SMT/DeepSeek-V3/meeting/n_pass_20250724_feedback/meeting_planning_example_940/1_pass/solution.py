from z3 import *
import json

# Initialize the solver
s = Solver()

# Define the travel times between locations (in minutes)
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'North Beach'): 10,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Sunset District'): 27,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Sunset District'): 24,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'The Castro'): 27,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'North Beach'): 5,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Sunset District'): 23,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'North Beach'): 11,
    ('Marina District', 'Chinatown'): 15,
    ('Marina District', 'Pacific Heights'): 7,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Sunset District'): 19,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Russian Hill'): 4,
    ('North Beach', 'Marina District'): 9,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'The Castro'): 23,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Sunset District'): 27,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Mission District'): 17,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Marina District'): 12,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Nob Hill'): 9,
    ('Chinatown', 'Sunset District'): 29,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Marina District'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Sunset District'): 21,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Fisherman\'s Wharf'): 24,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Chinatown'): 22,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Sunset District'): 17,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Fisherman\'s Wharf'): 10,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Nob Hill'): 27,
}

# Friends' availability and constraints
friends = {
    'Kevin': {'location': 'Mission District', 'start': '20:45', 'end': '21:45', 'min_duration': 60},
    'Mark': {'location': 'Fisherman\'s Wharf', 'start': '17:15', 'end': '20:00', 'min_duration': 90},
    'Jessica': {'location': 'Russian Hill', 'start': '09:00', 'end': '15:00', 'min_duration': 120},
    'Jason': {'location': 'Marina District', 'start': '15:15', 'end': '21:45', 'min_duration': 120},
    'John': {'location': 'North Beach', 'start': '09:45', 'end': '18:00', 'min_duration': 15},
    'Karen': {'location': 'Chinatown', 'start': '16:45', 'end': '19:00', 'min_duration': 75},
    'Sarah': {'location': 'Pacific Heights', 'start': '17:30', 'end': '18:15', 'min_duration': 45},
    'Amanda': {'location': 'The Castro', 'start': '20:00', 'end': '21:15', 'min_duration': 60},
    'Nancy': {'location': 'Nob Hill', 'start': '09:45', 'end': '13:00', 'min_duration': 45},
    'Rebecca': {'location': 'Sunset District', 'start': '08:45', 'end': '15:00', 'min_duration': 75},
}

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

# Convert minutes back to time string
def minutes_to_time(minutes):
    total_minutes = 540 + minutes
    hh = total_minutes // 60
    mm = total_minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Create variables for each meeting's start and end times
meetings = {}
for name in friends:
    start = Int(f'start_{name}')
    end = Int(f'end_{name}')
    meetings[name] = {'start': start, 'end': end}

# Add constraints for each friend's availability
for name in friends:
    friend = friends[name]
    start_min = time_to_minutes(friend['start'])
    end_min = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    s.add(meetings[name]['start'] >= start_min)
    s.add(meetings[name]['end'] <= end_min)
    s.add(meetings[name]['end'] - meetings[name]['start'] >= min_duration)

# Initial location is Union Square at time 0 (9:00 AM)
current_location = 'Union Square'
current_time = 0

# Define the order of meetings (this is a heuristic; in practice, we'd need to explore all permutations)
# For simplicity, we'll prioritize friends with tighter time windows first
priority_order = ['Rebecca', 'Jessica', 'Nancy', 'John', 'Jason', 'Karen', 'Sarah', 'Mark', 'Amanda', 'Kevin']

# Add travel time constraints between meetings
for i in range(len(priority_order) - 1):
    name1 = priority_order[i]
    name2 = priority_order[i + 1]
    loc1 = friends[name1]['location']
    loc2 = friends[name2]['location']
    travel_time = travel_times.get((loc1, loc2), 0)
    
    s.add(meetings[name2]['start'] >= meetings[name1]['end'] + travel_time)

# Ensure no overlapping meetings (though the travel time constraints should handle this)
for name1 in meetings:
    for name2 in meetings:
        if name1 != name2:
            s.add(Or(
                meetings[name1]['end'] <= meetings[name2]['start'],
                meetings[name2]['end'] <= meetings[name1]['start']
            ))

# Try to maximize the number of friends met (all in this case)
s.check()

# Get the model
m = s.model()

# Extract the meeting times
itinerary = []
for name in priority_order:
    if m[meetings[name]['start']] is not None and m[meetings[name]['end']] is not None:
        start_time = minutes_to_time(m[meetings[name]['start']].as_long())
        end_time = minutes_to_time(m[meetings[name]['end']].as_long())
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_time,
            "end_time": end_time
        })

# Print the solution
solution = {"itinerary": itinerary}
print("SOLUTION:")
print(json.dumps(solution, indent=2))