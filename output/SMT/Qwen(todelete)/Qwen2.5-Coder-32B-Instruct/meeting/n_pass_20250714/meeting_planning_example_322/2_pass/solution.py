from z3 import *

# Define the locations
locations = ['Sunset District', 'Russian Hill', 'Chinatown', 'Presidio', 'Fisherman\'s Wharf']

# Define the travel times
travel_times = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Presidio'): 17
}

# Define the friends' availability and meeting times
friends_availability = {
    'William': {'location': 'Russian Hill', 'start': 18*60 + 30, 'end': 20*60 + 45, 'min_meeting_time': 105},
    'Michelle': {'location': 'Chinatown', 'start': 8*60 + 15, 'end': 14*60, 'min_meeting_time': 15},
    'George': {'location': 'Presidio', 'start': 10*60 + 30, 'end': 18*60 + 45, 'min_meeting_time': 30},
    'Robert': {'location': 'Fisherman\'s Wharf', 'start': 9*60, 'end': 13*60 + 45, 'min_meeting_time': 30}
}

# Create a solver instance
solver = Solver()

# Define variables for the start time at each location
start_times = {loc: Int(f'start_{loc}') for loc in locations}

# Define variables for meeting each friend
meet_william = Bool('meet_william')
meet_michelle = Bool('meet_michelle')
meet_george = Bool('meet_george')
meet_robert = Bool('meet_robert')

# Add constraint for starting at Sunset District at 9:00 AM
solver.add(start_times['Sunset District'] == 9*60)

# Add constraints for travel times
for (loc1, loc2), time in travel_times.items():
    solver.add(start_times[loc2] >= start_times[loc1] + time)

# Add constraints for meeting friends
def add_meeting_constraints(friend, info, meet_var):
    loc = info['location']
    start = info['start']
    end = info['end']
    min_meeting_time = info['min_meeting_time']
    # Ensure we arrive at the location before the friend leaves and leave after the friend arrives
    solver.add(Implies(meet_var, start_times[loc] <= end - min_meeting_time))
    solver.add(Implies(meet_var, start_times[loc] + min_meeting_time >= start))

add_meeting_constraints('William', friends_availability['William'], meet_william)
add_meeting_constraints('Michelle', friends_availability['Michelle'], meet_michelle)
add_meeting_constraints('George', friends_availability['George'], meet_george)
add_meeting_constraints('Robert', friends_availability['Robert'], meet_robert)

# Ensure we meet exactly 4 people
solver.add(meet_william + meet_michelle + meet_george + meet_robert == 4)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = {loc: model[start_times[loc]].as_long() // 60 for loc in locations}
    print("SOLUTION:")
    for loc, time in sorted(schedule.items()):
        print(f"{loc}: {time}:{model[start_times[loc]].as_long() % 60:02}")
    print("Meetings:")
    if model[meet_william]:
        print("William at Russian Hill")
    if model[meet_michelle]:
        print("Michelle at Chinatown")
    if model[meet_george]:
        print("George at Presidio")
    if model[meet_robert]:
        print("Robert at Fisherman's Wharf")
else:
    print("No solution found")