from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times
travel_times = {
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Financial District'): 19,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Presidio'): 22,
}

# Define the available times for each person
available_times = {
    'Mary': (time_in_minutes(8, 45), time_in_minutes(11, 45)),
    'Kevin': (time_in_minutes(10, 15), time_in_minutes(16, 15)),
    'Deborah': (time_in_minutes(15, 0), time_in_minutes(19, 15)),
    'Stephanie': (time_in_minutes(10, 0), time_in_minutes(17, 15)),
    'Emily': (time_in_minutes(11, 30), time_in_minutes(21, 45)),
}

# Define the minimum meeting times
min_meeting_times = {
    'Mary': 45,
    'Kevin': 90,
    'Deborah': 120,
    'Stephanie': 120,
    'Emily': 105,
}

# Define the solver
solver = Solver()

# Define the variables
locations = ['Embarcadero', 'Golden Gate Park', 'Haight-Ashbury', 'Bayview', 'Presidio', 'Financial District']
people = ['Mary', 'Kevin', 'Deborah', 'Stephanie', 'Emily']

# Define the start and end times for each meeting
start_times = {person: Int(f'start_{person}') for person in people}
end_times = {person: Int(f'end_{person}') for person in people}

# Define the location for each meeting
meeting_locations = {person: String(f'location_{person}') for person in people}

# Define the current location and time
current_location = 'Embarcadero'
current_time = 0

# Add constraints for each person
for i, person in enumerate(people):
    start, end = available_times[person]
    min_meeting_time = min_meeting_times[person]
    
    # Meeting must start and end within the available time
    solver.add(start_times[person] >= start)
    solver.add(end_times[person] <= end)
    
    # Meeting must last at least the minimum meeting time
    solver.add(end_times[person] - start_times[person] >= min_meeting_time)
    
    # Travel time constraints
    if i > 0:
        prev_person = people[i - 1]
        travel_time = Int(f'travel_time_{prev_person}_{person}')
        solver.add(travel_time == travel_times[(meeting_locations[prev_person], meeting_locations[person])])
        solver.add(start_times[person] >= end_times[prev_person] + travel_time)
    
    # Define the possible locations for each meeting
    solver.add(Or([meeting_locations[person] == location for location in locations]))

# Ensure no overlapping meetings
for i in range(len(people)):
    for j in range(i + 1, len(people)):
        person_i = people[i]
        person_j = people[j]
        solver.add(Or(end_times[person_i] <= start_times[person_j], end_times[person_j] <= start_times[person_i]))

# Optimize the schedule
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in people:
        start_time = model[start_times[person]].as_long()
        end_time = model[end_times[person]].as_long()
        location = model[meeting_locations[person]].as_string()[1:-1]  # Remove quotes
        start_hour = start_time // 60 + 9
        start_minute = start_time % 60
        end_hour = end_time // 60 + 9
        end_minute = end_time % 60
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{start_hour:02}:{start_minute:02}",
            "end_time": f"{end_hour:02}:{end_minute:02}",
            "location": location
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")