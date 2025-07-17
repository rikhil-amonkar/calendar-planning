from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

# Define the availability of each friend in minutes from 9:00AM
availability = {
    'Rebecca': (time_in_minutes(11, 30), time_in_minutes(20, 15)),
    'Karen': (time_in_minutes(12, 45), time_in_minutes(15, 0)),
    'Carol': (time_in_minutes(10, 15), time_in_minutes(11, 45)),
}

# Define the minimum meeting durations in minutes
min_meeting_durations = {
    'Rebecca': 120,
    'Karen': 120,
    'Carol': 30,
}

# Define the locations
locations = ['Union Square', 'Mission District', 'Bayview', 'Sunset District']

# Create a solver
solver = Solver()

# Define the start and end times for each meeting
meeting_start = {person: Int(f'start_{person}') for person in availability}
meeting_end = {person: Int(f'end_{person}') for person in availability}

# Define the location for each meeting
meeting_location = {person: String(f'location_{person}') for person in availability}

# Add constraints for each meeting
for person, (start, end) in availability.items():
    solver.add(meeting_start[person] >= start)
    solver.add(meeting_end[person] <= end)
    solver.add(meeting_end[person] - meeting_start[person] >= min_meeting_durations[person])

# Add constraints for travel times
for i, person1 in enumerate(availability):
    for person2 in list(availability)[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts
        solver.add(Or(meeting_end[person1] + travel_times[(meeting_location[person1], meeting_location[person2])] <= meeting_start[person2],
                      meeting_end[person2] + travel_times[(meeting_location[person2], meeting_location[person1])] <= meeting_start[person1]))

# Define the initial location
initial_location = 'Union Square'
initial_time = 0

# Add constraints for the initial location and time
for person in availability:
    solver.add(meeting_start[person] >= initial_time + travel_times[(initial_location, meeting_location[person])])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for person in availability:
        start_time = model[meeting_start[person]].as_long()
        end_time = model[meeting_end[person]].as_long()
        location = model[meeting_location[person]].as_string()[1:-1]  # Remove quotes
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": f"{(start_time // 60 + 9):02}:{start_time % 60:02}",
            "end_time": f"{(end_time // 60 + 9):02}:{end_time % 60:02}"
        })
    itinerary.sort(key=lambda x: x["start_time"])
    print({"itinerary": itinerary})
else:
    print("No solution found")