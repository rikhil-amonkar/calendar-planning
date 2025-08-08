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

# Create a solver instance
solver = Solver()

# Define the start and end times for each meeting
meeting_start = {person: Int(f'start_{person}') for person in availability}
meeting_end = {person: Int(f'end_{person}') for person in availability}

# Define the location for each meeting using EnumSort
Location, (Union_Square, Mission_District, Bayview, Sunset_District) = EnumSort('Location', ['Union Square', 'Mission District', 'Bayview', 'Sunset District'])
meeting_location = {person: Const(f'location_{person}', Location) for person in availability}

# Add constraints for each meeting
for person, (start, end) in availability.items():
    solver.add(meeting_start[person] >= start)
    solver.add(meeting_end[person] <= end)
    solver.add(meeting_end[person] - meeting_start[person] >= min_meeting_durations[person])

# Add constraints for travel times
for i, person1 in enumerate(availability):
    for person2 in list(availability)[i+1:]:
        # If meeting with person1 ends before meeting with person2 starts
        travel_time_expr = If(meeting_location[person1] == Union_Square, 
                              If(meeting_location[person2] == Mission_District, travel_times[('Union Square', 'Mission District')],
                                 If(meeting_location[person2] == Bayview, travel_times[('Union Square', 'Bayview')],
                                    If(meeting_location[person2] == Sunset_District, travel_times[('Union Square', 'Sunset District')],
                                       0))),
                              If(meeting_location[person1] == Mission_District, 
                                 If(meeting_location[person2] == Union_Square, travel_times[('Mission District', 'Union Square')],
                                    If(meeting_location[person2] == Bayview, travel_times[('Mission District', 'Bayview')],
                                       If(meeting_location[person2] == Sunset_District, travel_times[('Mission District', 'Sunset District')],
                                          0))),
                                 If(meeting_location[person1] == Bayview, 
                                    If(meeting_location[person2] == Union_Square, travel_times[('Bayview', 'Union Square')],
                                       If(meeting_location[person2] == Mission_District, travel_times[('Bayview', 'Mission District')],
                                          If(meeting_location[person2] == Sunset_District, travel_times[('Bayview', 'Sunset District')],
                                             0))),
                                    If(meeting_location[person1] == Sunset_District, 
                                       If(meeting_location[person2] == Union_Square, travel_times[('Sunset District', 'Union Square')],
                                          If(meeting_location[person2] == Mission_District, travel_times[('Sunset District', 'Mission District')],
                                             If(meeting_location[person2] == Bayview, travel_times[('Sunset District', 'Bayview')],
                                                0))),
                                       0))))
        solver.add(Or(meeting_end[person1] + travel_time_expr <= meeting_start[person2],
                      meeting_end[person2] + travel_time_expr <= meeting_start[person1]))

# Define the initial location
initial_location = Union_Square
initial_time = 0

# Add constraints for the initial location and time
for person in availability:
    travel_time_expr = If(meeting_location[person] == Union_Square, travel_times[('Union Square', 'Union Square')],
                           If(meeting_location[person] == Mission_District, travel_times[('Union Square', 'Mission District')],
                              If(meeting_location[person] == Bayview, travel_times[('Union Square', 'Bayview')],
                                 If(meeting_location[person] == Sunset_District, travel_times[('Union Square', 'Sunset District')],
                                    0))))
    solver.add(meeting_start[person] >= initial_time + travel_time_expr)

# Define the objective to maximize the number of meetings
objective = Optimize()
objective.add(solver.assertions())
objective.maximize(Sum([If(meeting_start[person] >= 0, 1, 0) for person in availability]))

# Solve the problem
if objective.check() == sat:
    model = objective.model()
    itinerary = []
    for person in availability:
        start_time = model[meeting_start[person]].as_long()
        end_time = model[meeting_end[person]].as_long()
        location = model[meeting_location[person]].as_string()
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