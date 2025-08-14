from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17
}

# Define the availability of Stephanie and John
stephanie_start = time_in_minutes(8, 15)
stephanie_end = time_in_minutes(11, 30)
john_start = time_in_minutes(10, 15)
john_end = time_in_minutes(20, 45)

# Define the minimum meeting durations
stephanie_min_duration = 90
john_min_duration = 30

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
stephanie_meeting_start = Int('stephanie_meeting_start')
stephanie_meeting_end = Int('stephanie_meeting_end')
john_meeting_start = Int('john_meeting_start')
john_meeting_end = Int('john_meeting_end')

# Define the constraints
# Stephanie meeting constraints
solver.add(stephanie_meeting_start >= stephanie_start)
solver.add(stephanie_meeting_end <= stephanie_end)
solver.add(stephanie_meeting_end - stephanie_meeting_start >= stephanie_min_duration)

# John meeting constraints
solver.add(john_meeting_start >= john_start)
solver.add(john_meeting_end <= john_end)
solver.add(john_meeting_end - john_meeting_start >= john_min_duration)

# Travel constraints
# We need to ensure that the travel time between meetings is respected
# Let's assume we start at Embarcadero at 9:00AM (0 minutes)
start_time = 0

# Constraint for Stephanie meeting after starting at Embarcadero
solver.add(stephanie_meeting_start >= start_time + travel_times[('Embarcadero', 'Financial District')])

# Constraint for John meeting after Stephanie meeting
solver.add(john_meeting_start >= stephanie_meeting_end + travel_times[('Financial District', 'Alamo Square')])

# Constraint for John meeting ending before the day ends
solver.add(john_meeting_end <= time_in_minutes(23, 59))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    stephanie_meeting_start_value = model[stephanie_meeting_start].as_long()
    stephanie_meeting_end_value = model[stephanie_meeting_end].as_long()
    john_meeting_start_value = model[john_meeting_start].as_long()
    john_meeting_end_value = model[john_meeting_end].as_long()

    # Convert the times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60 + 9
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {"action": "meet", "person": "Stephanie", "start_time": format_time(stephanie_meeting_start_value), "end_time": format_time(stephanie_meeting_end_value)},
        {"action": "meet", "person": "John", "start_time": format_time(john_meeting_start_value), "end_time": format_time(john_meeting_end_value)}
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")