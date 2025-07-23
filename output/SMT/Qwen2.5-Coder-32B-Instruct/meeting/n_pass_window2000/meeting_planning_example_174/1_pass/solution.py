from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return (hour - 9) * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16
}

# Define the availability of friends
availability = {
    'Thomas': (time_in_minutes(15, 30), time_in_minutes(19, 15)),  # 3:30PM to 7:15PM
    'Kenneth': (time_in_minutes(12, 0), time_in_minutes(15, 45))   # 12:00PM to 3:45PM
}

# Define the minimum meeting durations in minutes
min_meeting_durations = {
    'Thomas': 75,
    'Kenneth': 45
}

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
thomas_start = Int('thomas_start')
thomas_end = Int('thomas_end')
kenneth_start = Int('kenneth_start')
kenneth_end = Int('kenneth_end')

# Define the constraints
solver.add(thomas_start >= availability['Thomas'][0])
solver.add(thomas_end <= availability['Thomas'][1])
solver.add(thomas_end - thomas_start >= min_meeting_durations['Thomas'])

solver.add(kenneth_start >= availability['Kenneth'][0])
solver.add(kenneth_end <= availability['Kenneth'][1])
solver.add(kenneth_end - kenneth_start >= min_meeting_durations['Kenneth'])

# Define the travel constraints
# Start at Nob Hill at 9:00AM (0 minutes)
start_time = 0

# If meeting Thomas first, then travel to Pacific Heights
solver.add(Implies(thomas_start < kenneth_start, thomas_start >= start_time + travel_times[('Nob Hill', 'Pacific Heights')]))
solver.add(Implies(thomas_start < kenneth_start, kenneth_start >= thomas_end + travel_times[('Pacific Heights', 'Mission District')]))

# If meeting Kenneth first, then travel to Mission District
solver.add(Implies(kenneth_start < thomas_start, kenneth_start >= start_time + travel_times[('Nob Hill', 'Mission District')]))
solver.add(Implies(kenneth_start < thomas_start, thomas_start >= kenneth_end + travel_times[('Mission District', 'Pacific Heights')]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    thomas_start_time = model[thomas_start].as_long()
    thomas_end_time = model[thomas_end].as_long()
    kenneth_start_time = model[kenneth_start].as_long()
    kenneth_end_time = model[kenneth_end].as_long()

    # Convert times back to HH:MM format
    def format_time(minutes):
        hours = 9 + minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = []
    if thomas_start_time < kenneth_start_time:
        itinerary.append({"action": "meet", "person": "Thomas", "start_time": format_time(thomas_start_time), "end_time": format_time(thomas_end_time)})
        itinerary.append({"action": "meet", "person": "Kenneth", "start_time": format_time(kenneth_start_time), "end_time": format_time(kenneth_end_time)})
    else:
        itinerary.append({"action": "meet", "person": "Kenneth", "start_time": format_time(kenneth_start_time), "end_time": format_time(kenneth_end_time)})
        itinerary.append({"action": "meet", "person": "Thomas", "start_time": format_time(thomas_start_time), "end_time": format_time(thomas_end_time)})

    print({"itinerary": itinerary})
else:
    print("No solution found")