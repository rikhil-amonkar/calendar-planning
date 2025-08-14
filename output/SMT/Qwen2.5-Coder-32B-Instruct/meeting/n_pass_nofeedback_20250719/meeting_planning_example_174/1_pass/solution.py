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
    'Thomas': (time_in_minutes(15, 30), time_in_minutes(19, 15)),
    'Kenneth': (time_in_minutes(12, 0), time_in_minutes(15, 45))
}

# Define the minimum meeting durations
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

# If meeting Thomas, must travel from current location to Pacific Heights
# If meeting Kenneth, must travel from current location to Mission District
# We assume the best possible schedule, so we need to check both possibilities

# Check if we can meet Thomas after Kenneth
solver.push()
solver.add(kenneth_end + travel_times[('Mission District', 'Pacific Heights')] <= thomas_start)
if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"action": "meet", "person": "Kenneth", "start_time": f"{(model[kenneth_start].as_long() // 60 + 9):02}:{model[kenneth_start].as_long() % 60:02}", "end_time": f"{(model[kenneth_end].as_long() // 60 + 9):02}:{model[kenneth_end].as_long() % 60:02}"},
        {"action": "meet", "person": "Thomas", "start_time": f"{(model[thomas_start].as_long() // 60 + 9):02}:{model[thomas_start].as_long() % 60:02}", "end_time": f"{(model[thomas_end].as_long() // 60 + 9):02}:{model[thomas_end].as_long() % 60:02}"}
    ]
    solver.pop()
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
    exit()

# Check if we can meet Kenneth after Thomas
solver.pop()
solver.add(thomas_end + travel_times[('Pacific Heights', 'Mission District')] <= kenneth_start)
if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"action": "meet", "person": "Thomas", "start_time": f"{(model[thomas_start].as_long() // 60 + 9):02}:{model[thomas_start].as_long() % 60:02}", "end_time": f"{(model[thomas_end].as_long() // 60 + 9):02}:{model[thomas_end].as_long() % 60:02}"},
        {"action": "meet", "person": "Kenneth", "start_time": f"{(model[kenneth_start].as_long() // 60 + 9):02}:{model[kenneth_start].as_long() % 60:02}", "end_time": f"{(model[kenneth_end].as_long() // 60 + 9):02}:{model[kenneth_end].as_long() % 60:02}"}
    ]
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
    exit()

# If neither order works, check if we can meet only one
solver.pop()
solver.add(kenneth_start >= start_time)
solver.add(kenneth_end <= availability['Kenneth'][1])
solver.add(kenneth_end - kenneth_start >= min_meeting_durations['Kenneth'])
if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"action": "meet", "person": "Kenneth", "start_time": f"{(model[kenneth_start].as_long() // 60 + 9):02}:{model[kenneth_start].as_long() % 60:02}", "end_time": f"{(model[kenneth_end].as_long() // 60 + 9):02}:{model[kenneth_end].as_long() % 60:02}"}
    ]
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
    exit()

solver.pop()
solver.add(thomas_start >= start_time)
solver.add(thomas_end <= availability['Thomas'][1])
solver.add(thomas_end - thomas_start >= min_meeting_durations['Thomas'])
if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"action": "meet", "person": "Thomas", "start_time": f"{(model[thomas_start].as_long() // 60 + 9):02}:{model[thomas_start].as_long() % 60:02}", "end_time": f"{(model[thomas_end].as_long() // 60 + 9):02}:{model[thomas_end].as_long() % 60:02}"}
    ]
    print(f"SOLUTION: {json.dumps({'itinerary': itinerary})}")
    exit()

# If no meetings can be made
print("SOLUTION: {\"itinerary\": []}")