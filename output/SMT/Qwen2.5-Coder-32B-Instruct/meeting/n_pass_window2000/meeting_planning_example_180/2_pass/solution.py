from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return hour * 60 + minute

# Define the travel times in minutes
travel_times = {
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'The Castro'): 22,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'The Castro'): 7,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Mission District'): 7,
}

# Define the availability of James and Robert
james_start = time_in_minutes(12, 45)
james_end = time_in_minutes(14, 0)
robert_start = time_in_minutes(12, 45)
robert_end = time_in_minutes(15, 15)

# Define the minimum meeting durations
james_min_duration = 75
robert_min_duration = 30

# Define the solver
solver = Solver()

# Define the variables for the start and end times of meetings
james_meeting_start = Int('james_meeting_start')
james_meeting_end = Int('james_meeting_end')
robert_meeting_start = Int('robert_meeting_start')
robert_meeting_end = Int('robert_meeting_end')

# Define the constraints
# James meeting constraints
solver.add(james_meeting_start >= james_start)
solver.add(james_meeting_end <= james_end)
solver.add(james_meeting_end - james_meeting_start >= james_min_duration)

# Robert meeting constraints
solver.add(robert_meeting_start >= robert_start)
solver.add(robert_meeting_end <= robert_end)
solver.add(robert_meeting_end - robert_meeting_start >= robert_min_duration)

# Ensure meetings do not overlap and respect travel times
# If meeting James first, then travel to Robert
travel_james_to_robert = travel_times[('Mission District', 'The Castro')]
solver.add(Implies(james_meeting_end <= robert_meeting_start, 
                  james_meeting_end + travel_james_to_robert <= robert_meeting_start))

# If meeting Robert first, then travel to James
travel_robert_to_james = travel_times[('The Castro', 'Mission District')]
solver.add(Implies(robert_meeting_end <= james_meeting_start, 
                  robert_meeting_end + travel_robert_to_james <= james_meeting_start))

# Ensure meetings do not overlap
solver.add(Or(james_meeting_end <= robert_meeting_start, robert_meeting_end <= james_meeting_start))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    james_start_time = model[james_meeting_start].as_long()
    james_end_time = model[james_meeting_end].as_long()
    robert_start_time = model[robert_meeting_start].as_long()
    robert_end_time = model[robert_meeting_end].as_long()
    
    # Convert times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    itinerary = []
    if james_start_time < james_end_time:
        itinerary.append({"action": "meet", "person": "James", "start_time": format_time(james_start_time), "end_time": format_time(james_end_time)})
    if robert_start_time < robert_end_time:
        itinerary.append({"action": "meet", "person": "Robert", "start_time": format_time(robert_start_time), "end_time": format_time(robert_end_time)})
    
    # Sort the itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    
    print({"itinerary": itinerary})
else:
    print("No solution found")