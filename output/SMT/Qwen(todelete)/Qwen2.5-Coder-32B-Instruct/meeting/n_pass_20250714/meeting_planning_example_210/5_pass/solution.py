from z3 import *

# Define the time variables for each friend
emily_start = Int('emily_start')
joseph_start = Int('joseph_start')
melissa_start = Int('melissa_start')

# Define the duration of meeting each friend
emily_duration = 105
joseph_duration = 120
melissa_duration = 75

# Define the availability times for each friend
emily_available_start = 4 * 60 + 15  # 4:15 PM in minutes from 00:00
emily_available_end = 9 * 60         # 9:00 PM in minutes from 00:00
joseph_available_start = 5 * 60 + 15 # 5:15 PM in minutes from 00:00
joseph_available_end = 10 * 60       # 10:00 PM in minutes from 00:00
melissa_available_start = 3 * 60 + 45 # 3:45 PM in minutes from 00:00
melissa_available_end = 9 * 60 + 45   # 9:45 PM in minutes from 00:00

# Create boolean variables to indicate whether we meet each friend
meet_emily = Bool('meet_emily')
meet_joseph = Bool('meet_joseph')
meet_melissa = Bool('meet_melissa')

# Create a solver instance
solver = Solver()

# Add constraints for meeting times if we decide to meet each friend
solver.add(Implies(meet_emily, emily_start >= emily_available_start))
solver.add(Implies(meet_emily, emily_start + emily_duration <= emily_available_end))

solver.add(Implies(meet_joseph, joseph_start >= joseph_available_start))
solver.add(Implies(meet_joseph, joseph_start + joseph_duration <= joseph_available_end))

solver.add(Implies(meet_melissa, melissa_start >= melissa_available_start))
solver.add(Implies(meet_melissa, melissa_start + melissa_duration <= melissa_available_end))

# Travel times from Fisherman's Wharf to each location
travel_times = {
    'Presidio': 17,
    'Richmond District': 18,
    'Financial District': 11
}

# Define the start time at Fisherman's Wharf
start_time = 9 * 60  # 9:00 AM in minutes from 00:00

# Add constraints for travel times if we decide to meet each friend
solver.add(Implies(meet_emily, emily_start >= start_time + travel_times['Presidio']))
solver.add(Implies(meet_joseph, joseph_start >= start_time + travel_times['Richmond District']))
solver.add(Implies(meet_melissa, melissa_start >= start_time + travel_times['Financial District']))

# Ensure we meet exactly 3 people
solver.add(meet_emily + meet_joseph + meet_melissa == 3)

# Add constraints to ensure no overlapping meetings if we decide to meet each friend
solver.add(Or(Not(meet_emily), Not(meet_joseph), emily_start + emily_duration <= joseph_start))
solver.add(Or(Not(meet_emily), Not(meet_melissa), emily_start + emily_duration <= melissa_start))
solver.add(Or(Not(meet_joseph), Not(meet_emily), joseph_start + joseph_duration <= emily_start))
solver.add(Or(Not(meet_joseph), Not(meet_melissa), joseph_start + joseph_duration <= melissa_start))
solver.add(Or(Not(meet_melissa), Not(meet_emily), melissa_start + melissa_duration <= emily_start))
solver.add(Or(Not(meet_melissa), Not(meet_joseph), melissa_start + melissa_duration <= joseph_start))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    emily_meeting_start = model[emily_start].as_long() if model[meet_emily] else None
    joseph_meeting_start = model[joseph_start].as_long() if model[meet_joseph] else None
    melissa_meeting_start = model[melissa_start].as_long() if model[meet_melissa] else None

    # Convert the meeting start times back to hours and minutes
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02}:{mins:02}"

    SOLUTION = ""
    if emily_meeting_start is not None:
        SOLUTION += f"Meeting Emily from {format_time(emily_meeting_start)} to {format_time(emily_meeting_start + emily_duration)}\n"
    if joseph_meeting_start is not None:
        SOLUTION += f"Meeting Joseph from {format_time(joseph_meeting_start)} to {format_time(joseph_meeting_start + joseph_duration)}\n"
    if melissa_meeting_start is not None:
        SOLUTION += f"Meeting Melissa from {format_time(melissa_meeting_start)} to {format_time(melissa_meeting_start + melissa_duration)}\n"
else:
    SOLUTION = "No solution found."

print(SOLUTION)