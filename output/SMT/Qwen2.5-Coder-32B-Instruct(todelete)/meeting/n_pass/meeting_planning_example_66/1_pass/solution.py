from z3 import *

# Define the time in minutes from 9:00AM
def time_in_minutes(hour, minute):
    return hour * 60 + minute

# Define the start and end times in minutes
start_time = time_in_minutes(9, 0)  # 9:00AM
robert_start = time_in_minutes(11, 15)  # 11:15AM
robert_end = time_in_minutes(17, 45)  # 5:45PM
travel_time_nob_to_presidio = 17  # in minutes
travel_time_presidio_to_nob = 18  # in minutes

# Create a solver instance
solver = Solver()

# Define the variables for the meeting start and end times
robert_meeting_start = Int('robert_meeting_start')
robert_meeting_end = Int('robert_meeting_end')

# Add constraints
# Robert meeting must be within his availability
solver.add(robert_meeting_start >= robert_start)
solver.add(robert_meeting_end <= robert_end)

# Meeting duration must be at least 120 minutes
solver.add(robert_meeting_end - robert_meeting_start >= 120)

# Travel time constraints
# You must arrive at Presidio before the meeting starts
solver.add(robert_meeting_start >= start_time + travel_time_nob_to_presidio)

# You must be back at Nob Hill by the end of the day (assuming 21:00 as the end of the day)
solver.add(robert_meeting_end + travel_time_presidio_to_nob <= time_in_minutes(21, 0))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    robert_meeting_start_value = model[robert_meeting_start].as_long()
    robert_meeting_end_value = model[robert_meeting_end].as_long()

    # Convert the meeting times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    itinerary = [
        {
            "action": "meet",
            "person": "Robert",
            "start_time": format_time(robert_meeting_start_value),
            "end_time": format_time(robert_meeting_end_value)
        }
    ]

    print({"itinerary": itinerary})
else:
    print("No solution found")