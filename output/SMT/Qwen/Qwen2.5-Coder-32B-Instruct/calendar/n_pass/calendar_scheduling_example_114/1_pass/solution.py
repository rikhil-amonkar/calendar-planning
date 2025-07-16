from z3 import *

# Define the variables for the meeting start time in minutes since the start of the day
meeting_start = Int('meeting_start')
meeting_duration = 60  # Meeting duration is 1 hour

# Define the available time slots for each participant in minutes since the start of the day
stephanie_busy = [(600, 630), (960, 990)]  # 10:00-10:30, 16:00-16:30
cheryl_busy = [(600, 630), (690, 720), (810, 840), (990, 1020)]  # 10:00-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00
bradley_busy = [(570, 600), (630, 690), (810, 840), (870, 900), (930, 1020)]  # 9:30-10:00, 10:30-11:30, 13:30-14:00, 14:30-15:00, 15:30-17:00
steven_busy = [(540, 720), (780, 810), (870, 1020)]  # 9:00-12:00, 13:00-13:30, 14:30-17:00

# Create a solver instance
solver = Solver()

# Add constraints for the meeting start time
solver.add(meeting_start >= 540)  # 9:00 in minutes
solver.add(meeting_start + meeting_duration <= 1020)  # 17:00 in minutes

# Add constraints to avoid busy times for each participant
for start, end in stephanie_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in cheryl_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in bradley_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in steven_busy:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert the times back to HH:MM format
    def convert_to_hhmm(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"
    
    start_time_hhmm = convert_to_hhmm(meeting_start_time)
    end_time_hhmm = convert_to_hhmm(meeting_end_time)
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time_hhmm}")
    print(f"End Time: {end_time_hhmm}")
else:
    print("No solution found")