from z3 import *

# Define the days of the week as integers for easier manipulation
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2
THURSDAY = 3

# Define the meeting duration in minutes
MEETING_DURATION = 30

# Define the work hours in minutes from 9:00 to 17:00
WORK_START = 9 * 60
WORK_END = 17 * 60

# Define the busy times for Betty and Scott
betty_busy_times = {
    MONDAY: [(10*60, 10*60+30), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
    TUESDAY: [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
    WEDNESDAY: [(9*60+30, 10*60), (13*60, 13*60+30), (14*60, 14*60+30)],
    THURSDAY: [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
}

scott_busy_times = {
    MONDAY: [(9*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)],
    TUESDAY: [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60), (14*60, 15*60), (16*60, 16*60+30)],
    WEDNESDAY: [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
    THURSDAY: [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
}

# Create a solver instance
solver = Solver()

# Define the variables for the meeting day and start time
meeting_day = Int('meeting_day')
meeting_start = Int('meeting_start')

# Add constraints for the meeting day
solver.add(meeting_day >= MONDAY)
solver.add(meeting_day <= THURSDAY)

# Add constraints for the meeting start time within work hours
solver.add(meeting_start >= WORK_START)
solver.add(meeting_start + MEETING_DURATION <= WORK_END)

# Add constraints to avoid busy times for Betty
for day, busy_times in betty_busy_times.items():
    for start, end in busy_times:
        solver.add(Or(meeting_day != day, meeting_start + MEETING_DURATION <= start, meeting_start >= end))

# Add constraints to avoid busy times for Scott
for day, busy_times in scott_busy_times.items():
    for start, end in busy_times:
        solver.add(Or(meeting_day != day, meeting_start + MEETING_DURATION <= start, meeting_start >= end))

# Add constraints based on preferences
# Betty cannot meet on Monday
solver.add(meeting_day != MONDAY)

# Scott would like to avoid more meetings on Wednesday
solver.add(meeting_day != WEDNESDAY)

# Thursday before 15:00 is not allowed for Betty
solver.add(Or(meeting_day != THURSDAY, meeting_start >= 15*60))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_value = model[meeting_start].as_long()
    
    # Convert the meeting day and start time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_day_str = days[meeting_day_value]
    meeting_start_str = f"{meeting_start_value // 60}:{meeting_start_value % 60:02}"
    meeting_end_str = f"{(meeting_start_value + MEETING_DURATION) // 60}:{(meeting_start_value + MEETING_DURATION) % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day_str}\nStart Time: {meeting_start_str}\nEnd Time: {meeting_end_str}")
else:
    print("No solution found")