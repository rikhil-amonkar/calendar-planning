from z3 import *

# Define the time slots
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # 0.5 hours in minutes

# Define the existing schedules for Julie and Ruth
julie_schedule_monday = []  # Julie has no meetings the whole week
julie_schedule_tuesday = []
julie_schedule_wednesday = []
julie_schedule_thursday = []

ruth_schedule_monday = [(9 * 60, 17 * 60)]
ruth_schedule_tuesday = [(9 * 60, 17 * 60)]
ruth_schedule_wednesday = [(9 * 60, 17 * 60)]
ruth_schedule_thursday = [(9 * 60, 11 * 60), (11 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)]

# Create a Z3 solver
solver = Solver()

# Create Z3 variables to represent the day and start time of the meeting
meeting_day = Int('meeting_day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday
meeting_start = Int('meeting_start')

# Add constraints to ensure the meeting day is either Monday, Tuesday, Wednesday or Thursday
solver.add(And(meeting_day >= 0, meeting_day <= 3))

# Add constraints to ensure the meeting start time is within the work hours
solver.add(And(meeting_start >= start_time, meeting_start <= end_time - meeting_duration))

# Add constraints to avoid Ruth's schedule on Monday
for start, end in ruth_schedule_monday:
    solver.add(Or(Not(And(meeting_day == 0, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 0)))

# Add constraints to avoid Ruth's schedule on Tuesday
for start, end in ruth_schedule_tuesday:
    solver.add(Or(Not(And(meeting_day == 1, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 1)))

# Add constraints to avoid Ruth's schedule on Wednesday
for start, end in ruth_schedule_wednesday:
    solver.add(Or(Not(And(meeting_day == 2, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 2)))

# Add constraints to avoid Ruth's schedule on Thursday
for start, end in ruth_schedule_thursday:
    solver.add(Or(Not(And(meeting_day == 3, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 3)))

# Add constraint to prefer meeting after 11:30 on Thursday for Julie
solver.add(Or(meeting_day!= 3, meeting_start >= 11 * 60 + 30))

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_time = model[meeting_start].as_long()
    day = ["Monday", "Tuesday", "Wednesday", "Thursday"][meeting_day_value]
    print(f"Meeting can be scheduled on {day} from {meeting_start_time // 60}:{meeting_start_time % 60:02} to {(meeting_start_time + meeting_duration) // 60}:{(meeting_start_time + meeting_duration) % 60:02}")
else:
    print("No solution found")