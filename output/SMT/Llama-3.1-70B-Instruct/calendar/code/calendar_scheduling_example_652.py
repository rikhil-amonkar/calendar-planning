from z3 import *

# Define the time slots
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # 0.5 hours in minutes

# Define the existing schedules for Jesse and Lawrence
jesse_schedule_monday = [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)]
jesse_schedule_tuesday = [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60)]

lawrence_schedule_monday = [(9 * 60, 17 * 60)]
lawrence_schedule_tuesday = [(9 * 60 + 30, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)]

# Create a Z3 solver
solver = Solver()

# Create Z3 variables to represent the day and start time of the meeting
meeting_day = Int('meeting_day')  # 0 for Monday, 1 for Tuesday
meeting_start = Int('meeting_start')

# Add constraints to ensure the meeting day is either Monday or Tuesday
solver.add(And(meeting_day >= 0, meeting_day <= 1))

# Add constraints to ensure the meeting start time is within the work hours
solver.add(And(meeting_start >= start_time, meeting_start <= end_time - meeting_duration))

# Add constraints to avoid Jesse's schedule on Monday
for start, end in jesse_schedule_monday:
    solver.add(Or(Not(And(meeting_day == 0, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 0)))

# Add constraints to avoid Jesse's schedule on Tuesday
for start, end in jesse_schedule_tuesday:
    solver.add(Or(Not(And(meeting_day == 1, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 1)))

# Add constraints to avoid Lawrence's schedule on Monday
for start, end in lawrence_schedule_monday:
    solver.add(Or(Not(And(meeting_day == 0, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 0)))

# Add constraints to avoid Lawrence's schedule on Tuesday
for start, end in lawrence_schedule_tuesday:
    solver.add(Or(Not(And(meeting_day == 1, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 1)))

# Add constraint to prefer not to meet on Tuesday after 16:30 for Lawrence
solver.add(Or(meeting_day!= 1, meeting_start + meeting_duration <= 16 * 60 + 30))

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_time = model[meeting_start].as_long()
    day = ["Monday", "Tuesday"][meeting_day_value]
    print(f"Meeting can be scheduled on {day} from {meeting_start_time // 60}:{meeting_start_time % 60:02} to {(meeting_start_time + meeting_duration) // 60}:{(meeting_start_time + meeting_duration) % 60:02}")
else:
    print("No solution found")