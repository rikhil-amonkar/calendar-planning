from z3 import *

# Define the time slots
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
meeting_duration = 30  # 0.5 hours in minutes

# Define the existing schedules for Susan and Sandra
susan_schedule_monday = [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)]
susan_schedule_tuesday = [(11 * 60 + 30, 12 * 60)]
susan_schedule_wednesday = [(9 * 60 + 30, 10 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)]

sandra_schedule_monday = [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)]
sandra_schedule_tuesday = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)]
sandra_schedule_wednesday = [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)]

# Create a Z3 solver
solver = Solver()

# Create Z3 variables to represent the day and start time of the meeting
meeting_day = Int('meeting_day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
meeting_start = Int('meeting_start')

# Add constraints to ensure the meeting day is either Monday, Tuesday or Wednesday
solver.add(And(meeting_day >= 0, meeting_day <= 2))

# Add constraints to ensure the meeting start time is within the work hours
solver.add(And(meeting_start >= start_time, meeting_start <= end_time - meeting_duration))

# Add constraints to avoid Susan's schedule on Monday
for start, end in susan_schedule_monday:
    solver.add(Or(Not(And(meeting_day == 0, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 0)))

# Add constraints to avoid Susan's schedule on Tuesday
solver.add(Not(meeting_day == 1))

# Add constraints to avoid Susan's schedule on Wednesday
for start, end in susan_schedule_wednesday:
    solver.add(Or(Not(And(meeting_day == 2, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 2)))

# Add constraints to avoid Sandra's schedule on Monday
for start, end in sandra_schedule_monday:
    solver.add(Or(Not(And(meeting_day == 0, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 0)))

# Add constraints to avoid Sandra's schedule on Tuesday
for start, end in sandra_schedule_tuesday:
    solver.add(Or(Not(And(meeting_day == 1, meeting_start + meeting_duration <= start, meeting_start >= end)), Not(meeting_day == 1)))

# Add constraints to avoid Sandra's schedule on Wednesday
solver.add(Not(meeting_day == 2))

# Add constraint to prefer not to meet on Monday after 16:00 for Sandra
solver.add(Or(meeting_day!= 0, meeting_start + meeting_duration <= 16 * 60))

# Check if the solver can find a solution
if solver.check() == sat:
    # Get the solution
    model = solver.model()
    meeting_day_value = model[meeting_day].as_long()
    meeting_start_time = model[meeting_start].as_long()
    day = ["Monday", "Tuesday", "Wednesday"][meeting_day_value]
    print(f"Meeting can be scheduled on {day} from {meeting_start_time // 60}:{meeting_start_time % 60:02} to {(meeting_start_time + meeting_duration) // 60}:{(meeting_start_time + meeting_duration) % 60:02}")
else:
    print("No solution found")