from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 60  # 1 hour meeting

# Create a solver instance
solver = Solver()

# Define the start time of the meeting as a variable
meeting_start = Int('meeting_start')

# Constraints for the meeting time
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Julie's blocked times
julie_blocked_times = [(9*60, 9*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 14*60), (16*60, 17*60)]
for start, end in julie_blocked_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Sean's blocked times
sean_blocked_times = [(9*60, 9*60+30), (13*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
for start, end in sean_blocked_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Lori's blocked times
lori_blocked_times = [(10*60, 10*60+30), (11*60, 13*60), (15*60+30, 17*60)]
for start, end in lori_blocked_times:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")