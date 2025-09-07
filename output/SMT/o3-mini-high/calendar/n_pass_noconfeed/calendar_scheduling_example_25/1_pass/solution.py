from z3 import *

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration in minutes
meeting_duration = 60

# S represents the meeting start time (in minutes from midnight)
S = Int('S')
meeting_end = S + meeting_duration

solver = Solver()

# Working hours on Monday: from 9:00 (540 minutes) to 17:00 (1020 minutes)
solver.add(S >= 540)
solver.add(meeting_end <= 1020)

# Pamela's preference: No meeting on Monday after 14:30 (870 minutes), so the meeting must finish by then.
solver.add(meeting_end <= 870)

# Anthony's busy intervals on Monday:
# 9:30-10:00 -> [570,600]
solver.add(Or(meeting_end <= 570, S >= 600))
# 12:00-13:00 -> [720,780]
solver.add(Or(meeting_end <= 720, S >= 780))
# 16:00-16:30 -> [960,990] (this is automatically satisfied due to earlier constraints, but added for completeness)
solver.add(Or(meeting_end <= 960, S >= 990))

# Pamela's busy intervals on Monday:
# 9:30-10:00 -> [570,600]
solver.add(Or(meeting_end <= 570, S >= 600))
# 16:30-17:00 -> [990,1020] 
solver.add(Or(meeting_end <= 990, S >= 1020))

# Zachary's busy intervals on Monday:
# 9:00-11:30 -> [540,690]
# (Since S must be >=540, the only option is that the meeting starts after 11:30)
solver.add(S >= 690)
# 12:00-12:30 -> [720,750]
solver.add(Or(meeting_end <= 720, S >= 750))
# 13:00-13:30 -> [780,810]
solver.add(Or(meeting_end <= 780, S >= 810))
# 14:30-15:00 -> [870,900]
solver.add(Or(meeting_end <= 870, S >= 900))
# 16:00-17:00 -> [960,1020]
solver.add(Or(meeting_end <= 960, S >= 1020))

if solver.check() == sat:
    model = solver.model()
    start_time = model[S].as_long()
    end_time = start_time + meeting_duration
    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)
    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    print("No valid meeting time found.")