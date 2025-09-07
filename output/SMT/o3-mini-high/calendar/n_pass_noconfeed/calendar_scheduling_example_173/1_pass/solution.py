from z3 import *

# Define meeting parameters
meeting_duration = 30  # duration in minutes
# We represent time as minutes from midnight. 9:00 is 540, 17:00 is 1020.
# Harold's constraint: no meeting after 13:00 so meeting must finish by 13:00 (i.e., start <= 750).
meeting_start = Int("meeting_start")

solver = Solver()
# Meeting must start no earlier than 9:00 and start no later than 12:30 (to finish by 13:00)
solver.add(meeting_start >= 540, meeting_start <= 750)

def no_overlap(x, busy_start, busy_end):
    """
    Returns a constraint that ensures the meeting [x, x+meeting_duration)
    does not overlap the busy interval [busy_start, busy_end).
    """
    return Or(x + meeting_duration <= busy_start, x >= busy_end)

# Jacqueline's busy intervals on Monday:
#   9:00-9:30, 11:00-11:30, 12:30-13:00, 15:30-16:00
solver.add(no_overlap(meeting_start, 540, 570))   # 9:00 to 9:30
solver.add(no_overlap(meeting_start, 660, 690))   # 11:00 to 11:30
solver.add(no_overlap(meeting_start, 750, 780))   # 12:30 to 13:00
solver.add(no_overlap(meeting_start, 930, 960))   # 15:30 to 16:00

# Harold's busy intervals:
#   10:00-10:30, 13:00-13:30, 15:00-17:00 and he does not want meetings after 13:00.
solver.add(no_overlap(meeting_start, 600, 630))   # 10:00 to 10:30
solver.add(no_overlap(meeting_start, 780, 810))   # 13:00 to 13:30
solver.add(no_overlap(meeting_start, 900, 1020))  # 15:00 to 17:00

# Arthur's busy intervals:
#   9:00-9:30, 10:00-12:30, 14:30-15:00, 15:30-17:00
solver.add(no_overlap(meeting_start, 540, 570))   # 9:00 to 9:30
solver.add(no_overlap(meeting_start, 600, 750))   # 10:00 to 12:30
solver.add(no_overlap(meeting_start, 870, 900))   # 14:30 to 15:00
solver.add(no_overlap(meeting_start, 930, 1020))  # 15:30 to 17:00

# Kelly's busy intervals:
#   9:00-9:30, 10:00-11:00, 11:30-12:30, 14:00-15:00, 15:30-16:00
solver.add(no_overlap(meeting_start, 540, 570))   # 9:00 to 9:30
solver.add(no_overlap(meeting_start, 600, 660))   # 10:00 to 11:00
solver.add(no_overlap(meeting_start, 690, 750))   # 11:30 to 12:30
solver.add(no_overlap(meeting_start, 840, 900))   # 14:00 to 15:00
solver.add(no_overlap(meeting_start, 930, 960))   # 15:30 to 16:00

if solver.check() == sat:
    model = solver.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration

    # Convert minutes from midnight into HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time_str = format_time(start_val)
    end_time_str = format_time(end_val)
    
    # The meeting is scheduled on Monday.
    print(f"Monday {start_time_str}:{end_time_str}")
else:
    print("No solution found.")