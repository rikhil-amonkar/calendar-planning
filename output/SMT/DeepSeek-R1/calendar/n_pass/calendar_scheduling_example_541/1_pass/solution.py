from z3 import Int, Solver, Or

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m - 9 * 60  # Subtract 540 minutes (9 hours) to start from 0 at 9:00

def minutes_to_time(minutes):
    total_minutes = minutes + 9 * 60
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work day boundaries in minutes (9:00 to 17:00)
work_start = 0  # 9:00
work_end = 480  # 17:00 (8 hours * 60 minutes)
meeting_duration = 60  # 1 hour

# Convert blocked times to minutes relative to 9:00
kayla_blocked = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

rebecca_blocked = [
    (time_to_minutes("9:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Combine all blocked intervals
all_blocked = kayla_blocked + rebecca_blocked

# Create Z3 solver and variable for meeting start time
s = Solver()
start = Int('start')

# Meeting must be within work hours
s.add(start >= work_start)
s.add(start + meeting_duration <= work_end)

# Meeting must not overlap with any blocked intervals
for block_start, block_end in all_blocked:
    s.add(Or(start + meeting_duration <= block_start, start >= block_end))

# Check for solution
if s.check() == z3.sat:
    model = s.model()
    start_minutes = model[start].as_long()
    start_time_str = minutes_to_time(start_minutes)
    end_time_str = minutes_to_time(start_minutes + meeting_duration)
    
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found")