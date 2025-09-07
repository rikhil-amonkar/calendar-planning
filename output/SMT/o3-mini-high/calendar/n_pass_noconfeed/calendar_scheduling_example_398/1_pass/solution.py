from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define meeting parameters
duration = 30  # in minutes

# Define meeting start time as an integer (minutes from midnight)
start = Int('start')

solver = Solver()

# Working hours: meeting must start no earlier than 9:00 (540 minutes)
# and finish by 17:00 (1020 minutes)
solver.add(start >= 540, start + duration <= 1020)

# Doris's blocked intervals:
# Block 1: 09:00 - 11:00  => [540, 660)
solver.add(Or(start + duration <= 540, start >= 660))
# Block 2: 13:30 - 14:00  => [810, 840)
solver.add(Or(start + duration <= 810, start >= 840))
# Block 3: 16:00 - 16:30  => [960, 990)
solver.add(Or(start + duration <= 960, start >= 990))

# Theresa's blocked interval:
# 10:00 - 12:00  => [600, 720)
solver.add(Or(start + duration <= 600, start >= 720))

# Terry's blocked intervals:
# Block 1: 09:30 - 10:00  => [570, 600)
solver.add(Or(start + duration <= 570, start >= 600))
# Block 2: 11:30 - 12:00  => [690, 720)
solver.add(Or(start + duration <= 690, start >= 720))
# Block 3: 12:30 - 13:00  => [750, 780)
solver.add(Or(start + duration <= 750, start >= 780))
# Block 4: 13:30 - 14:00  => [810, 840)
solver.add(Or(start + duration <= 810, start >= 840))
# Block 5: 14:30 - 15:00  => [870, 900)
solver.add(Or(start + duration <= 870, start >= 900))
# Block 6: 15:30 - 17:00  => [930, 1020)
# Since starting after 1020 is impossible, force meeting to finish by 930.
solver.add(start + duration <= 930)

# Carolyn's blocked intervals:
# Block 1: 09:00 - 10:30  => [540, 630)
solver.add(Or(start + duration <= 540, start >= 630))
# Block 2: 11:00 - 11:30  => [660, 690)
solver.add(Or(start + duration <= 660, start >= 690))
# Block 3: 12:00 - 13:00  => [720, 780)
solver.add(Or(start + duration <= 720, start >= 780))
# Block 4: 13:30 - 14:30  => [810, 870)
solver.add(Or(start + duration <= 810, start >= 870))
# Block 5: 15:00 - 17:00  => [900, 1020)
solver.add(start + duration <= 900)

# Kyle's blocked intervals:
# Block 1: 09:00 - 09:30  => [540, 570)
solver.add(Or(start + duration <= 540, start >= 570))
# Block 2: 11:30 - 12:00  => [690, 720)
solver.add(Or(start + duration <= 690, start >= 720))
# Block 3: 12:30 - 13:00  => [750, 780)
solver.add(Or(start + duration <= 750, start >= 780))
# Block 4: 14:30 - 17:00  => [870, 1020)
solver.add(start + duration <= 870)

if solver.check() == sat:
    model = solver.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + duration
    day = "Monday"
    # Output in the format: HH:MM-HH:MM along with the day of the week.
    print(f"{day} {format_time(meeting_start)}-{format_time(meeting_end)}")
else:
    print("No valid meeting time found.")