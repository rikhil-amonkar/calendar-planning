from z3 import Solver, Int, Or, sat

def minutes_to_time(minutes):
    # Convert minutes (offset from 9:00) into HH:MM in 24-hour format.
    hours = 9 + (minutes // 60)
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Initialize the Z3 solver
s = Solver()
# t represents the meeting start time in minutes after 9:00.
t = Int('t')
duration = 30  # meeting duration in minutes

# The meeting must start no earlier than 9:00 and finish by 17:00 (480 minutes after 9:00)
s.add(t >= 0, t + duration <= 480)

# Define the busy intervals (in minutes offset from 9:00) for each participant.
# Doris: 9:00-11:00, 13:30-14:00, 16:00-16:30 => (0,120), (270,300), (420,450)
# Theresa: 10:00-12:00 => (60,180)
# Christian: No meetings.
# Terry: 9:30-10:00, 11:30-12:00, 12:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-17:00 
#        => (30,60), (150,180), (210,240), (270,300), (330,360), (390,480)
# Carolyn: 9:00-10:30, 11:00-11:30, 12:00-13:00, 13:30-14:30, 15:00-17:00 
#          => (0,90), (120,150), (180,240), (270,330), (360,480)
# Kyle: 9:00-9:30, 11:30-12:00, 12:30-13:00, 14:30-17:00 
#       => (0,30), (150,180), (210,240), (330,480)
busy_intervals = [
    # Doris
    (0, 120), (270, 300), (420, 450),
    # Theresa
    (60, 180),
    # Terry
    (30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480),
    # Carolyn
    (0, 90), (120, 150), (180, 240), (270, 330), (360, 480),
    # Kyle
    (0, 30), (150, 180), (210, 240), (330, 480)
    # Christian has no busy intervals.
]

# For each busy interval, ensure the meeting does not overlap the busy time.
for busy_start, busy_end in busy_intervals:
    s.add(Or(t + duration <= busy_start, t >= busy_end))

# Check for a solution
if s.check() == sat:
    m = s.model()
    start = m[t].as_long()
    meeting_start = minutes_to_time(start)
    meeting_end = minutes_to_time(start + duration)
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time:", meeting_start)
    print("End Time:", meeting_end)
else:
    print("No solution found.")