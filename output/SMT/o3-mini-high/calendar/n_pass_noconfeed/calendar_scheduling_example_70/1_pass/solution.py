from z3 import Optimize, Int, Or, sat

def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting parameters
duration = 30       # Meeting duration: 30 minutes
work_start = 9 * 60  # 9:00 in minutes (9*60 = 540)
work_end = 17 * 60   # 17:00 in minutes (17*60 = 1020)

# Create an optimizer instance
opt = Optimize()
s = Int('s')  # Meeting start time in minutes from midnight

# Meeting must be within working hours
opt.add(s >= work_start, s + duration <= work_end)

# Function to add a non-overlap constraint for a busy interval.
# The meeting interval [s, s+duration) must either end before the busy interval starts, or start after it ends.
def add_no_overlap(opt, s, busy_start, busy_end):
    opt.add(Or(s + duration <= busy_start, s >= busy_end))

# Denise's busy intervals on Monday: [12:00, 12:30) and [15:30, 16:00)
denise_busy = [
    (12 * 60, 12 * 60 + 30),    # 12:00 to 12:30
    (15 * 60 + 30, 16 * 60)     # 15:30 to 16:00
]
for bs, be in denise_busy:
    add_no_overlap(opt, s, bs, be)

# Natalie's busy intervals on Monday: [9:00, 11:30), [12:00, 13:00), [14:00, 14:30), [15:00, 17:00)
natalie_busy = [
    (9 * 60, 11 * 60 + 30),     # 9:00 to 11:30
    (12 * 60, 13 * 60),         # 12:00 to 13:00
    (14 * 60, 14 * 60 + 30),    # 14:00 to 14:30
    (15 * 60, 17 * 60)          # 15:00 to 17:00
]
for bs, be in natalie_busy:
    add_no_overlap(opt, s, bs, be)

# Angela has no busy intervals, so no additional constraint is needed.

# To ensure the meeting is scheduled as early as possible, minimize the meeting start time.
opt.minimize(s)

if opt.check() == sat:
    model = opt.model()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    meeting_time = f"{{{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)}}}"
    print("Monday")
    print(meeting_time)
else:
    print("No available meeting time on Monday")