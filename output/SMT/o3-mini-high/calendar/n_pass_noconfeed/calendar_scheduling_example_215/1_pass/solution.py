from z3 import Optimize, Or, Int

def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Working hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020
meeting_duration = 30

# Busy intervals for each participant (in minutes from midnight)
# Cynthia is busy:
#   9:30 - 10:30  -> [570, 630]
#   11:30 - 12:00 -> [690, 720]
#   13:00 - 13:30 -> [780, 810]
#   15:00 - 16:00 -> [900, 960]
cynthia_busy = [(570, 630), (690, 720), (780, 810), (900, 960)]

# Lauren is busy:
#   9:00 - 9:30   -> [540, 570]
#   10:30 - 11:00 -> [630, 660]
#   11:30 - 12:00 -> [690, 720]
#   13:00 - 13:30 -> [780, 810]
#   14:00 - 14:30 -> [840, 870]
#   15:00 - 15:30 -> [900, 930]
#   16:00 - 17:00 -> [960, 1020]
lauren_busy = [(540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020)]

# Robert is busy:
#   10:30 - 11:00 -> [630, 660]
#   11:30 - 12:00 -> [690, 720]
#   12:30 - 13:30 -> [750, 810]
#   14:00 - 16:00 -> [840, 960]
robert_busy = [(630, 660), (690, 720), (750, 810), (840, 960)]

# Steven and Roy are free, so no busy intervals for them.

# Combine all busy intervals
all_busy = cynthia_busy + lauren_busy + robert_busy

# Create an optimizer to minimize the meeting start time
opt = Optimize()
meeting_start = Int("meeting_start")

# The meeting must be within work hours
opt.add(meeting_start >= work_start)
opt.add(meeting_start + meeting_duration <= work_end)

# For each busy interval, ensure the meeting does not overlap with it.
# Two intervals [a, b) and [c, d) do not overlap if either b <= c or a >= d.
for (busy_start, busy_end) in all_busy:
    opt.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))

# Minimize meeting_start so that the meeting is as early as possible
opt.minimize(meeting_start)

if opt.check() == 'sat':
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    meeting_time = f"{minutes_to_str(start_val)}:{minutes_to_str(end_val)}"
    print(meeting_time)
    print("Monday")
else:
    print("No valid meeting time found")