#!/usr/bin/env python3
from z3 import Optimize, Or, Int, sat

def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020
meeting_duration = 30

cynthia_busy = [(570, 630), (690, 720), (780, 810), (900, 960)]
lauren_busy = [(540, 570), (630, 660), (690, 720), (780, 810), (840, 870), (900, 930), (960, 1020)]
robert_busy = [(630, 660), (690, 720), (750, 810), (840, 960)]

all_busy = cynthia_busy + lauren_busy + robert_busy

opt = Optimize()
meeting_start = Int("meeting_start")

opt.add(meeting_start >= work_start)
opt.add(meeting_start + meeting_duration <= work_end)

for (busy_start, busy_end) in all_busy:
    opt.add(Or(meeting_start + meeting_duration <= busy_start,
               meeting_start >= busy_end))

opt.minimize(meeting_start)

if opt.check() == sat:
    model = opt.model()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    meeting_time = f"{minutes_to_str(start_val)} - {minutes_to_str(end_val)}"
    print("Meeting time:", meeting_time)
    print("Monday")
else:
    print("No valid meeting time found")