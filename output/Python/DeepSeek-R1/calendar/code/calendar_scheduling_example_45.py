work_start = 540  # 9:00 in minutes
work_end = 1020   # 17:00 in minutes
samuel_busy = [(540, 630), (690, 720), (780, 810), (840, 960), (990, 1020)]
free_slots = []
prev_end = work_start

for start, end in samuel_busy:
    if start > prev_end:
        free_slots.append((prev_end, start))
    prev_end = max(prev_end, end)

if prev_end < work_end:
    free_slots.append((prev_end, work_end))

meeting_duration = 30
for slot_start, slot_end in free_slots:
    if slot_end - slot_start >= meeting_duration:
        meeting_start = slot_start
        meeting_end = meeting_start + meeting_duration
        print(f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d}")
        print("Monday")
        break