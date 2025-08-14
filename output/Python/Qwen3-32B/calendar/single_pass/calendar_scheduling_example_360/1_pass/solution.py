import datetime

work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

participants = {
    'Emily': [(600, 630), (960, 990)],
    'Mason': [],
    'Maria': [(630, 660), (840, 870)],
    'Carl': [(570, 600), (630, 750), (810, 840), (870, 930), (960, 1020)],
    'David': [(570, 660), (690, 720), (750, 810), (840, 900), (960, 1020)],
    'Frank': [(570, 630), (660, 690), (750, 810), (870, 1020)],
}

def get_free_intervals(work_start, work_end, busy_intervals):
    busy = sorted(busy_intervals)
    merged = []
    for interval in busy:
        if not merged or interval[0] > merged[-1][1]:
            merged.append(interval)
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], interval[1]))
    free = []
    prev_end = work_start
    for start, end in merged:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def generate_slots(free_intervals):
    slots = []
    for s, e in free_intervals:
        if e - s >= 30:
            for start in range(s, e - 30 + 1):
                slots.append((start, start + 30))
    return slots

all_slots = []
for name, busy in participants.items():
    free = get_free_intervals(work_start, work_end, busy)
    slots = generate_slots(free)
    all_slots.append(set(slots))

common_slots = set.intersection(*all_slots)
earliest = min(common_slots)

def to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

start, end = earliest
formatted = f"{to_time(start)}:{to_time(end)}"

print(f"{formatted} Monday")