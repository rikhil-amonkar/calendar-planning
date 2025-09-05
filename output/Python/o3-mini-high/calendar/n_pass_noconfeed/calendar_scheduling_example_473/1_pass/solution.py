def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting parameters
meeting_duration = 30  # minutes
work_start = 9 * 60    # 9:00 in minutes (540)
work_end = 17 * 60     # 17:00 in minutes (1020)

# Busy schedules for each participant represented as (start_minute, end_minute)
schedules = {
    "Gregory": [(540, 570), (690, 720)],  # 9:00-9:30, 11:30-12:00
    "Jonathan": [(540, 570), (720, 750), (780, 810), (900, 960), (990, 1020)], 
                  # 9:00-9:30, 12:00-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
    "Barbara": [(600, 630), (810, 840)],  # 10:00-10:30, 13:30-14:00
    "Jesse": [(600, 660), (750, 870)],     # 10:00-11:00, 12:30-14:30
    "Alan": [(570, 660), (690, 750), (780, 930), (960, 1020)],  
                  # 9:30-11:00, 11:30-12:30, 13:00-15:30, 16:00-17:00
    "Nicole": [(540, 630), (690, 720), (750, 810), (840, 1020)],  
                  # 9:00-10:30, 11:30-12:00, 12:30-13:30, 14:00-17:00
    "Catherine": [(540, 630), (720, 810), (900, 930), (960, 990)],  
                  # 9:00-10:30, 12:00-13:30, 15:00-15:30, 16:00-16:30
}

proposed_slot = None

# Iterate over each possible start time (minute by minute)
for candidate in range(work_start, work_end - meeting_duration + 1):
    slot_start = candidate
    slot_end = candidate + meeting_duration
    conflict = False
    for person, busy_times in schedules.items():
        for busy_start, busy_end in busy_times:
            # Check for overlap.
            # Two intervals [slot_start, slot_end) and [busy_start, busy_end) overlap if:
            # slot_start < busy_end and slot_end > busy_start.
            if slot_start < busy_end and slot_end > busy_start:
                conflict = True
                break
        if conflict:
            break
    if not conflict:
        proposed_slot = (slot_start, slot_end)
        break

if proposed_slot:
    start_str = minutes_to_time(proposed_slot[0])
    end_str = minutes_to_time(proposed_slot[1])
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available slot found.")