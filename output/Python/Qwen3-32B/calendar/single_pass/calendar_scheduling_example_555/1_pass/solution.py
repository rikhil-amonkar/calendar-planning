def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_day_start = 9 * 60  # 540
work_day_end = 17 * 60   # 1020

# Randy's busy intervals in minutes
randy_busy = [
    (9*60, 10*60 + 30),  # 9:00-10:30
    (11*60, 15*60 + 30), # 11:00-15:30
    (16*60, 17*60)       # 16:00-17:00
]

def get_available_slots(work_start, work_end, busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            available.append( (current_start, start) )
        current_start = max(current_start, end)
        if current_start >= work_end:
            break
    if current_start < work_end:
        available.append( (current_start, work_end) )
    return available

randy_available = get_available_slots(work_day_start, work_day_end, randy_busy)

# Evelyn's available is from 9:00 to 13:00
evelyn_available = [(work_day_start, 13 * 60)]

meeting_duration = 30  # minutes

possible_slots = []
for r_start, r_end in randy_available:
    for e_start, e_end in evelyn_available:
        overlap_start = max(r_start, e_start)
        overlap_end = min(r_end, e_end)
        if overlap_start < overlap_end:
            duration = overlap_end - overlap_start
            if duration >= meeting_duration:
                possible_slots.append( (overlap_start, overlap_end) )

best_slot = possible_slots[0]
start_time = minutes_to_time(best_slot[0])
end_time = minutes_to_time(best_slot[0] + meeting_duration)
day = "Monday"

print(f"{start_time}:{end_time} {day}")