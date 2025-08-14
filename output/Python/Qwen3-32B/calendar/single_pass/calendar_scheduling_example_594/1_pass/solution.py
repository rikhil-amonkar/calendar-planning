def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append( (prev_end, start) )
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append( (prev_end, work_end) )
    return free

work_start = 9 * 60
work_end = 17 * 60

# Adam's busy times on Monday
adam_busy = [
    (9*60 + 30, 10*60),  # 9:30-10:00
    (12*60 + 30, 13*60), # 12:30-13:00
    (14*60 + 30, 15*60), # 14:30-15:00
    (16*60 + 30, 17*60)  # 16:30-17:00
]

# Roy's busy times on Monday
roy_busy = [
    (10*60, 11*60),          # 10:00-11:00
    (11*60 + 30, 13*60),     # 11:30-13:00
    (13*60 + 30, 14*60 + 30),# 13:30-14:30
    (16*60 + 30, 17*60)      # 16:30-17:00
]

adam_free = get_free_intervals(adam_busy, work_start, work_end)
roy_free = get_free_intervals(roy_busy, work_start, work_end)

possible_slots = []
for a_start, a_end in adam_free:
    for r_start, r_end in roy_free:
        start = max(a_start, r_start)
        end = min(a_end, r_end)
        if start < end and (end - start) >= 30:
            possible_slots.append( (start, end) )

# Find earliest slot
possible_slots.sort()
earliest_start, earliest_end = possible_slots[0]

start_str = to_time_str(earliest_start)
end_str = to_time_str(earliest_end)
print(f"{start_str}:{end_str} Monday")