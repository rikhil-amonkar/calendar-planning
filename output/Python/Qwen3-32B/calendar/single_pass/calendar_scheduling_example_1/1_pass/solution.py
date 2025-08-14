def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_slot_free(busy_intervals, start, end):
    for b_start, b_end in busy_intervals:
        if start < b_end and end > b_start:
            return False
    return True

raymond_busy = [(540, 570), (690, 720), (780, 810), (900, 930)]
billy_busy = [(600, 630), (720, 780), (990, 1020)]
donald_busy = [(540, 570), (600, 660), (720, 780), (840, 870), (960, 1020)]

found = False
for start in range(540, 871):
    end = start + 30
    if (is_slot_free(raymond_busy, start, end) and
        is_slot_free(billy_busy, start, end) and
        is_slot_free(donald_busy, start, end)):
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        time_range = f"{start_time}:{end_time}"
        day = "Monday"
        print(f"{{{time_range}}} {day}")
        found = True
        break