def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

work_start = 9 * 60
work_end = 17 * 60
meeting_duration = 60

# Busy intervals for each participant
kayla_busy = [(10*60, 10*60 + 30), (14*60 + 30, 16*60)]
rebecca_busy = [(9*60, 13*60), (13*60 + 30, 15*60), (15*60 + 30, 16*60)]

# Compute free intervals
kayla_free = get_free_intervals(kayla_busy, work_start, work_end)
rebecca_free = get_free_intervals(rebecca_busy, work_start, work_end)

# Find common intervals
common = []
for k in kayla_free:
    for r in rebecca_free:
        start = max(k[0], r[0])
        end = min(k[1], r[1])
        if start < end and (end - start) >= meeting_duration:
            common.append((start, end))

# Find earliest common interval
earliest = min(common, key=lambda x: x[0])
start_time_str = to_time_str(earliest[0])
end_time_str = to_time_str(earliest[1])
day = "Monday"

print(f"{{{start_time_str}:{end_time_str}}} {day}")