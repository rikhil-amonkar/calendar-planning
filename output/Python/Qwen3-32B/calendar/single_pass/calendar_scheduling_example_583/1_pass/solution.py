def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals


def find_earliest_meeting(lisa_free, anthony_free, duration):
    for l_start, l_end in lisa_free:
        for a_start, a_end in anthony_free:
            overlap_start = max(l_start, a_start)
            overlap_end = min(l_end, a_end)
            if overlap_start < overlap_end:
                if overlap_end - overlap_start >= duration:
                    return (overlap_start, overlap_start + duration)
    return None


def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


work_start = 9 * 60
work_end = 17 * 60

# Lisa's busy times
lisa_busy = [
    (9*60, 9*60 + 30),
    (10*60 + 30, 11*60),
    (14*60, 16*60)
]

# Anthony's busy times
anthony_busy = [
    (9*60, 9*60 + 30),
    (11*60, 11*60 + 30),
    (12*60 + 30, 13*60 + 30),
    (14*60, 15*60),
    (15*60 + 30, 16*60),
    (16*60 + 30, 17*60)
]

lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
anthony_free = get_free_intervals(anthony_busy, work_start, work_end)

meeting_duration = 30
meeting_time = find_earliest_meeting(lisa_free, anthony_free, meeting_duration)

start_str = minutes_to_time_str(meeting_time[0])
end_str = minutes_to_time_str(meeting_time[1])

print(f"{start_str}:{end_str} Monday")
