def format_time(time_int):
    hour = time_int // 100
    minute = time_int % 100
    return f"{hour:02d}:{minute:02d}"

def get_free_intervals(busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = 900
    for start, end in sorted_busy:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < 1700:
        free.append((prev_end, 1700))
    return free

terry_busy = {
    "Monday": [(1030, 1100), (1230, 1400), (1500, 1700)],
    "Tuesday": [(930, 1000), (1030, 1100), (1400, 1430), (1600, 1630)],
    "Wednesday": [(930, 1030), (1100, 1200), (1300, 1330), (1500, 1600), (1630, 1700)],
    "Thursday": [(930, 1000), (1200, 1230), (1300, 1430), (1600, 1630)],
    "Friday": [(900, 1130), (1200, 1230), (1330, 1600), (1630, 1700)],
}

frances_busy = {
    "Monday": [(930, 1100), (1130, 1300), (1400, 1430), (1500, 1600)],
    "Tuesday": [(900, 930), (1000, 1030), (1100, 1200), (1300, 1430), (1530, 1630)],
    "Wednesday": [(930, 1000), (1030, 1100), (1130, 1600), (1630, 1700)],
    "Thursday": [(1100, 1230), (1430, 1700)],
    "Friday": [(930, 1030), (1100, 1230), (1300, 1600), (1630, 1700)],
}

days_order = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]

for day in days_order:
    terry_free = get_free_intervals(terry_busy.get(day, []))
    frances_free = get_free_intervals(frances_busy.get(day, []))
    earliest_slot = None
    for t_start, t_end in terry_free:
        for f_start, f_end in frances_free:
            start_overlap = max(t_start, f_start)
            end_overlap = min(t_end, f_end)
            if start_overlap < end_overlap:
                duration = end_overlap - start_overlap
                if duration >= 30:
                    earliest_slot = (start_overlap, start_overlap + 30)
                    break
        if earliest_slot:
            break
    if earliest_slot:
        start_time = earliest_slot[0]
        end_time = earliest_slot[1]
        formatted_start = format_time(start_time)
        formatted_end = format_time(end_time)
        print(f"{formatted_start}:{formatted_end} {day}")
        break