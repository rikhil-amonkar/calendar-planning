def get_available_intervals(blocked_intervals, start, end):
    if not blocked_intervals:
        return [(start, end)]
    blocked_sorted = sorted(blocked_intervals, key=lambda x: x[0])
    available = []
    current = start
    for block in blocked_sorted:
        if current < block[0]:
            available.append((current, block[0]))
        current = max(current, block[1])
    if current < end:
        available.append((current, end))
    return available

meeting_duration = 30
work_start = 0
work_end = 360

christine_blocked = [(120, 150)]
helen_blocked = [(30, 90), (120, 150), (180, 210), (270, 360)]

christine_avail = get_available_intervals(christine_blocked, work_start, work_end)
helen_avail = get_available_intervals(helen_blocked, work_start, work_end)

for c_avail in christine_avail:
    for h_avail in helen_avail:
        low = max(c_avail[0], h_avail[0])
        high = min(c_avail[1], h_avail[1])
        if low < high and high - low >= meeting_duration:
            meeting_start = low
            meeting_end = low + meeting_duration
            start_hour = 9 + meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = 9 + meeting_end // 60
            end_minute = meeting_end % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(f"Monday {time_str}")
            exit()