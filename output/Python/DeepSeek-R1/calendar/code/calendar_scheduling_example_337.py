def find_meeting_time():
    import datetime

    participants = {
        'John': [(690, 720), (840, 870)],  # 11:30-12:00, 14:00-14:30
        'Megan': [(720, 750), (840, 900), (930, 960)],  # 12:00-12:30, 14:00-15:00, 15:30-16:00
        'Brandon': [],
        'Kimberly': [(540, 570), (600, 630), (660, 870), (900, 960), (990, 1020)],  # 9:00-9:30, 10:00-10:30, 11:00-14:30, 15:00-16:00, 16:30-17:00
        'Sean': [(600, 660), (690, 840), (900, 930)],  # 10:00-11:00, 11:30-14:00, 15:00-15:30
        'Lori': [(540, 570), (630, 720), (780, 870), (960, 990)]  # 9:00-9:30, 10:30-12:00, 13:00-14:30, 16:00-16:30
    }

    work_start = 540  # 9:00 in minutes since midnight
    work_end = 1020   # 17:00 in minutes since midnight
    duration = 30

    all_busy = []
    for person in participants.values():
        all_busy.extend(person)
    all_busy.sort()

    def merge_intervals(intervals):
        if not intervals:
            return []
        merged = [list(intervals[0])]
        for current in intervals[1:]:
            last = merged[-1]
            if current[0] <= last[1]:
                last[1] = max(last[1], current[1])
            else:
                merged.append(list(current))
        return merged

    merged_busy = merge_intervals(all_busy)
    free_slots = []
    previous_end = work_start
    for start, end in merged_busy:
        if start > previous_end:
            free_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free_slots.append((previous_end, work_end))

    for slot in free_slots:
        start, end = slot
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            return (
                datetime.time(meeting_start // 60, meeting_start % 60).strftime('%H:%M'),
                datetime.time(meeting_end // 60, meeting_end % 60).strftime('%H:%M'),
                'Monday'
            )

    return None

start_time, end_time, day = find_meeting_time()
print(f"{day}:{start_time}:{end_time}")