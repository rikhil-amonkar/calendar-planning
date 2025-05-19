def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30

    # Convert schedules to minutes since midnight
    schedules = {
        'Patrick': [(540, 570), (600, 630), (810, 840), (960, 990)],
        'Kayla': [(750, 810), (900, 930), (960, 990)],
        'Carl': [(630, 660), (720, 750), (780, 810), (870, 1020)],
        'Christian': [(540, 750), (780, 840), (870, 1020)]
    }

    # Create a unified busy timeline
    timeline = [0] * (work_end - work_start)
    for person in schedules.values():
        for start, end in person:
            for t in range(max(start, work_start) - work_start, min(end, work_end) - work_start):
                timeline[t] += 1

    # Find available slot
    current_start = None
    for i, count in enumerate(timeline):
        if count == 0:
            if current_start is None:
                current_start = i
            if i - current_start + 1 >= duration:
                start_time = current_start + work_start
                end_time = start_time + duration
                return (
                    f"{start_time // 60:02d}:{start_time % 60:02d}-"
                    f"{end_time // 60:02d}:{end_time % 60:02d}",
                    "Monday"
                )
        else:
            current_start = None

    return None

time_range, day = find_meeting_time()
print(f"{day}: {time_range}")