def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_free(busy_intervals, start, end):
    for b_start, b_end in busy_intervals:
        if start < b_end and end > b_start:
            return False
    return True

# Define busy intervals for each participant
raymond_busy = [
    (540, 570),  # 9:00-9:30
    (690, 720),  # 11:30-12:00
    (780, 810),  # 13:00-13:30
    (900, 930),  # 15:00-15:30
]

billy_busy = [
    (600, 630),  # 10:00-10:30
    (720, 780),  # 12:00-13:00
    (990, 1020), # 16:30-17:00
]

donald_busy = [
    (540, 570),  # 9:00-9:30
    (600, 660),  # 10:00-11:00
    (720, 780),  # 12:00-13:00
    (840, 870),  # 14:00-14:30
    (960, 1020), # 16:00-17:00
]

# Meeting duration in minutes
meeting_duration = 30

# Work hours start and end (in minutes)
work_start = 540  # 9:00 AM
latest_start = 870  # 14:30 (latest start to end by 15:00)

# Find the earliest possible time slot
for start in range(work_start, latest_start + 1):
    end = start + meeting_duration
    if (is_free(raymond_busy, start, end) and
        is_free(billy_busy, start, end) and
        is_free(donald_busy, start, end)):
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        day = "Monday"
        print(f"{{{start_time}:{end_time}}} {day}")
        break