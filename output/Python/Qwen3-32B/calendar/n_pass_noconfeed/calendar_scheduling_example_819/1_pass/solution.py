import sys

def get_free_slots(busy_periods, work_start, work_end):
    sorted_busy = sorted(busy_periods, key=lambda x: x[0])
    free_slots = []
    prev_end = work_start
    for start, end in sorted_busy:
        if prev_end < start:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    return free_slots

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

WORK_START = 9 * 60
WORK_END = 17 * 60

ruth_schedule = {
    'Monday': [(WORK_START, WORK_END)],
    'Tuesday': [(WORK_START, WORK_END)],
    'Wednesday': [(WORK_START, WORK_END)],
    'Thursday': [(9 * 60, 11 * 60), (11 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

for day in days:
    busy_periods = ruth_schedule[day]
    free_slots = get_free_slots(busy_periods, WORK_START, WORK_END)
    for start, end in free_slots:
        if end - start >= 30:
            if day == 'Thursday':
                julie_min_start = 11 * 60 + 30  # 11:30 AM
                possible_start = max(start, julie_min_start)
                if possible_start + 30 <= end:
                    meeting_start = possible_start
                    meeting_end = possible_start + 30
                    day_name = day
                    start_time = to_time_str(meeting_start)
                    end_time = to_time_str(meeting_end)
                    print(f"{start_time}:{end_time} {day_name}")
                    sys.exit()
            else:
                meeting_start = start
                meeting_end = start + 30
                day_name = day
                start_time = to_time_str(meeting_start)
                end_time = to_time_str(meeting_end)
                print(f"{start_time}:{end_time} {day_name}")
                sys.exit()