def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current_start, current_end in sorted_intervals[1:]:
        last_start, last_end = merged[-1]
        if current_start <= last_end:
            merged[-1] = (last_start, max(last_end, current_end))
        else:
            merged.append((current_start, current_end))
    return merged

def get_free_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_time():
    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM
    schedules = {
        'Monday': {
            'Doris': [(540, 690), (720, 750), (810, 960), (990, 1020)],
            'Jean': []
        },
        'Tuesday': {
            'Doris': [(540, 1020)],
            'Jean': [(690, 720), (960, 990)]
        }
    }
    for day in ['Monday', 'Tuesday']:
        all_busy = []
        for participant in schedules[day]:
            all_busy.extend(schedules[day][participant])
        merged = merge_intervals(all_busy)
        free_intervals = get_free_intervals(work_start, work_end, merged)
        candidates = []
        for (start, end) in free_intervals:
            if end - start >= 30:  # 30 minutes meeting
                meeting_start = start
                meeting_end = start + 30
                if meeting_end <= end:
                    if day == 'Monday' and meeting_end <= 840:  # 14:00 is 840 minutes
                        candidates.append((meeting_start, meeting_end))
        if candidates:
            candidates.sort()
            earliest = candidates[0]
            day_name = day
            start_str = minutes_to_time(earliest[0])
            end_str = minutes_to_time(earliest[1])
            print(f"{{{start_str}:{end_str}}} {day_name}")
            return
    print("No meeting found")

find_meeting_time()