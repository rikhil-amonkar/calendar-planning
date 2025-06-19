import re

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def parse_schedule(s, days):
    pattern = '(' + '|'.join(days) + ')'
    parts = re.split(pattern, s)
    schedule = {day: [] for day in days}
    for i in range(1, len(parts), 2):
        if i + 1 >= len(parts):
            break
        day_name = parts[i]
        if day_name not in days:
            continue
        meeting_str = parts[i + 1].strip()
        if meeting_str.startswith('during '):
            meeting_str = meeting_str[7:]
        meetings = meeting_str.split(',')
        intervals = []
        for meet in meetings:
            meet = meet.strip()
            if not meet:
                continue
            if ' to ' not in meet:
                continue
            times = meet.split(' to ')
            if len(times) < 2:
                continue
            start_str = times[0].strip()
            end_str = times[1].strip()
            try:
                start_min_abs = time_str_to_minutes(start_str)
                end_min_abs = time_str_to_minutes(end_str)
            except:
                continue
            start_min = start_min_abs - 540
            end_min = end_min_abs - 540
            if start_min < 0:
                start_min = 0
            if end_min > 480:
                end_min = 480
            if start_min < end_min:
                intervals.append((start_min, end_min))
        schedule[day_name] = intervals
    return schedule

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end:
            if e > end:
                end = e
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def get_free_intervals(merged_busy, total_start=0, total_end=480):
    free = []
    current = total_start
    for start, end in merged_busy:
        if current < start:
            free.append((current, start))
        current = end
    if current < total_end:
        free.append((current, total_end))
    return free

def main():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    megan_str = "Monday during 13:00 to 13:30, 14:00 to 15:30, Tuesday during 9:00 to 9:30, 12:00 to 12:30, 16:00 to 17:00, Wednesday during 9:30 to 10:00, 10:30 to 11:30, 12:30 to 14:00, 16:00 to 16:30, Thursday during 13:30 to 14:30, 15:00 to 15:30"
    daniel_str = "Monday during 10:00 to 11:30, 12:30 to 15:00, Tuesday during 9:00 to 10:00, 10:30 to 17:00, Wednesday during 9:00 to 10:00, 10:30 to 11:30, 12:00 to 17:00, Thursday during 9:00 to 12:00, 12:30 to 14:30, 15:00 to 15:30, 16:00 to 17:00"
    megan_schedule = parse_schedule(megan_str, days)
    daniel_schedule = parse_schedule(daniel_str, days)
    for day in days:
        busy_intervals = megan_schedule[day] + daniel_schedule[day]
        merged_busy = merge_intervals(busy_intervals)
        free_intervals = get_free_intervals(merged_busy)
        for interval in free_intervals:
            start, end = interval
            duration = end - start
            if duration >= 60:
                abs_start_min = 540 + start
                abs_end_min = abs_start_min + 60
                start_hour = abs_start_min // 60
                start_minute = abs_start_min % 60
                end_hour = abs_end_min // 60
                end_minute = abs_end_min % 60
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                print(day)
                print(time_str)
                return

if __name__ == "__main__":
    main()