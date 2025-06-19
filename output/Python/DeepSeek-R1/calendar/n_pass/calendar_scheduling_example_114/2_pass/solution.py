def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = []
    start, end = intervals[0]
    for interval in intervals[1:]:
        if interval[0] <= end:
            end = max(end, interval[1])
        else:
            merged.append((start, end))
            start, end = interval
    merged.append((start, end))
    return merged

def parse_schedule(schedule_str):
    intervals = []
    if schedule_str.strip() == "":
        return intervals
    for interval in schedule_str.split(','):
        times = interval.split('-')
        start = time_to_minutes(times[0])
        end = time_to_minutes(times[1])
        intervals.append((start, end))
    return intervals

def main():
    day = input().strip()
    duration = int(input().strip())
    stephanie = parse_schedule(input().strip())
    cheryl = parse_schedule(input().strip())
    bradley = parse_schedule(input().strip())
    steven = parse_schedule(input().strip())

    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    all_busy = stephanie + cheryl + bradley + steven
    all_busy = merge_intervals(all_busy)

    free_intervals = []
    current = work_start
    for start, end in all_busy:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))

    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            print(f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}")
            print(day)
            return

    print("No suitable time found")

if __name__ == "__main__":
    main()