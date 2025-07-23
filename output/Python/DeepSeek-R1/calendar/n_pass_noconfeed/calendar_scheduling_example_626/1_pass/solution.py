def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) - 9) * 60 + int(m)

def minutes_to_time_str(m):
    total_minutes = m
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def convert_intervals(intervals):
    return [(time_str_to_minutes(start), time_str_to_minutes(end)) for start, end in intervals]

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_intervals[0]
    for s, e in sorted_intervals[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    return merged

def find_free_intervals(busy_intervals, work_start=0, work_end=480):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged_busy = merge_intervals(busy_intervals)
    free_intervals = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_meeting_slot(free_intervals, duration=60):
    for start, end in free_intervals:
        if end - start >= duration:
            return (start, start + duration)
    return None

def main():
    schedules = {
        'Monday': {
            'Patricia': [('10:00','10:30'), ('11:30','12:00'), ('13:00','13:30'), ('14:30','15:30'), ('16:00','16:30')],
            'Jesse': [('9:00','17:00')]
        },
        'Tuesday': {
            'Patricia': [('10:00','10:30'), ('11:00','12:00'), ('14:00','16:00'), ('16:30','17:00')],
            'Jesse': [('11:00','11:30'), ('12:00','12:30'), ('13:00','14:00'), ('14:30','15:00'), ('15:30','17:00')]
        }
    }
    days = ['Monday', 'Tuesday']
    duration = 60
    work_start = 0
    work_end = 480

    for day in days:
        patricia_intervals = schedules[day]['Patricia']
        jesse_intervals = schedules[day]['Jesse']
        
        patricia_minutes = convert_intervals(patricia_intervals)
        jesse_minutes = convert_intervals(jesse_intervals)
        all_busy = patricia_minutes + jesse_minutes
        
        free_intervals = find_free_intervals(all_busy, work_start, work_end)
        slot = find_meeting_slot(free_intervals, duration)
        
        if slot:
            start_time = minutes_to_time_str(slot[0])
            end_time = minutes_to_time_str(slot[1])
            time_output = f"{start_time}:{end_time}"
            print(day)
            print(time_output)
            return

    print("No suitable slot found")

if __name__ == "__main__":
    main()