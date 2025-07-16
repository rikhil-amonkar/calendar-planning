import re

def parse_busy_for_participant(s, day_list):
    pattern = '(' + '|'.join(day_list) + ')'
    tokens = re.split(pattern, s)
    result = {}
    i = 1
    while i < len(tokens):
        day_name = tokens[i]
        if i+1 < len(tokens):
            time_str = tokens[i+1].strip()
            if time_str.startswith('during'):
                time_str = time_str[6:].strip()
            time_str = time_str.rstrip(';,').strip()
            intervals = []
            if time_str != '':
                parts = time_str.split(',')
                for part in parts:
                    part = part.strip()
                    if part == '':
                        continue
                    if 'to' not in part:
                        continue
                    times = part.split('to')
                    if len(times) < 2:
                        continue
                    start_time_str = times[0].strip()
                    end_time_str = times[1].strip()
                    try:
                        start_h, start_m = start_time_str.split(':')
                        end_h, end_m = end_time_str.split(':')
                        start_minutes = int(start_h)*60 + int(start_m)
                        end_minutes = int(end_h)*60 + int(end_m)
                        intervals.append((start_minutes, end_minutes))
                    except:
                        pass
            result[day_name] = intervals
        i += 2
    return result

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end:
            end = max(end, e)
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def compute_free_intervals(busy_intervals, work_start, work_end):
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    for s, e in merged_busy:
        if current < s:
            free.append((current, s))
        current = max(current, e)
        if current >= work_end:
            break
    if current < work_end:
        free.append((current, work_end))
    return free

def interval_intersection(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        a1, b1 = intervals1[i]
        a2, b2 = intervals2[j]
        low = max(a1, a2)
        high = min(b1, b2)
        if low < high:
            common.append((low, high))
        if b1 < b2:
            i += 1
        else:
            j += 1
    return common

def main():
    nancy_str = "Monday during 10:00 to 10:30, 11:30 to 12:30, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00, Tuesday during 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 15:30 to 16:00, Wednesday during 10:00 to 11:30, 13:30 to 16:00;"
    jose_str = "Monday during 9:00 to 17:00, Tuesday during 9:00 to 17:00, Wednesday during 9:00 to 9:30, 10:00 to 12:30, 13:30 to 14:30, 15:00 to 17:00;"
    
    days_of_week = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30
    
    nancy_busy_dict = parse_busy_for_participant(nancy_str, days_of_week)
    jose_busy_dict = parse_busy_for_participant(jose_str, days_of_week)
    
    for day in days_of_week:
        nancy_busy = nancy_busy_dict.get(day, [])
        jose_busy = jose_busy_dict.get(day, [])
        
        free_nancy = compute_free_intervals(nancy_busy, work_start, work_end)
        free_jose = compute_free_intervals(jose_busy, work_start, work_end)
        common_free = interval_intersection(free_nancy, free_jose)
        
        for start, end in common_free:
            if end - start >= duration:
                meeting_start = start
                meeting_end = meeting_start + duration
                start_hour = meeting_start // 60
                start_minute = meeting_start % 60
                end_hour = meeting_end // 60
                end_minute = meeting_end % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                time_range_str = f"{start_str}:{end_str}"
                print(day)
                print(time_range_str)
                return

if __name__ == "__main__":
    main()