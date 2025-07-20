def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) * 60 + int(m)) - 9 * 60

def minutes_to_time(minutes):
    total_minutes = minutes + 9 * 60
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start_curr, end_curr = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end_curr:
            if e > end_curr:
                end_curr = e
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    return merged

def get_free_intervals(busy_intervals):
    if not busy_intervals:
        return [(0, 480)]
    merged_busy = merge_intervals(busy_intervals)
    free_intervals = []
    current = 0
    for s, e in merged_busy:
        if current < s:
            free_intervals.append((current, s))
        current = e
    if current < 480:
        free_intervals.append((current, 480))
    return free_intervals

def main():
    duration = 60
    wednesday_constraint = 180  # 12:00 in minutes from 9:00

    busy_times = {
        'Monday': [
            ('12:00', '12:30'),   # Judith
            ('9:30', '10:00'),    # Timothy
            ('10:30', '11:30'),   # Timothy
            ('12:30', '14:00'),   # Timothy
            ('15:30', '17:00')    # Timothy
        ],
        'Tuesday': [
            ('9:30', '13:00'),    # Timothy
            ('13:30', '14:00'),   # Timothy
            ('14:30', '17:00')    # Timothy
        ],
        'Wednesday': [
            ('11:30', '12:00'),   # Judith
            ('9:00', '9:30'),     # Timothy
            ('10:30', '11:00'),   # Timothy
            ('13:30', '14:30'),   # Timothy
            ('15:00', '15:30'),   # Timothy
            ('16:00', '16:30')    # Timothy
        ]
    }

    busy_intervals = {}
    for day, intervals in busy_times.items():
        busy_intervals[day] = []
        for (s, e) in intervals:
            start_min = time_to_minutes(s)
            end_min = time_to_minutes(e)
            busy_intervals[day].append((start_min, end_min))

    days_order = ['Tuesday', 'Wednesday', 'Monday']
    meeting_day = None
    meeting_start = None
    meeting_end = None

    for day in days_order:
        free_intervals = get_free_intervals(busy_intervals[day])
        if day == 'Wednesday':
            for s, e in free_intervals:
                candidate_start = max(s, wednesday_constraint)
                if candidate_start + duration <= e:
                    meeting_day = day
                    meeting_start = candidate_start
                    meeting_end = candidate_start + duration
                    break
            if meeting_day is not None:
                break
        else:
            for s, e in free_intervals:
                if e - s >= duration:
                    meeting_day = day
                    meeting_start = s
                    meeting_end = s + duration
                    break
            if meeting_day is not None:
                break

    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    print(meeting_day)
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()