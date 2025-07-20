def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for s_busy, e_busy in sorted_busy:
        if current_start < s_busy:
            free.append((current_start, s_busy))
        current_start = max(current_start, e_busy)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a1, a2 = intervals1[i]
        b1, b2 = intervals2[j]
        start = max(a1, b1)
        end = min(a2, b2)
        if start < end:
            result.append((start, end))
        if a2 < b2:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    preference_start = time_to_minutes("14:30")
    
    busy = {
        'Adam': [(time_to_minutes("14:00"), time_to_minutes("15:00"))],
        'John': [
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        'Stephanie': [
            (time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        'Anna': [
            (time_to_minutes("09:30"), time_to_minutes("10:00")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ]
    }
    
    persons = ['Adam', 'John', 'Stephanie', 'Anna']
    free_intervals = {}
    for person in persons:
        free_intervals[person] = compute_free(busy[person], work_start, work_end)
    
    common = free_intervals[persons[0]]
    for i in range(1, len(persons)):
        common = intersect_intervals(common, free_intervals[persons[i]])
    
    candidate_meetings = []
    for s, e in common:
        if e - s >= meeting_duration:
            t_start = max(s, preference_start)
            if t_start + meeting_duration <= e:
                candidate_meetings.append((t_start, t_start + meeting_duration))
    
    if candidate_meetings:
        candidate_meetings.sort(key=lambda x: x[0])
        meeting_start, meeting_end = candidate_meetings[0]
        time_range_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        print("Monday")
        print(time_range_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()