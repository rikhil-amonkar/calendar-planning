def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    # Ensure busy intervals are sorted by start time
    for interval in sorted(busy_intervals, key=lambda x: time_to_minutes(x[0])):
        start_busy = time_to_minutes(interval[0])
        end_busy = time_to_minutes(interval[1])
        if current < start_busy:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int < end_int:
            intersections.append((start_int, end_int))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(natalie_sched, william_sched, duration):
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    for day in days:
        natalie_busy = natalie_sched.get(day, [])
        william_busy = william_sched.get(day, [])
        
        # Calculate free intervals during working hours for each participant
        natalie_free = get_free_intervals(natalie_busy, work_start, work_end)
        william_free = get_free_intervals(william_busy, work_start, work_end)
        
        # Find common free intervals
        common_free = intersect_intervals(natalie_free, william_free)
        
        # Check if any common interval is long enough for the meeting
        for start, end in common_free:
            if end - start >= duration:
                meeting_start = start
                meeting_end = meeting_start + duration
                return day, minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    return None, None, None

def main():
    meeting_duration = 60  # meeting duration in minutes

    natalie_schedule = {
        "Monday": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"),
                   ("14:00", "14:30"), ("15:00", "16:30")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("12:30", "14:00"),
                    ("16:00", "17:00")],
        "Wednesday": [("11:00", "11:30"), ("16:00", "16:30")],
        "Thursday": [("10:00", "11:00"), ("11:30", "15:00"), ("15:30", "16:00"),
                     ("16:30", "17:00")]
    }

    william_schedule = {
        "Monday": [("09:30", "11:00"), ("11:30", "17:00")],
        "Tuesday": [("09:00", "13:00"), ("13:30", "16:00")],
        "Wednesday": [("09:00", "12:30"), ("13:00", "14:30"),
                      ("15:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                     ("13:00", "14:00"), ("15:00", "17:00")]
    }

    day, start_time, end_time = find_meeting_slot(natalie_schedule, william_schedule, meeting_duration)
    
    if day:
        # Output format: Day HH:MM:HH:MM (e.g., Wednesday 14:30:15:30)
        print(f"{day} {start_time}:{end_time}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()