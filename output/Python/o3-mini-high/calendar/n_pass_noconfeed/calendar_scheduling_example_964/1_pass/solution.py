def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, work_start, work_end):
    # busy: list of (start, end) tuples (in minutes); work_start/work_end in minutes.
    free = []
    current = work_start
    for start, end in sorted(busy, key=lambda b: b[0]):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Return intersections between two lists of intervals.
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        inter_start = max(s1, s2)
        inter_end = min(e1, e2)
        if inter_start < inter_end:
            intersections.append((inter_start, inter_end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    meeting_duration = 60  # minutes needed for the meeting
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Betty's busy schedule (in HH:MM) by day
    betty_busy = {
        "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("16:00", "16:30")],
        "Tuesday": [("09:30", "10:00"), ("10:30", "11:00"), ("12:00", "12:30"),
                    ("13:30", "15:00"), ("16:30", "17:00")],
        "Wednesday": [("13:30", "14:00"), ("14:30", "15:00")],
        "Friday": [("09:00", "10:00"), ("11:30", "12:00"),
                   ("12:30", "13:00"), ("14:30", "15:00")]
    }
    
    # Megan's busy schedule (in HH:MM) by day
    megan_busy = {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("12:00", "14:00"),
                    ("15:00", "15:30"), ("16:00", "16:30")],
        "Wednesday": [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:00"),
                      ("13:30", "14:30"), ("15:30", "17:00")],
        "Thursday": [("09:00", "10:30"), ("11:30", "14:00"), ("14:30", "15:00"),
                     ("15:30", "16:30")],
        "Friday": [("09:00", "17:00")]
    }
    
    # Convert busy times to minutes for easier calculation.
    for day in betty_busy:
        betty_busy[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in betty_busy[day]]
    for day in megan_busy:
        megan_busy[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in megan_busy[day]]
    
    # Betty cannot meet on Wednesday and Thursday.
    unavailable_for_betty = {"Wednesday", "Thursday"}
    
    # Days to consider: Monday through Friday.
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    for day in days:
        if day in unavailable_for_betty:
            continue
        
        # Get busy intervals for each participant; if none defined, assume an empty list.
        betty_day_busy = betty_busy.get(day, [])
        megan_day_busy = megan_busy.get(day, [])
        
        # Compute free intervals based on working hours.
        betty_free = get_free_intervals(betty_day_busy, work_start, work_end)
        megan_free = get_free_intervals(megan_day_busy, work_start, work_end)
        
        # Find common free intervals.
        common_free = intersect_intervals(betty_free, megan_free)
        
        # Look for an interval that can accommodate the meeting.
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                meeting_start_str = minutes_to_time(meeting_start)
                meeting_end_str = minutes_to_time(meeting_end)
                # Output in the required format: day and time range as HH:MM:HH:MM
                print(f"{day} {meeting_start_str}:{meeting_end_str}")
                return

if __name__ == "__main__":
    main()