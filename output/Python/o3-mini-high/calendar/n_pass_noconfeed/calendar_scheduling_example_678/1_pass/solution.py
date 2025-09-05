def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_common = max(start1, start2)
        end_common = min(end1, end2)
        if start_common < end_common:
            common.append((start_common, end_common))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

def find_meeting_slot(day, busy_russell, busy_alex, work_start, work_end, meeting_duration, extra_constraint=None):
    free_russell = get_free_intervals(busy_russell, work_start, work_end)
    free_alex = get_free_intervals(busy_alex, work_start, work_end)
    
    # Apply extra constraint (e.g., Tuesday: Russell not before 13:30)
    if extra_constraint is not None:
        adjusted = []
        for start, end in free_russell:
            if end <= extra_constraint:
                continue
            adjusted.append((max(start, extra_constraint), end))
        free_russell = adjusted

    common_free = intersect_intervals(free_russell, free_alex)
    for start, end in common_free:
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    return None

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # in minutes

    schedule = {
        "Monday": {
            "Russell": [("10:30", "11:00")],
            "Alexander": [("09:00", "11:30"), ("12:00", "14:30"), ("15:00", "17:00")]
        },
        "Tuesday": {
            "Russell": [("13:00", "13:30")],
            "Alexander": [("09:00", "10:00"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")]
        }
    }

    # Check Monday first, then Tuesday.
    for day in ["Monday", "Tuesday"]:
        busy_russell = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedule[day]["Russell"]]
        busy_alex = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedule[day]["Alexander"]]
        
        extra = None
        if day == "Tuesday":
            # Russell would rather not meet on Tuesday before 13:30.
            extra = time_to_minutes("13:30")
    
        slot = find_meeting_slot(day, busy_russell, busy_alex, work_start, work_end, meeting_duration, extra)
        if slot:
            start, end = slot
            meeting_time = f"{minutes_to_str(start)}:{minutes_to_str(end)}"
            print(day, meeting_time)
            break

if __name__ == "__main__":
    main()