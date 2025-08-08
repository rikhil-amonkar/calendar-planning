def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    # Sort busy intervals by start time
    busy = sorted(busy, key=lambda x: x[0])
    free = []
    # First free time from work_start to first busy start (if any)
    if not busy:
        return [(work_start, work_end)]
    if work_start < busy[0][0]:
        free.append((work_start, busy[0][0]))
    # Gaps between busy intervals
    for i in range(1, len(busy)):
        if busy[i-1][1] < busy[i][0]:
            free.append((busy[i-1][1], busy[i][0]))
    # Last gap from end of last busy to work_end
    if busy[-1][1] < work_end:
        free.append((busy[-1][1], work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    for a_start, a_end in intervals1:
        for b_start, b_end in intervals2:
            start = max(a_start, b_start)
            end = min(a_end, b_end)
            if end > start:
                intersections.append((start, end))
    return intersections

def find_meeting_slot():
    meeting_duration = 60  # in minutes
    work_start = 9 * 60    # 9:00 in minutes
    work_end   = 17 * 60   # 17:00 in minutes

    # Busy schedules in minutes (start, end)
    diane_busy = {
        "Monday": [(12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
        "Tuesday": [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
        "Wednesday": [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
        "Thursday": [(15 * 60 + 30, 16 * 60 + 30)],
        "Friday": [(9 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
    }
    
    matthew_busy = {
        "Monday": [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
        "Tuesday": [(9 * 60, 17 * 60)],
        "Wednesday": [(9 * 60, 11 * 60), (12 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
        "Thursday": [(9 * 60, 16 * 60)],
        "Friday": [(9 * 60, 17 * 60)]
    }
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    for day in days:
        # Get free intervals for each
        d_free = get_free_intervals(diane_busy.get(day, []), work_start, work_end)
        m_free = get_free_intervals(matthew_busy.get(day, []), work_start, work_end)
        # Find common free intervals
        common = intersect_intervals(d_free, m_free)
        # If it's Wednesday, enforce Matthew's preference that meeting not start before 12:30 (750 minutes)
        for interval in common:
            start, end = interval
            if day == "Wednesday" and start < 12 * 60 + 30:
                start = max(start, 12 * 60 + 30)
            # If this interval can accommodate the meeting
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                start_str = minutes_to_str(meeting_start)
                end_str = minutes_to_str(meeting_end)
                # Output in format HH:MM:HH:MM along with the day of the week.
                print(f"{day} {start_str}:{end_str}")
                return
    print("No available slot found.")

if __name__ == "__main__":
    find_meeting_slot()