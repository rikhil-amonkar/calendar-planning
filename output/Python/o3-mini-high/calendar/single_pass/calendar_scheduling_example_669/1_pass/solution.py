def time_to_minutes(time_str):
    """Convert time string HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string HH:MM."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, start, end):
    """
    Given a sorted list of busy intervals and overall start/end times,
    return a list of free intervals.
    Each interval is a tuple (free_start, free_end).
    """
    free = []
    current = start
    for b_start, b_end in busy:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, return the list of intersections.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def find_meeting_slot(free_intervals, meeting_duration, preferred_cutoff=None):
    """
    From a list of free intervals, find the earliest slot that can fit
    the meeting duration. If preferred_cutoff is given, ensure that
    the meeting starts before that time.
    """
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            # Check Doris' preference: on Monday, meeting should start before 14:00.
            if preferred_cutoff is None or start < preferred_cutoff:
                return start, start + meeting_duration
    return None

def main():
    meeting_duration = 30  # minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Define the schedules:
    # For Jean, only Tuesday has busy times. Monday is completely free.
    # For Doris, Monday busy intervals are as provided, and Tuesday is entirely busy.
    schedules = {
        "Monday": {
            "jean": [],  # Jean has no meetings on Monday.
            "doris": [
                (time_to_minutes("09:00"), time_to_minutes("11:30")),
                (time_to_minutes("12:00"), time_to_minutes("12:30")),
                (time_to_minutes("13:30"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))
            ],
            # Doris would rather not meet on Monday after 14:00.
            "preferred_cutoff": time_to_minutes("14:00")
        },
        "Tuesday": {
            "jean": [
                (time_to_minutes("11:30"), time_to_minutes("12:00")),
                (time_to_minutes("16:00"), time_to_minutes("16:30"))
            ],
            "doris": [
                (time_to_minutes("09:00"), time_to_minutes("17:00"))
            ],
            "preferred_cutoff": None  # No additional preference on Tuesday.
        }
    }
    
    # Try to find a meeting slot on either Monday or Tuesday.
    meeting_found = False
    for day in ["Monday", "Tuesday"]:
        jean_busy = sorted(schedules[day]["jean"])
        doris_busy = sorted(schedules[day]["doris"])
        preferred_cutoff = schedules[day]["preferred_cutoff"]
        
        jean_free = get_free_intervals(jean_busy, work_start, work_end)
        doris_free = get_free_intervals(doris_busy, work_start, work_end)
        
        # Find overlapping free intervals.
        common_free = intersect_intervals(jean_free, doris_free)
        
        slot = find_meeting_slot(common_free, meeting_duration, preferred_cutoff)
        if slot:
            start_minutes, end_minutes = slot
            start_time_str = minutes_to_time(start_minutes)
            end_time_str = minutes_to_time(end_minutes)
            # Output in the format: Day HH:MM:HH:MM
            print(f"{day} {start_time_str}:{end_time_str}")
            meeting_found = True
            break

    if not meeting_found:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()