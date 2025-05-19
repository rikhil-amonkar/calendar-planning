def find_meeting_time():
    # Define meeting duration in minutes
    duration = 30

    # Constraints:
    # Work hours: 09:00-17:00 on both days
    # Shirley's busy slots:
    shirley_busy = {
        "Monday": [("10:30", "11:00"), ("12:00", "12:30"), ("16:00", "16:30")],
        "Tuesday": [("09:30", "10:00")]
    }
    # Albert's busy slots:
    albert_busy = {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:30", "11:00"), ("11:30", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")]
    }
    # Preference: Shirley would rather not meet on Tuesday after 10:30.
    
    # We'll represent times in minutes after midnight for easier computation.
    def time_to_minutes(t):
        h, m = map(int, t.split(":"))
        return h * 60 + m

    def minutes_to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    days = ["Monday", "Tuesday"]
    
    # Function to get free intervals for a participant given their busy slots within work hours.
    def free_intervals(busy_slots):
        intervals = []
        current_start = work_start
        # sort busy slots by start time
        busy_slots_sorted = sorted(busy_slots, key=lambda x: time_to_minutes(x[0]))
        for start, end in busy_slots_sorted:
            busy_start, busy_end = time_to_minutes(start), time_to_minutes(end)
            if busy_start > current_start:
                intervals.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        if current_start < work_end:
            intervals.append((current_start, work_end))
        return intervals

    # Check if an interval can accommodate the meeting
    def interval_fits(interval, duration):
        start, end = interval
        return (end - start) >= duration

    found_day = None
    found_start = None

    # We need a time slot that fits for both participants.
    # For each day, compute the free intervals for both and find the intersection.
    for day in days:
        # Get free intervals for Shirley and Albert on the day
        shirley_free = free_intervals(shirley_busy.get(day, []))
        albert_free = free_intervals(albert_busy.get(day, []))
        
        # Find common free intervals (intersection)
        for s_start, s_end in shirley_free:
            for a_start, a_end in albert_free:
                interval_start = max(s_start, a_start)
                interval_end = min(s_end, a_end)
                if interval_end - interval_start >= duration:
                    # For Tuesday, check preference: Shirley would rather not meet after 10:30.
                    # So if day is Tuesday, try to choose a start time not later than 10:30 if possible.
                    if day == "Tuesday":
                        pref_latest_start = time_to_minutes("10:30")
                        if interval_start > pref_latest_start:
                            continue
                        # If interval_start is before pref_latest_start but the meeting would extend beyond it,
                        # still use interval_start if available, as it's meeting early in the slot.
                    found_day = day
                    found_start = interval_start
                    break
            if found_day is not None:
                break
        if found_day is not None:
            break

    if found_day is None or found_start is None:
        return "No suitable meeting time found."
    
    meeting_start = found_start
    meeting_end = meeting_start + duration

    # Format the time as "HH:MM:HH:MM" and include the day.
    result_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    result = f"{result_time} on {found_day}"
    return result

if __name__ == "__main__":
    meeting_time = find_meeting_time()
    print(meeting_time)