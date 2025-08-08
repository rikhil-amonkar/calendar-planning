def time_to_minutes(t):
    # t is a string in "HH:MM" format
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, office_start, office_end):
    free = []
    current = office_start
    # Sort busy intervals by start time
    for b in sorted(busy_intervals):
        b_start, b_end = b
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < office_end:
        free.append((current, office_end))
    return free

def schedule_meeting():
    # Meeting parameters
    meeting_duration = 30  # minutes
    office_start = time_to_minutes("09:00")
    office_end   = time_to_minutes("17:00")
    
    # Define candidate days and Ruth's respective busy intervals.
    # Julie is free, but on Thursday she would prefer not to have a meeting starting before 11:30.
    schedules = {
        "Monday":  [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("17:00"))],
        "Thursday": [
            (time_to_minutes("09:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ]
    }
    
    julie_preference = time_to_minutes("11:30")  # She prefers to avoid meetings before 11:30 on Thursday.
    
    # Check each day for a free slot for both
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
        busy_intervals = schedules[day]
        free_intervals = get_free_intervals(busy_intervals, office_start, office_end)
        
        for start, end in free_intervals:
            # We look for a free slot of at least meeting_duration minutes.
            if end - start >= meeting_duration:
                proposed_start = start
                # If it's Thursday, try to honor Julie's preference.
                if day == "Thursday" and proposed_start < julie_preference:
                    # Make sure we can start at julie_preference without overrunning the free interval.
                    if julie_preference + meeting_duration <= end:
                        proposed_start = julie_preference
                    else:
                        # If starting at her preferred time doesn't fit, skip this interval.
                        continue
                # Once we have a valid start time, define the end time.
                proposed_end = proposed_start + meeting_duration
                # Format the times in "HH:MM:HH:MM"
                start_str = minutes_to_time(proposed_start)
                end_str = minutes_to_time(proposed_end)
                print(f"{day} {start_str}:{end_str}")
                return

    print("No suitable meeting time found.")

if __name__ == "__main__":
    schedule_meeting()