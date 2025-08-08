import datetime

def find_meeting_slot():
    # Meeting parameters
    meeting_duration = datetime.timedelta(minutes=30)
    
    # Work hours on Monday
    work_start = datetime.datetime.strptime("09:00", "%H:%M")
    work_end = datetime.datetime.strptime("17:00", "%H:%M")
    
    # Participant schedules on Monday:
    # Judy: free all day
    # Nicole: busy 09:00-10:00 and 10:30-16:30
    busy_intervals = [
        (datetime.datetime.strptime("09:00", "%H:%M"), datetime.datetime.strptime("10:00", "%H:%M")),
        (datetime.datetime.strptime("10:30", "%H:%M"), datetime.datetime.strptime("16:30", "%H:%M"))
    ]
    
    # Nicole prefers not to meet before 16:00
    preferred_start = datetime.datetime.strptime("16:00", "%H:%M")
    
    # Build free intervals within work hours (for Nicole)
    free_intervals = []
    current_start = work_start
    
    for busy_start, busy_end in busy_intervals:
        if busy_start > current_start:
            free_interval = (current_start, busy_start)
            if (busy_start - current_start) >= meeting_duration:
                free_intervals.append(free_interval)
        # Move current start forward after the busy period
        if busy_end > current_start:
            current_start = busy_end

    # Add the interval after the last busy interval, if any
    if work_end - current_start >= meeting_duration:
        free_intervals.append((current_start, work_end))
    
    # Select a free slot that matches Nicole's preference (start not before 16:00)
    for start, end in free_intervals:
        # Adjust start if it's earlier than the preferred start time.
        if start < preferred_start:
            start = preferred_start
        if end - start >= meeting_duration:
            return start, start + meeting_duration

    return None

def format_time(dt):
    return dt.strftime("%H:%M")

def main():
    meeting_slot = find_meeting_slot()
    if meeting_slot:
        meeting_start, meeting_end = meeting_slot
        # Formatting output as {HH:MM:HH:MM} with day of the week
        time_range = "{" + f"{format_time(meeting_start)}:{format_time(meeting_end)}" + "}"
        day = "Monday"
        print(day, time_range)
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()