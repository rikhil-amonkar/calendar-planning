def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_meeting():
    meeting_duration = 30  # minutes
    work_start = 9 * 60    # 9:00 in minutes
    work_end = 17 * 60     # 17:00 in minutes

    # Julie is free the whole day except she wants to avoid Thursday meetings before 11:30
    # Ruth's busy times are given as:
    # Monday, Tuesday, Wednesday: busy from 9:00 to 17:00 (i.e., no free time)
    # Thursday: busy 9:00-11:00, 11:30-14:30, 15:00-17:00.
    # We'll derive free intervals for each participant based on work hours.
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    for day in days:
        # Julie's availability: full work hours,
        # but on Thursday, she prefers to avoid meetings before 11:30.
        if day == "Thursday":
            julie_free_start = max(work_start, 11 * 60 + 30)  # 11:30 is 690 minutes
        else:
            julie_free_start = work_start
        julie_interval = (julie_free_start, work_end)
        
        # Ruth's free intervals for each day
        if day in ["Monday", "Tuesday", "Wednesday"]:
            # Ruth is busy all day
            ruth_intervals = []
        elif day == "Thursday":
            # Ruth is busy 9:00-11:00, 11:30-14:30, 15:00-17:00.
            # So her free slots within work hours (9:00-17:00) are:
            # from 11:00 to 11:30 and from 14:30 to 15:00.
            ruth_intervals = [
                (9 * 60 + 60 * 11 - (11 * 60 - 9 * 60), 11 * 60 + 30 - (11 * 60 - 9 * 60)),  # dummy incorrect calc, fixing below
            ]
            # Let's calculate correctly in minutes:
            # Busy: 9:00 (540) to 11:00 (660) => free: from 660 to 11:30 (690)
            # Busy: 11:30 (690) to 14:30 (870) => free: from 870 to 15:00 (900)
            ruth_intervals = [
                (660, 690),  # 11:00 to 11:30
                (870, 900)   # 14:30 to 15:00
            ]
        else:
            ruth_intervals = []

        # Try to find a meeting slot that fits both Julie and Ruth.
        for interval in ruth_intervals:
            # Find the intersection of Julie's available time and Ruth's free interval.
            common_start = max(julie_interval[0], interval[0])
            common_end = min(julie_interval[1], interval[1])
            if common_end - common_start >= meeting_duration:
                meeting_start = common_start
                meeting_end = meeting_start + meeting_duration
                return day, minutes_to_str(meeting_start), minutes_to_str(meeting_end)
    
    return None, None, None

if __name__ == "__main__":
    day, start_time, end_time = find_meeting()
    if day:
        # Output in the format: HH:MM:HH:MM and the day of the week
        print(f"{day}, {start_time}:{end_time}")
    else:
        print("No available meeting slot found.")