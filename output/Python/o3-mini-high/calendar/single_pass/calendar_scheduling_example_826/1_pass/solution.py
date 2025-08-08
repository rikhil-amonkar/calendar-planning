def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def find_meeting_slot(busy_intervals, work_start=9*60, work_end=17*60, meeting_duration=30):
    # Ensure the busy intervals are sorted
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    
    # Check the window before the first meeting
    if not busy_intervals:
        if work_end - work_start >= meeting_duration:
            return work_start, work_start + meeting_duration
        else:
            return None
    if busy_intervals[0][0] - work_start >= meeting_duration:
        return work_start, work_start + meeting_duration
    
    # Check the gaps between meetings
    prev_end = busy_intervals[0][1]
    for interval in busy_intervals[1:]:
        gap = interval[0] - prev_end
        if gap >= meeting_duration:
            return prev_end, prev_end + meeting_duration
        prev_end = max(prev_end, interval[1])
    
    # Check the time after the last meeting
    if work_end - prev_end >= meeting_duration:
        return prev_end, prev_end + meeting_duration
        
    return None

def main():
    meeting_duration = 30  # in minutes
    work_start = 9 * 60    # 9:00 AM in minutes
    work_end = 17 * 60     # 5:00 PM in minutes

    # James's schedule given as busy intervals for each day (in minutes)
    schedules = {
        "Monday": [
            (9 * 60, 9 * 60 + 30),       # 09:00-09:30
            (10 * 60 + 30, 11 * 60),      # 10:30-11:00
            (12 * 60 + 30, 13 * 60),      # 12:30-13:00
            (14 * 60 + 30, 15 * 60 + 30), # 14:30-15:30
            (16 * 60 + 30, 17 * 60)       # 16:30-17:00
        ],
        "Tuesday": [
            (9 * 60, 11 * 60),           # 09:00-11:00
            (11 * 60 + 30, 12 * 60),      # 11:30-12:00
            (12 * 60 + 30, 15 * 60 + 30), # 12:30-15:30
            (16 * 60, 17 * 60)           # 16:00-17:00
        ],
        "Wednesday": [
            (10 * 60, 11 * 60),          # 10:00-11:00
            (12 * 60, 13 * 60),          # 12:00-13:00
            (13 * 60 + 30, 16 * 60)      # 13:30-16:00
        ],
        "Thursday": [
            (9 * 60 + 30, 11 * 60 + 30), # 09:30-11:30
            (12 * 60, 12 * 60 + 30),      # 12:00-12:30
            (13 * 60, 13 * 60 + 30),      # 13:00-13:30
            (14 * 60, 14 * 60 + 30),      # 14:00-14:30
            (16 * 60 + 30, 17 * 60)       # 16:30-17:00
        ]
    }
    
    # Cheryl is free all week but prefers not to meet on Wednesday.
    # We try scheduling in the order: Monday, Tuesday, Thursday, and lastly Wednesday.
    preferred_days = ["Monday", "Tuesday", "Thursday", "Wednesday"]
    
    meeting_found = False
    for day in preferred_days:
        busy_intervals = schedules.get(day, [])
        slot = find_meeting_slot(busy_intervals, work_start, work_end, meeting_duration)
        if slot:
            start_time, end_time = slot
            print(f"{day} {minutes_to_time_str(start_time)}:{minutes_to_time_str(end_time)}")
            meeting_found = True
            break

    if not meeting_found:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()