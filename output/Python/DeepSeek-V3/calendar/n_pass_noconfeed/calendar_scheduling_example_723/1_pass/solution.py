def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Arthur's schedule: {day: list of (start, end) meetings in minutes}
    arthur_schedule = {
        'Monday': [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
        'Tuesday': [(13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],
        'Wednesday': [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }
    
    # Michael's schedule: {day: list of (start, end) meetings in minutes}
    michael_schedule = {
        'Monday': [(9 * 60, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)],
        'Tuesday': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 13 * 60 + 30), (14 * 60, 15 * 60 + 30)],
        'Wednesday': [(10 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30)]
    }
    
    # Arthur cannot meet on Tuesday
    excluded_days = ['Tuesday']
    
    meeting_duration = 30  # minutes
    
    for day in days:
        if day in excluded_days:
            continue
        
        # Combine and sort all meetings for both participants on this day
        all_meetings = []
        for meeting in arthur_schedule.get(day, []):
            all_meetings.append(meeting)
        for meeting in michael_schedule.get(day, []):
            all_meetings.append(meeting)
        
        # Sort meetings by start time
        all_meetings.sort()
        
        # Check the time before the first meeting
        if len(all_meetings) > 0:
            first_meeting_start = all_meetings[0][0]
            if first_meeting_start - work_start >= meeting_duration:
                start_time = work_start
                end_time = start_time + meeting_duration
                return day, start_time, end_time
        
        # Check gaps between meetings
        for i in range(len(all_meetings) - 1):
            current_end = all_meetings[i][1]
            next_start = all_meetings[i + 1][0]
            if next_start - current_end >= meeting_duration:
                start_time = current_end
                end_time = start_time + meeting_duration
                return day, start_time, end_time
        
        # Check the time after the last meeting
        if len(all_meetings) > 0:
            last_meeting_end = all_meetings[-1][1]
            if work_end - last_meeting_end >= meeting_duration:
                start_time = last_meeting_end
                end_time = start_time + meeting_duration
                return day, start_time, end_time
        else:
            # No meetings at all on this day
            start_time = work_start
            end_time = start_time + meeting_duration
            return day, start_time, end_time
    
    return None  # No time found (though the problem states there is a solution)

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, start_time, end_time = find_meeting_time()
start_str = minutes_to_time(start_time)
end_str = minutes_to_time(end_time)
print(f"{day}: {start_str}:{end_str}")