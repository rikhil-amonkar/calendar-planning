def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    
    # Define days to check
    days = ["Monday", "Tuesday"]
    
    # Amanda's and Nathan's busy times in minutes since midnight for each day
    amanda_busy = {
        "Monday": [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 11 * 60 + 30),   # 11:00-11:30
            (12 * 60 + 30, 13 * 60),   # 12:30-13:00
            (13 * 60 + 30, 14 * 60),   # 13:30-14:00
            (14 * 60 + 30, 15 * 60),  # 14:30-15:00
        ],
        "Tuesday": [
            (9 * 60, 9 * 60 + 30),     # 9:00-9:30
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60 + 30, 12 * 60),   # 11:30-12:00
            (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
            (15 * 60 + 30, 16 * 60),    # 15:30-16:00
            (16 * 60 + 30, 17 * 60),   # 16:30-17:00
        ]
    }
    
    nathan_busy = {
        "Monday": [
            (10 * 60, 10 * 60 + 30),   # 10:00-10:30
            (11 * 60, 11 * 60 + 30),   # 11:00-11:30
            (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
            (16 * 60, 16 * 60 + 30),   # 16:00-16:30
        ],
        "Tuesday": [
            (9 * 60, 10 * 60 + 30),    # 9:00-10:30
            (11 * 60, 13 * 60),        # 11:00-13:00
            (13 * 60 + 30, 14 * 60),   # 13:30-14:00
            (14 * 60 + 30, 15 * 60 + 30),  # 14:30-15:30
            (16 * 60, 16 * 60 + 30),   # 16:00-16:30
        ]
    }
    
    meeting_duration = 30  # minutes
    
    # Nathan cannot meet on Monday, so remove Monday
    days_to_check = ["Tuesday"]
    
    for day in days_to_check:
        # Get busy intervals for both participants
        amanda_intervals = amanda_busy.get(day, [])
        nathan_intervals = nathan_busy.get(day, [])
        
        # Combine and sort all busy intervals
        all_busy = amanda_intervals + nathan_intervals
        all_busy.sort()
        
        # Merge overlapping or adjacent intervals
        merged_busy = []
        for start, end in all_busy:
            if not merged_busy:
                merged_busy.append((start, end))
            else:
                last_start, last_end = merged_busy[-1]
                if start <= last_end:
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append((start, end))
        
        # Check the time before the first busy interval
        if len(merged_busy) > 0:
            first_start, first_end = merged_busy[0]
            if first_start - work_start >= meeting_duration:
                # Amanda doesn't want to meet on Tuesday after 11:00
                if day == "Tuesday" and work_start >= 11 * 60:
                    continue
                meeting_start = work_start
                meeting_end = meeting_start + meeting_duration
                return day, meeting_start, meeting_end
        
        # Check the time between busy intervals
        for i in range(len(merged_busy) - 1):
            current_end = merged_busy[i][1]
            next_start = merged_busy[i + 1][0]
            if next_start - current_end >= meeting_duration:
                # Amanda doesn't want to meet on Tuesday after 11:00
                if day == "Tuesday" and current_end >= 11 * 60:
                    continue
                meeting_start = current_end
                meeting_end = meeting_start + meeting_duration
                return day, meeting_start, meeting_end
        
        # Check the time after the last busy interval
        if len(merged_busy) > 0:
            last_start, last_end = merged_busy[-1]
            if work_end - last_end >= meeting_duration:
                # Amanda doesn't want to meet on Tuesday after 11:00
                if day == "Tuesday" and last_end >= 11 * 60:
                    continue
                meeting_start = last_end
                meeting_end = meeting_start + meeting_duration
                return day, meeting_start, meeting_end
        else:
            # No busy intervals, any time works
            # Amanda doesn't want to meet on Tuesday after 11:00
            if day == "Tuesday" and work_start >= 11 * 60:
                continue
            meeting_start = work_start
            meeting_end = meeting_start + meeting_duration
            return day, meeting_start, meeting_end
    
    return None

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, start, end = find_meeting_time()
start_time = minutes_to_time(start)
end_time = minutes_to_time(end)
print(f"{day}: {start_time}:{end_time}")