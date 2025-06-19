def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start_minutes = 9 * 60   # 540 minutes
    work_end_minutes = 17 * 60    # 1020 minutes
    meeting_end_deadline = 12 * 60 + 30  # 750 minutes (12:30)

    # Jack's busy times for each day in minutes
    jack_busy_by_day = {
        'Monday': [
            (9*60+30, 10*60+30),   # 09:30-10:30
            (11*60, 11*60+30),      # 11:00-11:30
            (12*60+30, 13*60),      # 12:30-13:00
            (14*60, 14*60+30),      # 14:00-14:30
            (16*60, 16*60+30)       # 16:00-16:30
        ],
        'Tuesday': [
            (10*60, 11*60),         # 10:00-11:00
            (12*60+30, 13*60+30),   # 12:30-13:30
            (14*60+30, 15*60),      # 14:30-15:00
            (15*60, 16*60)          # 15:00-16:00
        ],
        'Wednesday': [
            (9*60+30, 10*60),       # 09:30-10:00
            (11*60+30, 12*60),      # 11:30-12:00
            (14*60, 14*60+30),      # 14:00-14:30
            (15*60, 16*60)          # 15:00-16:00
        ]
    }

    # Charlotte's busy times for each day in minutes
    charlotte_busy_by_day = {
        'Monday': [
            (9*60+30, 10*60),       # 09:30-10:00
            (10*60+30, 12*60),      # 10:30-12:00
            (12*60+30, 13*60+30),   # 12:30-13:30
            (14*60, 16*60)          # 14:00-16:00
        ],
        'Tuesday': [
            (10*60+30, 11*60+30),   # 10:30-11:30
            (12*60, 12*60+30),      # 12:00-12:30
            (13*60+30, 14*60+30),   # 13:30-14:30
            (15*60, 16*60)          # 15:00-16:00
        ],
        'Wednesday': [
            (9*60+30, 10*60+30),   # 09:30-10:30
            (11*60, 12*60+30),     # 11:00-12:30
            (13*60, 14*60),        # 13:00-14:00
            (14*60+30, 16*60)      # 14:30-16:00
        ]
    }

    # Days to check in order
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Function to format minutes to HH:MM
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    for day in days:
        jack_busy = jack_busy_by_day[day]
        charlotte_busy = charlotte_busy_by_day[day]
        
        # Combine and sort all busy intervals for the day
        all_busy = jack_busy + charlotte_busy
        all_busy.sort(key=lambda interval: interval[0])
        
        # Merge overlapping or adjacent intervals
        merged_busy = []
        if all_busy:
            current_start, current_end = all_busy[0]
            for i in range(1, len(all_busy)):
                start, end = all_busy[i]
                if start <= current_end:
                    current_end = max(current_end, end)
                else:
                    merged_busy.append((current_start, current_end))
                    current_start, current_end = start, end
            merged_busy.append((current_start, current_end))
        
        # Calculate free intervals within work hours
        free_intervals = []
        if not merged_busy:
            free_intervals.append((work_start_minutes, work_end_minutes))
        else:
            if work_start_minutes < merged_busy[0][0]:
                free_intervals.append((work_start_minutes, merged_busy[0][0]))
            
            for i in range(len(merged_busy) - 1):
                gap_start = merged_busy[i][1]
                gap_end = merged_busy[i+1][0]
                if gap_start < gap_end:
                    free_intervals.append((gap_start, gap_end))
            
            if merged_busy[-1][1] < work_end_minutes:
                free_intervals.append((merged_busy[-1][1], work_end_minutes))
        
        # Find the earliest 30-minute meeting slot ending by meeting_end_deadline
        meeting_slot = None
        for start, end in free_intervals:
            # The meeting must end by min(end, meeting_end_deadline)
            latest_end = min(end, meeting_end_deadline)
            if latest_end - start >= 30:
                meeting_slot = (start, start + 30)
                break
        
        if meeting_slot is not None:
            start_time = format_time(meeting_slot[0])
            end_time = format_time(meeting_slot[1])
            print(f"{start_time}:{end_time}")
            print(day)
            return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()