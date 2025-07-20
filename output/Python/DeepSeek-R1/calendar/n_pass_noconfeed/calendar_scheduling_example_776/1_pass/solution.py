def main():
    work_start = 9 * 60   # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    avoid_monday_after = 14 * 60 + 30  # 14:30 in minutes
    meeting_duration = 30  # minutes

    # Jennifer's busy intervals (start inclusive, end exclusive) in minutes
    jennifer_busy = {
        'Monday': [
            (9*60, 11*60),      # 9:00-11:00
            (11*60+30, 13*60),  # 11:30-13:00
            (13*60+30, 14*60+30),  # 13:30-14:30
            (15*60, 17*60)      # 15:00-17:00
        ],
        'Tuesday': [
            (9*60, 11*60+30),  # 9:00-11:30
            (12*60, 17*60)      # 12:00-17:00
        ],
        'Wednesday': [
            (9*60, 11*60+30),  # 9:00-11:30
            (12*60, 12*60+30), # 12:00-12:30
            (13*60, 14*60),    # 13:00-14:00
            (14*60+30, 16*60), # 14:30-16:00
            (16*60+30, 17*60)  # 16:30-17:00
        ]
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    for day in days:
        busy_intervals = sorted(jennifer_busy[day])
        free_blocks = []
        current = work_start
        
        # Compute free blocks within work hours
        for start, end in busy_intervals:
            if current < start:
                free_blocks.append((current, start))
            current = end
        if current < work_end:
            free_blocks.append((current, work_end))
            
        # Adjust free blocks on Monday to avoid after 14:30
        if day == 'Monday':
            adjusted_blocks = []
            for s, e in free_blocks:
                if e <= avoid_monday_after:
                    adjusted_blocks.append((s, e))
                elif s < avoid_monday_after:
                    adjusted_blocks.append((s, avoid_monday_after))
            free_blocks = adjusted_blocks
        
        # Find first suitable free block
        for s, e in free_blocks:
            if e - s >= meeting_duration:
                meeting_start = s
                meeting_end = s + meeting_duration
                # Format time to HH:MM strings
                start_hr, start_min = divmod(meeting_start, 60)
                end_hr, end_min = divmod(meeting_end, 60)
                time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return
                
    print("No suitable time found")  # Should not happen per problem statement

if __name__ == "__main__":
    main()