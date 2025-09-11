def main():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes

    # Meeting duration in minutes
    meeting_duration = 30

    # Participants' busy intervals in minutes from 00:00 (but we consider 9:00 as 0 offset later)
    # Convert each meeting to minutes since 9:00 (so 9:00 becomes 0)
    schedules = {
        "John": [
            (11*60 + 30 - work_start, 12*60 - work_start),      # 11:30-12:00 -> (150, 180)
            (14*60 - work_start, 14*60 + 30 - work_start)        # 14:00-14:30 -> (300, 330)
        ],
        "Megan": [
            (12*60 - work_start, 12*60 + 30 - work_start),       # 12:00-12:30 -> (180, 210)
            (14*60 - work_start, 15*60 - work_start),            # 14:00-15:00 -> (300, 360)
            (15*60 + 30 - work_start, 16*60 - work_start)        # 15:30-16:00 -> (390, 420)
        ],
        "Brandon": [],  # No meetings
        "Kimberly": [
            (9*60 - work_start, 9*60 + 30 - work_start),         # 9:00-9:30 -> (0, 30)
            (10*60 - work_start, 10*60 + 30 - work_start),       # 10:00-10:30 -> (60, 90)
            (11*60 - work_start, 14*60 + 30 - work_start),       # 11:00-14:30 -> (120, 330)
            (15*60 - work_start, 16*60 - work_start),            # 15:00-16:00 -> (360, 420)
            (16*60 + 30 - work_start, 17*60 - work_start)        # 16:30-17:00 -> (450, 480)
        ],
        "Sean": [
            (10*60 - work_start, 11*60 - work_start),            # 10:00-11:00 -> (60, 120)
            (11*60 + 30 - work_start, 14*60 - work_start),       # 11:30-14:00 -> (150, 300)
            (15*60 - work_start, 15*60 + 30 - work_start)        # 15:00-15:30 -> (360, 390)
        ],
        "Lori": [
            (9*60 - work_start, 9*60 + 30 - work_start),         # 9:00-9:30 -> (0, 30)
            (10*60 + 30 - work_start, 12*60 - work_start),       # 10:30-12:00 -> (90, 180)
            (13*60 - work_start, 14*60 + 30 - work_start),       # 13:00-14:30 -> (240, 330)
            (16*60 - work_start, 16*60 + 30 - work_start)        # 16:00-16:30 -> (420, 450)
        ]
    }

    # Check every possible start time from 9:00 to 16:30 (in minutes from 9:00)
    for start_minutes in range(0, work_end - work_start - meeting_duration + 1, 5):  # Step by 5 minutes for finer granularity
        end_minutes = start_minutes + meeting_duration
        # Check if the time slot is free for all participants
        free = True
        for person, busy_slots in schedules.items():
            for busy_start, busy_end in busy_slots:
                # Check for overlap: if the proposed slot overlaps with any busy slot
                if not (end_minutes <= busy_start or start_minutes >= busy_end):
                    free = False
                    break
            if not free:
                break
        
        if free:
            # Convert start_minutes back to time from 9:00 base
            total_minutes_start = work_start + start_minutes
            total_minutes_end = total_minutes_start + meeting_duration
            
            # Format hours and minutes
            start_hour = total_minutes_start // 60
            start_minute = total_minutes_start % 60
            end_hour = total_minutes_end // 60
            end_minute = total_minutes_end % 60
            
            # Format as HH:MM
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(f"Monday {time_str}")
            return

    print("No suitable time found")

if __name__ == "__main__":
    main()