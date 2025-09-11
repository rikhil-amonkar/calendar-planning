def main():
    # Define work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480
    meeting_duration = 60

    # Convert each person's busy times to minutes from 9:00
    julie_busy = [
        (0, 30),    # 9:00-9:30
        (120, 150), # 11:00-11:30
        (180, 210), # 12:00-12:30
        (270, 300), # 13:30-14:00
        (420, 480)  # 16:00-17:00
    ]
    
    sean_busy = [
        (0, 30),    # 9:00-9:30
        (240, 270), # 13:00-13:30
        (360, 390), # 15:00-15:30
        (420, 450)  # 16:00-16:30
    ]
    
    lori_busy = [
        (60, 90),   # 10:00-10:30
        (120, 240), # 11:00-13:00
        (390, 480)  # 15:30-17:00
    ]

    # Initialize an array for each minute in the workday
    minutes = [True] * work_end  # 0 to 479 minutes (9:00 to 16:59)
    
    # Mark busy minutes for each person
    for start, end in julie_busy:
        for i in range(start, end):
            if i < work_end:
                minutes[i] = False
                
    for start, end in sean_busy:
        for i in range(start, end):
            if i < work_end:
                minutes[i] = False
                
    for start, end in lori_busy:
        for i in range(start, end):
            if i < work_end:
                minutes[i] = False

    # Find a contiguous free slot of meeting_duration minutes
    start_minute = -1
    for i in range(work_end - meeting_duration + 1):
        if all(minutes[j] for j in range(i, i + meeting_duration)):
            start_minute = i
            break

    # Convert start minute to time format
    total_minutes = start_minute
    hours = total_minutes // 60
    minutes_remainder = total_minutes % 60
    start_time = f"{9 + hours:02d}:{minutes_remainder:02d}"
    
    # Calculate end time
    end_minute = start_minute + meeting_duration
    total_minutes_end = end_minute
    hours_end = total_minutes_end // 60
    minutes_remainder_end = total_minutes_end % 60
    end_time = f"{9 + hours_end:02d}:{minutes_remainder_end:02d}"
    
    print(f"Monday {start_time}:{end_time}")

if __name__ == "__main__":
    main()