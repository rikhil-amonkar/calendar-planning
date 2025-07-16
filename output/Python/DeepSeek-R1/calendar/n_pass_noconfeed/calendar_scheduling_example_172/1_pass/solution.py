def main():
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        total_minutes = (hour - 9) * 60 + minute
        return total_minutes

    # Define busy intervals in minutes (relative to 9:00)
    # Patrick: 9:00-9:30, 10:00-10:30, 13:30-14:00, 16:00-16:30
    busy_patrick = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    
    # Kayla: 12:30-13:30, 15:00-15:30, 16:00-16:30
    busy_kayla = [
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
    
    # Carl: 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-17:00
    busy_carl = [
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
    
    # Christian: 9:00-12:30, 13:00-14:00, 14:30-17:00
    busy_christian = [
        (time_to_minutes("9:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
    
    participants_busy = [busy_patrick, busy_kayla, busy_carl, busy_christian]
    meeting_duration = 30  # minutes
    day_end = time_to_minutes("17:00")  # 480 minutes
    
    # Generate all possible start times (every 30 minutes from 0 to 450 inclusive)
    start_times = list(range(0, day_end - meeting_duration + 1, 30))
    
    for s in start_times:
        e = s + meeting_duration
        free = True
        for busy_list in participants_busy:
            for (b_start, b_end) in busy_list:
                if s < b_end and e > b_start:
                    free = False
                    break
            if not free:
                break
        if free:
            # Convert minutes back to time string (HH:MM)
            start_hour = 9 + s // 60
            start_minute = s % 60
            end_hour = 9 + e // 60
            end_minute = e % 60
            
            # Format to HH:MM:HH:MM
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Monday")
            print(time_str)
            return
    
    # Fallback if no slot found (though problem states a solution exists)
    print("No suitable time found")

if __name__ == "__main__":
    main()