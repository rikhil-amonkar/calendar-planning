def main():
    # Define work hours: 9:00 to 17:00 (540 to 1020 minutes)
    # Busy times in minutes (half-open intervals [start, end))
    joshua_busy = {
        'Monday': [(15*60, 15*60+30)],   # 15:00-15:30
        'Tuesday': [],  # No need to check Tuesday due to Joyce's schedule
        'Wednesday': []
    }
    
    joyce_busy = {
        'Monday': [
            (9*60, 9*60+30),     # 9:00-9:30
            (10*60, 11*60),       # 10:00-11:00
            (11*60+30, 12*60+30), # 11:30-12:30
            (13*60, 15*60),       # 13:00-15:00
            (15*60+30, 17*60)     # 15:30-17:00
        ],
        'Tuesday': [(9*60, 17*60)],  # Entire day busy
        'Wednesday': [
            (9*60, 9*60+30),      # 9:00-9:30
            (10*60, 11*60),        # 10:00-11:00
            (12*60+30, 15*60+30), # 12:30-15:30
            (16*60, 16*60+30)      # 16:00-16:30
        ]
    }
    
    # Days to check (skip Tuesday)
    days = ['Monday', 'Wednesday']
    
    for day in days:
        # On Monday, start from 12:30 due to Joyce's preference
        start_minute = 12*60+30 if day == 'Monday' else 9*60
        # Last slot starts at 16:30 (ends at 17:00)
        current = start_minute
        while current <= 16*60+30:  # 16:30 in minutes
            end_minute = current + 30  # 30-minute meeting
            
            # Check if slot [current, end_minute) is free for Joshua
            joshua_free = True
            for busy_start, busy_end in joshua_busy[day]:
                if current < busy_end and end_minute > busy_start:
                    joshua_free = False
                    break
            
            if not joshua_free:
                current += 30
                continue
            
            # Check if slot is free for Joyce
            joyce_free = True
            for busy_start, busy_end in joyce_busy[day]:
                if current < busy_end and end_minute > busy_start:
                    joyce_free = False
                    break
            
            if joyce_free:
                # Format the time as HH:MM:HH:MM
                start_hour = current // 60
                start_min = current % 60
                end_hour = end_minute // 60
                end_min = end_minute % 60
                time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
                print(time_str)
                print(day)
                return
            
            current += 30
    
    # Fallback if no slot found (shouldn't happen per problem)
    print("No suitable slot found")

if __name__ == "__main__":
    main()