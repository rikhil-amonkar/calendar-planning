def main():
    import datetime

    # Define work hours (9:00 to 17:00 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60

    # Define days to check in order
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Ruth's schedule (in minutes since midnight)
    ruth_busy = {
        'Monday': [
            (9*60, 10*60),       # 9:00-10:00
            (10*60 + 30, 12*60), # 10:30-12:00
            (12*60 + 30, 14*60 + 30), # 12:30-14:30
            (15*60, 16*60),      # 15:00-16:00
            (16*60 + 30, 17*60)  # 16:30-17:00
        ],
        'Tuesday': [(9*60, 17*60)],   # Entire day blocked
        'Wednesday': [(9*60, 17*60)]  # Entire day blocked
    }

    # Tyler's constraints (prefers no meetings before 16:00 on Monday)
    def is_tyler_available(day, start_min):
        if day == 'Monday' and start_min < 16 * 60:
            return False
        # Check Tyler's explicit busy times (only Tue/Wed in this case)
        return True

    # Find the first available slot
    meeting_duration = 30
    for day in days:
        if day != 'Monday':  # Ruth is fully busy on Tue/Wed
            continue
        
        # Get Ruth's busy intervals for the day
        busy_intervals = ruth_busy.get(day, [])
        busy_intervals.sort()
        
        # Calculate Ruth's free intervals within work hours
        free_ruth = []
        prev_end = work_start
        for start, end in busy_intervals:
            if start > prev_end:
                free_ruth.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free_ruth.append((prev_end, work_end))
        
        # Check each free interval against Tyler's availability
        for start, end in free_ruth:
            # Find earliest start time within this interval that satisfies Tyler
            current_start = start
            while current_start + meeting_duration <= end:
                if is_tyler_available(day, current_start):
                    # Format the time
                    start_time = f"{current_start // 60:02d}:{current_start % 60:02d}"
                    end_time = f"{(current_start + meeting_duration) // 60:02d}:{(current_start + meeting_duration) % 60:02d}"
                    print(f"{day}:{start_time}:{end_time}")
                    return
                current_start += 15  # Check every 15 minutes for flexibility

    print("No suitable time found")

if __name__ == "__main__":
    main()