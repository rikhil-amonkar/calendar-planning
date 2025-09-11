def main():
    # Define busy times in minutes since midnight
    russell_busy = {
        'Monday': [(10*60 + 30, 11*60 + 0)],  # 10:30-11:00
        'Tuesday': [(13*60 + 0, 13*60 + 30)]  # 13:00-13:30
    }
    
    alexander_busy = {
        'Monday': [
            (9*60 + 0, 11*60 + 30),  # 9:00-11:30
            (12*60 + 0, 14*60 + 30),  # 12:00-14:30
            (15*60 + 0, 17*60 + 0)    # 15:00-17:00
        ],
        'Tuesday': [
            (9*60 + 0, 10*60 + 0),    # 9:00-10:00
            (13*60 + 0, 14*60 + 0),   # 13:00-14:00
            (15*60 + 0, 15*60 + 30),  # 15:00-15:30
            (16*60 + 0, 16*60 + 30)   # 16:00-16:30
        ]
    }
    
    # Check each day
    days = ['Monday', 'Tuesday']
    for day in days:
        # Iterate over all possible start times (in minutes since midnight)
        for start in range(9*60, 17*60):  # 9:00 to 17:00, but meeting is one hour, so start must be <= 16:00 (16*60)
            if start >= 16*60:
                continue  # end time would be 17:00, which is allowed
            end = start + 60
            
            # Check Russell's availability
            russell_available = True
            for b_start, b_end in russell_busy.get(day, []):
                # Check overlap between [start, end) and [b_start, b_end)
                if start < b_end and b_start < end:
                    russell_available = False
                    break
            if not russell_available:
                continue
            
            # Check Russell's preference for Tuesday
            if day == 'Tuesday':
                # Russell would rather not meet before 13:30 (13*60 + 30 = 810)
                if start < 13*60 + 30:
                    continue
            
            # Check Alexander's availability
            alex_available = True
            for b_start, b_end in alexander_busy.get(day, []):
                if start < b_end and b_start < end:
                    alex_available = False
                    break
            if not alex_available:
                continue
            
            # If both are available, output the time
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            print(f"{time_str} {day}")
            return  # Exit after finding the first valid time
    
    # The problem states there's a solution, so this should not be reached
    print("No solution found")

if __name__ == "__main__":
    main()