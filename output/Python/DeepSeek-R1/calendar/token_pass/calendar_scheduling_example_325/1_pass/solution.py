def main():
    # Define work hours: 9:00 to 17:00 (0 to 480 minutes from 9:00)
    # Meeting duration: 30 minutes
    # Jose constraint: meeting must end by 15:30 (390 minutes from 9:00)
    # So start time S must satisfy S + 30 <= 390, thus S <= 360 minutes.
    
    # Busy intervals for each person in minutes from 9:00 [start, end)
    busy_times = {
        "Jose": [[120, 150], [210, 240]],
        "Keith": [[300, 330], [360, 390]],
        "Logan": [[0, 60], [180, 210], [360, 390]],
        "Megan": [[0, 90], [120, 180], [240, 270], [330, 450]],
        "Gary": [[0, 30], [60, 90], [150, 240], [270, 300], [330, 450]],
        "Bobby": [[120, 150], [180, 210], [240, 420]]
    }
    
    # List of participants
    participants = list(busy_times.keys())
    
    # Function to check if a person is available for a meeting starting at S
    def is_available(person, S):
        intervals = busy_times[person]
        for start, end in intervals:
            # Check if [S, S+30) overlaps with [start, end)
            if S < end and S + 30 > start:
                return False
        return True
    
    # Check possible start times from 0 to 360 minutes in steps of 30
    found_slot = None
    for S in range(0, 361, 30):  S from 0 to 360 inclusive
        # Check if all participants are available at S
        all_available = True
        for person in participants:
            if not is_available(person, S):
                all_available = False
                break
        if all_available:
            found_slot = S
            break
    
    if found_slot is None:
        print("No suitable time found.")
    else:
        # Convert start time to hours and minutes
        start_minutes = found_slot
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        # Format the time as HH:MM:HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday {time_str}")

if __name__ == "__main__":
    main()