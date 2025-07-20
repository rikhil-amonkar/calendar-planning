def main():
    # Define the day
    day = "Monday"
    
    # Busy intervals in minutes relative to 9:00 (0 minutes = 9:00)
    emily_busy = [(60, 90), (150, 210), (300, 360), (420, 450)]
    melissa_busy = [(30, 60), (330, 360)]
    frank_busy = [(60, 90), (120, 150), (210, 240), (270, 330), (360, 420), (450, 480)]
    
    # Meeting duration in minutes
    duration = 30
    
    # Frank's constraint: meeting must end by 9:30 (30 minutes from 9:00)
    max_end_time = 30
    
    # Candidate slot: [0, 30) minutes (9:00 to 9:30)
    candidate_start = 0
    candidate_end = 30
    
    # Function to check if a time interval [start, end) is free given a list of busy intervals
    def is_free(busy_list, start, end):
        for s, e in busy_list:
            if start < e and end > s:
                return False
        return True
    
    # Check if the candidate slot is free for everyone
    if (is_free(emily_busy, candidate_start, candidate_end) and
        is_free(melissa_busy, candidate_start, candidate_end) and
        is_free(frank_busy, candidate_start, candidate_end)):
        # Format the time to HH:MM
        def format_time(minutes_since_900):
            total_minutes = 9 * 60 + minutes_since_900
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(candidate_start)
        end_str = format_time(candidate_end)
        time_range_str = f"{start_str}:{end_str}"
        
        print(day)
        print(time_range_str)
    else:
        # Since the problem states there is a solution, this should not happen
        print("No suitable time found")

if __name__ == "__main__":
    main()