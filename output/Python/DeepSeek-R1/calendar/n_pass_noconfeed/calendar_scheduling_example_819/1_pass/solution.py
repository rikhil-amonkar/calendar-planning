def time_to_min(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define days to check
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Julie's free intervals in minutes (start, end) for each day
# Julie is free 9:00-17:00 on Mon, Tue, Wed; on Thu, avoid before 11:30 -> free from 11:30 to 17:00
julie_free = {
    'Monday': [(time_to_min('09:00'), time_to_min('17:00'))],
    'Tuesday': [(time_to_min('09:00'), time_to_min('17:00'))],
    'Wednesday': [(time_to_min('09:00'), time_to_min('17:00'))],
    'Thursday': [(time_to_min('11:30'), time_to_min('17:00'))]
}

# Ruth's free intervals in minutes (start, end) for each day
# Ruth is free on Thursday: 11:00-11:30 and 14:30-15:00
ruth_free = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [],
    'Thursday': [
        (time_to_min('11:00'), time_to_min('11:30')),
        (time_to_min('14:30'), time_to_min('15:00'))
    ]
}

# Meeting duration in minutes
meeting_duration = 30

# Iterate through each day to find a suitable time
for day in days:
    julie_intervals = julie_free[day]
    ruth_intervals = ruth_free[day]
    
    # Check all interval pairs for Julie and Ruth on this day
    for j_start, j_end in julie_intervals:
        for r_start, r_end in ruth_intervals:
            # Find the overlapping interval
            overlap_start = max(j_start, r_start)
            overlap_end = min(j_end, r_end)
            overlap_duration = overlap_end - overlap_start
            
            # Check if the overlap is sufficient for the meeting
            if overlap_duration >= meeting_duration:
                # Schedule the meeting at the beginning of the overlap
                meeting_start = overlap_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert times to HH:MM format
                start_str = min_to_time(meeting_start)
                end_str = min_to_time(meeting_end)
                
                # Output the day and time range in HH:MM:HH:MM format
                print(day)
                print(f"{start_str}:{end_str}")
                exit(0)

# If no slot is found (though the problem states there is a solution)
print("No suitable time found")