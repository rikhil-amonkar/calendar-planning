from datetime import datetime, timedelta

# Define work hours and duration
work_start = timedelta(hours=9)
work_end = timedelta(hours=17)
meeting_duration = timedelta(hours=1)

# Define participants' busy schedules
betty_busy = {
    "Monday": [(timedelta(hours=10), timedelta(hours=10, minutes=30)),
               (timedelta(hours=11, minutes=30), timedelta(hours=12, minutes=30)),
               (timedelta(hours=16), timedelta(hours=16, minutes=30))],
    "Tuesday": [(timedelta(hours=9, minutes=30), timedelta(hours=10)),
                (timedelta(hours=10, minutes=30), timedelta(hours=11)),
                (timedelta(hours=12), timedelta(hours=12, minutes=30)),
                (timedelta(hours=13, minutes=30), timedelta(hours=15)),
                (timedelta(hours=16, minutes=30), timedelta(hours=17))],
    "Wednesday": [(timedelta(hours=13, minutes=30), timedelta(hours=14)),
                  (timedelta(hours=14, minutes=30), timedelta(hours=15))],
    "Friday": [(timedelta(hours=9), timedelta(hours=10)),
               (timedelta(hours=11, minutes=30), timedelta(hours=12)),
               (timedelta(hours=12, minutes=30), timedelta(hours=13)),
               (timedelta(hours=14, minutes=30), timedelta(hours=15))]
}

megan_busy = {
    "Monday": [(timedelta(hours=9), timedelta(hours=17))],
    "Tuesday": [(timedelta(hours=9), timedelta(hours=9, minutes=30)),
                (timedelta(hours=10), timedelta(hours=10, minutes=30)),
                (timedelta(hours=12), timedelta(hours=14)),
                (timedelta(hours=15), timedelta(hours=15, minutes=30)),
                (timedelta(hours=16), timedelta(hours=16, minutes=30))],
    "Wednesday": [(timedelta(hours=9, minutes=30), timedelta(hours=10, minutes=30)),
                  (timedelta(hours=11), timedelta(hours=11, minutes=30)),
                  (timedelta(hours=12, minutes=30), timedelta(hours=13)),
                  (timedelta(hours=13, minutes=30), timedelta(hours=14, minutes=30)),
                  (timedelta(hours=15, minutes=30), timedelta(hours=17))],
    "Thursday": [(timedelta(hours=9), timedelta(hours=10, minutes=30)),
                 (timedelta(hours=11, minutes=30), timedelta(hours=14)),
                 (timedelta(hours=14, minutes=30), timedelta(hours=15)),
                 (timedelta(hours=15, minutes=30), timedelta(hours=16, minutes=30))],
    "Friday": [(timedelta(hours=9), timedelta(hours=17))]
}

# Exclude certain days for Betty 
exclude_days = ["Wednesday", "Thursday"]

# Function to find a suitable time for the meeting
def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        if day in exclude_days:
            continue
        
        # Get the busy intervals for both Betty and Megan
        busy_intervals = betty_busy.get(day, []) + megan_busy.get(day, [])
        
        # Create a timeline of busy intervals for the day
        busy_intervals.append((work_start, work_start))  # start of work
        busy_intervals.append((work_end, work_end))      # end of work
        
        # Sort intervals and merge them
        busy_intervals = sorted(busy_intervals)
        
        merged_intervals = []
        current_start, current_end = busy_intervals[0]
        
        for start, end in busy_intervals[1:]:
            if start <= current_end:
                current_end = max(current_end, end)  # extend the end
            else:
                merged_intervals.append((current_start, current_end))
                current_start, current_end = start, end
        
        merged_intervals.append((current_start, current_end))
        
        # Find an available slot for the meeting
        for i in range(len(merged_intervals) - 1):
            end_of_current = merged_intervals[i][1]
            start_of_next = merged_intervals[i + 1][0]
            
            # Calculate the gap
            if start_of_next - end_of_current >= meeting_duration:
                meeting_start = end_of_current
                meeting_end = meeting_start + meeting_duration
                
                # Checking if the meeting fits in the work hours
                if meeting_start >= work_start and meeting_end <= work_end:
                    start_time = (datetime.combine(datetime.today(), datetime.min.time()) + meeting_start).time()
                    end_time = (datetime.combine(datetime.today(), datetime.min.time()) + meeting_end).time()
                    print(f"Time: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}")
                    return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}"

# Call the function
find_meeting_time()