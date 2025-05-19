from datetime import datetime, timedelta

# Function to find a suitable time for a meeting
def find_meeting_time():
    # Participants' busy schedules
    busy_times = {
        'Jose': [(datetime(2023, 10, 23, 11, 0), datetime(2023, 10, 23, 11, 30)),
                 (datetime(2023, 10, 23, 12, 30), datetime(2023, 10, 23, 13, 0))],
        'Keith': [(datetime(2023, 10, 23, 14, 0), datetime(2023, 10, 23, 14, 30)),
                  (datetime(2023, 10, 23, 15, 0), datetime(2023, 10, 23, 15, 30))],
        'Logan': [(datetime(2023, 10, 23, 9, 0), datetime(2023, 10, 23, 10, 0)),
                  (datetime(2023, 10, 23, 12, 0), datetime(2023, 10, 23, 12, 30)),
                  (datetime(2023, 10, 23, 15, 0), datetime(2023, 10, 23, 15, 30))],
        'Megan': [(datetime(2023, 10, 23, 9, 0), datetime(2023, 10, 23, 10, 30)),
                  (datetime(2023, 10, 23, 11, 0), datetime(2023, 10, 23, 12, 0)),
                  (datetime(2023, 10, 23, 13, 0), datetime(2023, 10, 23, 13, 30)),
                  (datetime(2023, 10, 23, 14, 30), datetime(2023, 10, 23, 16, 30))],
        'Gary': [(datetime(2023, 10, 23, 9, 0), datetime(2023, 10, 23, 9, 30)),
                 (datetime(2023, 10, 23, 10, 0), datetime(2023, 10, 23, 10, 30)),
                 (datetime(2023, 10, 23, 11, 30), datetime(2023, 10, 23, 13, 0)),
                 (datetime(2023, 10, 23, 13, 30), datetime(2023, 10, 23, 14, 0)),
                 (datetime(2023, 10, 23, 14, 30), datetime(2023, 10, 23, 16, 30))],
        'Bobby': [(datetime(2023, 10, 23, 11, 0), datetime(2023, 10, 23, 11, 30)),
                  (datetime(2023, 10, 23, 12, 0), datetime(2023, 10, 23, 12, 30)),
                  (datetime(2023, 10, 23, 13, 0), datetime(2023, 10, 23, 16, 0))]
    }
    
    # Available meeting time slots
    meeting_duration = timedelta(minutes=30)
    meeting_end_time = datetime(2023, 10, 23, 15, 30)
    
    # Define the work hours
    start_time = datetime(2023, 10, 23, 9, 0)
    end_time = datetime(2023, 10, 23, 17, 0)

    for start in range(0, (end_time - start_time).seconds // 60, 30):
        proposed_start = start_time + timedelta(minutes=start)
        proposed_end = proposed_start + meeting_duration
        
        if proposed_end > end_time or proposed_start > meeting_end_time:
            continue
        
        if all(not (proposed_start < end and proposed_end > start) for busy in busy_times.values() for start, end in busy):
            return f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}", "Monday"

# Output the proposed meeting time
proposed_time, day = find_meeting_time()
print(proposed_time, day)