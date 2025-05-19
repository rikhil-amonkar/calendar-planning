from datetime import timedelta, datetime

# Participants' busy schedules
amanda_busy = {
    'Monday': [
        (timedelta(hours=9, minutes=0), timedelta(hours=10, minutes=30)),
        (timedelta(hours=11, minutes=0), timedelta(hours=11, minutes=30)),
        (timedelta(hours=12, minutes=30), timedelta(hours=13, minutes=0)),
        (timedelta(hours=13, minutes=30), timedelta(hours=14, minutes=0)),
        (timedelta(hours=14, minutes=30), timedelta(hours=15, minutes=0)),
    ],
    'Tuesday': [
        (timedelta(hours=9, minutes=0), timedelta(hours=9, minutes=30)),
        (timedelta(hours=10, minutes=0), timedelta(hours=10, minutes=30)),
        (timedelta(hours=11, minutes=30), timedelta(hours=12, minutes=0)),
        (timedelta(hours=13, minutes=30), timedelta(hours=14, minutes=30)),
        (timedelta(hours=15, minutes=30), timedelta(hours=16, minutes=0)),
        (timedelta(hours=16, minutes=30), timedelta(hours=17, minutes=0)),
    ]
}

nathan_busy = {
    'Monday': [
        (timedelta(hours=10, minutes=0), timedelta(hours=10, minutes=30)),
        (timedelta(hours=11, minutes=0), timedelta(hours=11, minutes=30)),
        (timedelta(hours=13, minutes=30), timedelta(hours=14, minutes=30)),
        (timedelta(hours=16, minutes=0), timedelta(hours=16, minutes=30)),
    ],
    'Tuesday': [
        (timedelta(hours=9, minutes=0), timedelta(hours=10, minutes=30)),
        (timedelta(hours=11, minutes=0), timedelta(hours=13, minutes=0)),
        (timedelta(hours=13, minutes=30), timedelta(hours=14, minutes=0)),
        (timedelta(hours=14, minutes=30), timedelta(hours=15, minutes=30)),
        (timedelta(hours=16, minutes=0), timedelta(hours=16, minutes=30)),
    ]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

def find_meeting_time(amanda_busy, nathan_busy, duration):
    for day in amanda_busy.keys():
        # Skipping Nathan's busy slots for Monday
        if day == 'Monday':
            continue
        
        amanda_slots = amanda_busy[day]
        nathan_slots = nathan_busy[day]
        
        # Find available slots for both
        for a_start, a_end in amanda_slots:
            for n_start, n_end in nathan_slots:
                # Calculate start and end for the meeting
                start_time = max(a_start, n_start)
                end_time = start_time + duration
                
                if end_time <= min(a_end, n_end):
                    return f"{start_time.seconds//3600}:{(start_time.seconds//60)%60:02d}:{end_time.seconds//3600}:{(end_time.seconds//60)%60:02d}", day

meeting_time, day_of_week = find_meeting_time(amanda_busy, nathan_busy, meeting_duration)
print(meeting_time)
print(day_of_week)