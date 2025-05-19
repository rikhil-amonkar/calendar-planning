from datetime import datetime, timedelta

# Define participant schedules
schedules = {
    "Patrick": [(datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Shirley": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Jeffrey": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Gloria": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Nathan": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Angela": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "David": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Define meeting time and work hours
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Finding a suitable time slot
def find_meeting_time():
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        # Check if all participants are available
        meeting_end = current_time + meeting_duration
        if all(not any(start < meeting_end and current_time < end for start, end in schedules[participant]) for participant in schedules):
            return current_time, meeting_end
        current_time += timedelta(minutes=30)  # Increment time by 30 minutes

# Get proposed meeting time
proposed_start, proposed_end = find_meeting_time()

# Output the result
print(f"Proposed meeting time: {{{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}}}")
print("Day: Monday")