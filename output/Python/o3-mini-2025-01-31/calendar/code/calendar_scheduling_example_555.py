from datetime import datetime, timedelta

# Define workday start and end time
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Meeting duration (in minutes)
meeting_duration = timedelta(minutes=30)

# Randy's busy intervals on Monday (start and end times)
randy_busy = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
    (datetime.strptime("11:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

# Evelyn's constraint: Cannot meet after 13:00, so effective end time is min(13:00, work_end)
evelyn_constraint = datetime.strptime("13:00", "%H:%M")
effective_end = min(work_end, evelyn_constraint)

def is_available(start, end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Check if the candidate meeting overlaps with a busy interval
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

# Find the first available time slot for a meeting on Monday that satisfies everyone's schedule
candidate = work_start
meeting_slot = None

while candidate + meeting_duration <= effective_end:
    meeting_end = candidate + meeting_duration
    if is_available(candidate, meeting_end, randy_busy):
        meeting_slot = (candidate, meeting_end)
        break
    candidate += timedelta(minutes=1)

if meeting_slot:
    start_time_str = meeting_slot[0].strftime("%H:%M")
    end_time_str = meeting_slot[1].strftime("%H:%M")
    print(f"Monday {start_time_str}:{end_time_str}")
else:
    print("No available time slot found.")