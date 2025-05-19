from datetime import datetime, timedelta

# Define meeting parameters
meeting_duration = timedelta(minutes=30)
day_of_week = "Monday"
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define existing schedules as lists of (start, end) times for each participant (as datetime objects)
# Times are represented relative to an arbitrary same day with date "1900-01-01"
def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M")

# Emily's busy times
emily_busy = [
    (parse_time("10:00"), parse_time("10:30")),
    (parse_time("11:30"), parse_time("12:30")),
    (parse_time("14:00"), parse_time("15:00")),
    (parse_time("16:00"), parse_time("16:30"))
]

# Melissa's busy times
melissa_busy = [
    (parse_time("09:30"), parse_time("10:00")),
    (parse_time("14:30"), parse_time("15:00"))
]

# Frank's busy times
frank_busy = [
    (parse_time("10:00"), parse_time("10:30")),
    (parse_time("11:00"), parse_time("11:30")),
    (parse_time("12:30"), parse_time("13:00")),
    (parse_time("13:30"), parse_time("14:30")),
    (parse_time("15:00"), parse_time("16:00")),
    (parse_time("16:30"), parse_time("17:00"))
]
# Frank's extra constraint: Frank does not want any meeting on Monday after 9:30.
# Therefore, the meeting must end by 9:30.

# Combine all participants' busy schedules
all_busy = emily_busy + melissa_busy + frank_busy

# Function that checks if proposed time slot conflicts with any busy slots
def is_free(proposed_start, proposed_end, busy_slots):
    for busy_start, busy_end in busy_slots:
        # Check if proposed meeting overlaps with a busy slot
        if proposed_start < busy_end and busy_start < proposed_end:
            return False
    return True

# Since Frank's constraint requires the meeting to finish by 9:30,
# we set the latest possible end time as 9:30.
latest_end = parse_time("09:30")

# We try to find a meeting time slot between work_start and latest_end
possible_start = work_start
meeting_found = False
proposed_start = None
proposed_end = None

while possible_start + meeting_duration <= latest_end:
    possible_end = possible_start + meeting_duration
    # Check if all participants are free
    if is_free(possible_start, possible_end, all_busy):
        proposed_start = possible_start
        proposed_end = possible_end
        meeting_found = True
        break
    possible_start += timedelta(minutes=1)

if meeting_found:
    # Format output as HH:MM:HH:MM and include day of week
    meeting_time_str = f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}"
    print(f"{day_of_week}, {meeting_time_str}")
else:
    print("No available meeting time found that meets all constraints.")