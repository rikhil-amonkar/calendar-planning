from datetime import timedelta, datetime

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end   = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define each participant's busy intervals on Monday.
# Each busy interval is a tuple (start_time, end_time) in HH:MM format.
busy_times = {
    "Patrick": [("13:30","14:00"), ("14:30","15:00")],
    "Shirley": [("09:00","09:30"), ("11:00","11:30"), ("12:00","12:30"), ("14:30","15:00"), ("16:00","17:00")],
    "Jeffrey": [("09:00","09:30"), ("10:30","11:00"), ("11:30","12:00"), ("13:00","13:30"), ("16:00","17:00")],
    "Gloria":  [("11:30","12:00"), ("15:00","15:30")],
    "Nathan":  [("09:00","09:30"), ("10:30","12:00"), ("14:00","17:00")],
    "Angela":  [("09:00","09:30"), ("10:00","11:00"), ("12:30","15:00"), ("15:30","16:30")],
    "David":   [("09:00","09:30"), ("10:00","10:30"), ("11:00","14:00"), ("14:30","16:30")]
}

# Convert a time string to a datetime object based on the workday date
def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Check if two time intervals [start1, end1) and [start2, end2) overlap
def intervals_overlap(start1, end1, start2, end2):
    return max(start1, start2) < min(end1, end2)

# Given a candidate meeting time, check if it is free for every participant
def is_candidate_free(candidate_start, candidate_end):
    for person, intervals in busy_times.items():
        for interval in intervals:
            busy_start = parse_time(interval[0])
            busy_end   = parse_time(interval[1])
            # If candidate meeting overlaps with any busy interval, return False
            if intervals_overlap(candidate_start, candidate_end, busy_start, busy_end):
                return False
    return True

# Starting from workday_start, check for a candidate meeting slot of meeting_duration
current_time = workday_start
meeting_slot_found = False
candidate_meeting = None

# We'll check in minute increments.
while current_time + meeting_duration <= workday_end:
    candidate_start = current_time
    candidate_end = current_time + meeting_duration
    if is_candidate_free(candidate_start, candidate_end):
        candidate_meeting = (candidate_start, candidate_end)
        meeting_slot_found = True
        break
    current_time += timedelta(minutes=1)

if meeting_slot_found:
    # Format the output as HH:MM:HH:MM and include the day "Monday"
    start_str = candidate_meeting[0].strftime("%H:%M")
    end_str   = candidate_meeting[1].strftime("%H:%M")
    print(f"{start_str}:{end_str} Monday")
else:
    print("No available meeting slot found.")
    
# For this particular schedule, the meeting time found is 09:30 to 10:00 on Monday.