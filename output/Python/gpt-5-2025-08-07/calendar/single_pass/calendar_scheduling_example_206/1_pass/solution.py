from datetime import datetime

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Parameters
day = "Monday"
work_start = to_min("09:00")
work_end = to_min("17:00")
meeting_duration = 30  # minutes

# Participants' busy schedules on Monday
schedules = {
    "Shirley": [("10:30", "11:00"), ("12:00", "12:30")],
    "Jacob": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "15:00")],
    "Stephen": [("11:30", "12:00"), ("12:30", "13:00")],
    "Margaret": [("09:00", "09:30"), ("10:30", "12:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:30", "17:00")],
    "Mason": [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
}

# Convert schedules to minutes
busy_minutes = {}
for person, intervals in schedules.items():
    busy_minutes[person] = [(to_min(s), to_min(e)) for s, e in intervals]

# Preference: Margaret does not want to meet before 14:30 on Monday
earliest_start = max(work_start, to_min("14:30"))

def is_free_for_all(start_time):
    end_time = start_time + meeting_duration
    for person, intervals in busy_minutes.items():
        for s, e in intervals:
            if start_time < e and end_time > s:  # overlap
                return False
    return True

proposed_start = None
for t in range(earliest_start, work_end - meeting_duration + 1, 30):
    if is_free_for_all(t):
        proposed_start = t
        break

if proposed_start is not None:
    proposed_end = proposed_start + meeting_duration
    print(day)
    print(f"{{{to_str(proposed_start)}:{to_str(proposed_end)}}}")
else:
    # As per problem statement, a solution exists, but handle gracefully anyway
    print(day)
    print("{No available slot}")