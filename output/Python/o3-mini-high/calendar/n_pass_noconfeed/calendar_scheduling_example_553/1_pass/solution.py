def time_to_minutes(time_str):
    # Converts "HH:MM" into minutes since midnight
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Converts minutes since midnight back to "HH:MM" string
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def overlaps(interval1, interval2):
    # Returns True if the two intervals (start, end) overlap.
    start1, end1 = interval1
    start2, end2 = interval2
    return start1 < end2 and candidate_end > start2

def is_slot_free(candidate, busy_intervals):
    candidate_start, candidate_end = candidate
    for interval in busy_intervals:
        # Check if candidate overlaps with any busy interval.
        if candidate_start < interval[1] and candidate_end > interval[0]:
            return False
    return True

# Define meeting and working parameters
meeting_duration = 30  # in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
henry_meeting_deadline = time_to_minutes("10:00")  # Henry prefers not to meet after 10:00

# Define the busy times for Eric and Henry (times in "HH:MM" format)
eric_busy = [("12:00", "13:00"), ("14:00", "15:00")]
henry_busy = [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"),
              ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")]

# Convert busy times into intervals in minutes
eric_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in eric_busy]
henry_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in henry_busy]

# Because Henry prefers not to meet after 10:00, we restrict our search to slots 
# that finish by 10:00 (i.e. candidate_start + meeting_duration <= henry_meeting_deadline)
latest_possible_start = henry_meeting_deadline - meeting_duration

proposed_slot = None
for candidate_start in range(work_start, latest_possible_start + 1):
    candidate_end = candidate_start + meeting_duration
    # Ensure the candidate time is within work hours and Henry's preferred timeframe.
    if candidate_end > work_end or candidate_end > henry_meeting_deadline:
        continue
    candidate = (candidate_start, candidate_end)
    if is_slot_free(candidate, eric_intervals) and is_slot_free(candidate, henry_intervals):
        proposed_slot = candidate
        break

if proposed_slot:
    meeting_day = "Monday"
    start_time = minutes_to_time(proposed_slot[0])
    end_time = minutes_to_time(proposed_slot[1])
    # Output in the format: DAY HH:MM:HH:MM
    print(f"{meeting_day} {start_time}:{end_time}")
else:
    print("No suitable meeting slot found.")