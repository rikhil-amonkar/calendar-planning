from datetime import timedelta, datetime

# Helper function to convert time string "HH:MM" to minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Helper function to convert minutes since midnight to time string "HH:MM"
def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Function to compute free intervals based on working hours and booked intervals
def get_free_intervals(booked, work_start, work_end):
    free = []
    start = work_start
    for b in sorted(booked, key=lambda x: x[0]):
        if b[0] > start:
            free.append((start, b[0]))
        start = max(start, b[1])
    if start < work_end:
        free.append((start, work_end))
    return free

# Function to compute the intersection between two lists of intervals
def intersect_intervals(intervals1, intervals2):
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find overlap
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersections.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersections

# Parameters
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Booked intervals for each participant by day (times in 24-hour format, as minutes).
# Each booked interval is a tuple (start, end) in minutes.
susan_schedule = {
    "Monday": [(time_to_minutes("12:30"), time_to_minutes("13:00")),
               (time_to_minutes("13:30"), time_to_minutes("14:00"))],
    "Tuesday": [(time_to_minutes("11:30"), time_to_minutes("12:00"))],
    "Wednesday": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
                  (time_to_minutes("14:00"), time_to_minutes("14:30")),
                  (time_to_minutes("15:30"), time_to_minutes("16:30"))]
}

sandra_schedule = {
    "Monday": [(time_to_minutes("09:00"), time_to_minutes("13:00")),
               (time_to_minutes("14:00"), time_to_minutes("15:00")),
               (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
               (time_to_minutes("10:30"), time_to_minutes("12:00")),
               (time_to_minutes("12:30"), time_to_minutes("13:30")),
               (time_to_minutes("14:00"), time_to_minutes("14:30")),
               (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("11:30")),
                  (time_to_minutes("12:00"), time_to_minutes("12:30")),
                  (time_to_minutes("13:00"), time_to_minutes("17:00"))]
}

# Participant constraints
# Susan would rather not meet on Tuesday.
# Sandra cannot meet on Monday after 16:00 (i.e. meeting must end by 16:00 on Monday).
preferred_days = ["Monday", "Wednesday", "Tuesday"]

def find_meeting_time():
    for day in preferred_days:
        # Skip Tuesday for Susan's preference: only consider Tuesday if no other option is found.
        # We try days in the order: Monday, Wednesday, then Tuesday.
        
        # Get free intervals for Susan and Sandra on this day
        susan_booked = susan_schedule.get(day, [])
        sandra_booked = sandra_schedule.get(day, [])
        
        susan_free = get_free_intervals(susan_booked, work_start, work_end)
        sandra_free = get_free_intervals(sandra_booked, work_start, work_end)
        
        # Calculate common free intervals
        common_free = intersect_intervals(susan_free, sandra_free)
        
        # Try to find a common slot that fits the meeting duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                
                # Apply additional constraints: 
                # Sandra cannot meet on Monday after 16:00.
                if day == "Monday" and meeting_start >= time_to_minutes("16:00"):
                    continue
                return day, meeting_start, meeting_end
    return None

result = find_meeting_time()
if result:
    day, meeting_start, meeting_end = result
    print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} on {day}")
else:
    print("No available meeting time found.")

# Expected Output (according to the constraints, a valid meeting time is):
# "13:00:13:30 on Monday"