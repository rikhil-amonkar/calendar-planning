from datetime import time, timedelta, datetime

# Define a helper function to convert a string "HH:MM" to a time object
def str_to_time(t_str):
    return datetime.strptime(t_str, "%H:%M").time()

# Define a helper function to check if a time interval (start, end) fits into a free slot interval (free_start, free_end)
def fits(free_start, free_end, meeting_start, meeting_end):
    return free_start <= meeting_start and meeting_end <= free_end

# Meeting duration in minutes
MEETING_DURATION = 30

# Define office hours
office_start = str_to_time("09:00")
office_end   = str_to_time("17:00")

# Define participants' busy schedules as dictionaries with days as keys and a list of (start, end) busy intervals.
# Times are in "HH:MM" format.
schedules = {
    "Amy": {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [("11:00", "11:30"), ("13:30", "14:00")]
    },
    "Pamela": {
        "Monday": [("09:00", "10:30"), ("11:00", "16:30")],
        "Tuesday": [("09:00", "9:30"), ("10:00", "17:00")],
        "Wednesday": [("09:00", "9:30"), ("10:00", "11:00"), ("11:30", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")]
    }
}

# Pamela's preference: she would like to avoid meetings on Monday,
# and on Tuesday/Wednesday before 16:00.
def meet_satisfies_preference(day, meeting_start):
    # If meeting is on Monday, avoid it.
    if day == "Monday":
        return False
    # For Tuesday/Wednesday, meeting should not start before 16:00.
    if day in ["Tuesday", "Wednesday"]:
        if meeting_start < str_to_time("16:00"):
            return False
    return True

# Calculate the free intervals for a given participant on a particular day
def get_free_intervals(busy_intervals):
    free_intervals = []
    # start with office start
    current_start = office_start
    # Sort busy_intervals by start time
    busy_intervals_sorted = sorted(busy_intervals, key=lambda x: str_to_time(x[0]))
    for b_start, b_end in busy_intervals_sorted:
        b_start_time = str_to_time(b_start)
        b_end_time = str_to_time(b_end)
        if current_start < b_start_time:
            free_intervals.append((current_start, b_start_time))
        current_start = max(current_start, b_end_time)
    if current_start < office_end:
        free_intervals.append((current_start, office_end))
    return free_intervals

# Check for overlapping free intervals between two sets of intervals
def intersect_intervals(intervals1, intervals2):
    result = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            # The overlapping interval is between max(s1,s2) and min(e1,e2)
            overlap_start = max(s1, s2)
            overlap_end = min(e1, e2)
            if overlap_start < overlap_end:
                result.append((overlap_start, overlap_end))
    return result

# Convert a time object to minutes since midnight for easy arithmetic
def time_to_minutes(t):
    return t.hour * 60 + t.minute

# Convert minutes since midnight back to a time object
def minutes_to_time(m):
    return time(m // 60, m % 60)

# Given a free interval, check if a meeting of MEETING_DURATION can be scheduled within it.
def find_meeting_in_interval(interval):
    start, end = interval
    start_minutes = time_to_minutes(start)
    end_minutes = time_to_minutes(end)
    if end_minutes - start_minutes >= MEETING_DURATION:
        return minutes_to_time(start_minutes), minutes_to_time(start_minutes + MEETING_DURATION)
    return None

# Days to consider
days = ["Monday", "Tuesday", "Wednesday"]

# Try to schedule the meeting
proposed_day = None
proposed_start = None
proposed_end = None

# Loop through each day in order, preferring days that satisfy Pamela’s preferences.
for day in days:
    # Get free intervals for each participant
    amy_busy = schedules["Amy"].get(day, [])
    pam_busy = schedules["Pamela"].get(day, [])
    amy_free = get_free_intervals(amy_busy)
    pam_free = get_free_intervals(pam_busy)
    # Get the intersection of free intervals
    common_free = intersect_intervals(amy_free, pam_free)
    
    # For each free interval, try to find a slot that is at least 30 minutes
    for interval in common_free:
        meeting_slot = find_meeting_in_interval(interval)
        if meeting_slot:
            meeting_start, meeting_end = meeting_slot
            # Check Pamela's meeting time preference for this day
            if meet_satisfies_preference(day, meeting_start):
                proposed_day = day
                proposed_start = meeting_start
                proposed_end = meeting_end
                break
    if proposed_day:
        break

# If no slot found that meets the preferences, then choose the earliest available slot
if not proposed_day:
    for day in days:
        amy_busy = schedules["Amy"].get(day, [])
        pam_busy = schedules["Pamela"].get(day, [])
        amy_free = get_free_intervals(amy_busy)
        pam_free = get_free_intervals(pam_busy)
        common_free = intersect_intervals(amy_free, pam_free)
        for interval in common_free:
            meeting_slot = find_meeting_in_interval(interval)
            if meeting_slot:
                proposed_day = day
                proposed_start, proposed_end = meeting_slot
                break
        if proposed_day:
            break

# Format time for output (HH:MM)
def format_time(t):
    return t.strftime("%H:%M")

if proposed_day and proposed_start and proposed_end:
    # Output in the desired format: day and time range HH:MM:HH:MM
    output = f"{proposed_day} {format_time(proposed_start)}:{format_time(proposed_end)}"
    print(output)
else:
    print("No available meeting slot meets the criteria.")