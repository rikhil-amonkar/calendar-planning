from datetime import timedelta, datetime

# Utility functions to convert between "HH:MM" and minutes since midnight.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Function to compute free intervals given busy intervals and working range.
def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    # Sort busy intervals by start time.
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Function to intersect two lists of intervals.
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap between intervals.
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Advance the pointer with the smaller end time.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Meeting parameters
meeting_duration = 30  # in minutes

# Work day start and end times in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define schedules (in "HH:MM" format) for Arthur and Michael.
schedules = {
    "Arthur": {
        "Monday": [("11:00", "11:30"), ("13:30", "14:00"), ("15:00", "15:30")],
        # Arthur cannot meet on Tuesday, so we skip Tuesday for him.
        "Wednesday": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:00", "14:30"), ("16:00", "16:30")]
    },
    "Michael": {
        "Monday": [("09:00", "12:00"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("09:30", "11:30"), ("12:00", "13:30"), ("14:00", "15:30")],
        "Wednesday": [("10:00", "12:30"), ("13:00", "13:30")]
    }
}

# Days to consider
days = ["Monday", "Tuesday", "Wednesday"]

# Since Arthur cannot meet on Tuesday, we remove Tuesday from his schedule.
if "Tuesday" in days:
    # Only include Tuesday if all participants can attend.
    # Arthur is not available on Tuesday so we remove that day.
    days = [day for day in days if day != "Tuesday"]

# Find earliest available meeting slot that works for all.
found_slot = False
for day in days:
    # For each day, get the free intervals for each participant.
    free_intervals_all = []
    
    for person, person_sched in schedules.items():
        # If the person doesn't have any schedule on this day, they're free the whole workday.
        busy_intervals = []
        if day in person_sched:
            # Convert busy times into minutes tuples.
            busy_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in person_sched[day]]
        
        free_intervals = get_free_intervals(busy_intervals, work_start, work_end)
        free_intervals_all.append(free_intervals)
    
    # Intersect free intervals of all participants.
    common_free = free_intervals_all[0]
    for other in free_intervals_all[1:]:
        common_free = intersect_intervals(common_free, other)
        if not common_free:
            break  # No common free time on this day.
    
    # Check for a slot at least meeting_duration long.
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            found_slot = True
            break
    if found_slot:
        break

if not found_slot:
    print("No available meeting slot found.")