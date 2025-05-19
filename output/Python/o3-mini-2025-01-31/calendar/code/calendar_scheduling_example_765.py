from datetime import timedelta

# Convert HH:MM string to minutes since midnight
def time_to_minutes(t):
    hh, mm = map(int, t.split(":"))
    return hh * 60 + mm

# Convert minutes since midnight to HH:MM format
def minutes_to_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Work hours: 09:00 to 17:00
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy schedules in minutes for each participant per day.
# Each busy interval is a tuple: (start, end)
# Days: Monday, Tuesday, Wednesday

schedules = {
    "Monday": {
        "Joshua": [
            (time_to_minutes("15:00"), time_to_minutes("15:30"))
        ],
        "Joyce": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("17:00"))
        ]
    },
    "Tuesday": {
        "Joshua": [
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00"))
        ],
        "Joyce": [
            (work_start, work_end)  # Busy whole day
        ]
    },
    "Wednesday": {
        "Joshua": [
            # No meetings for Joshua on Wednesday
        ],
        "Joyce": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("12:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
}

# For Monday, Joyce prefers not to meet before 12:00
def apply_preferences(day, start_min):
    if day == "Monday":
        preferred_start = time_to_minutes("12:00")
        return max(start_min, preferred_start)
    return start_min

# Function to compute free intervals in [work_start, work_end] given busy intervals
def get_free_intervals(busy_intervals):
    free_intervals = []
    current = work_start
    # Sort busy intervals based on start times
    for bstart, bend in sorted(busy_intervals):
        if current < bstart:
            free_intervals.append((current, bstart))
        current = max(current, bend)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

# Function to compute intersection of intervals from two persons
def intersect_intervals(intervals1, intervals2):
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # compute the intersection
        start_int = max(start1, start2)
        end_int = min(end1, end2)
        if start_int < end_int:
            intersections.append((start_int, end_int))
        # Move to next interval from one of the lists
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Find a meeting slot across the days (Monday, Tuesday, Wednesday)
found_slot = False

for day in ["Monday", "Tuesday", "Wednesday"]:
    # Get free intervals for each person
    joshua_free = get_free_intervals(schedules[day].get("Joshua", []))
    joyce_free = get_free_intervals(schedules[day].get("Joyce", []))
    
    # Get overlapping free intervals
    common_free = intersect_intervals(joshua_free, joyce_free)

    # Check common free intervals for a slot of meeting_duration
    for start, end in common_free:
        # Apply day-specific preference. For example, Joyce doesn't prefer Monday before 12:00.
        adjusted_start = apply_preferences(day, start)
        if adjusted_start + meeting_duration <= end:
            meeting_start = adjusted_start
            meeting_end = meeting_start + meeting_duration
            print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} on {day}")
            found_slot = True
            break
    if found_slot:
        break

if not found_slot:
    print("No available meeting slot found.")