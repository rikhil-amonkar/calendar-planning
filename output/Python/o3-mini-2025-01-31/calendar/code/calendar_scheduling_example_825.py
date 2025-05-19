def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define working hours in minutes (9:00 to 17:00)
work_start = 9 * 60  # 540
work_end = 17 * 60   # 1020
meeting_duration = 60

# Busy schedules in minutes for each day and participant.
# Each tuple represents (start_time, end_time) in minutes.
schedules = {
    "Monday": {
        "Laura": [(10 * 60 + 30, 11 * 60),   # 10:30-11:00
                  (12 * 60 + 30, 13 * 60),   # 12:30-13:00
                  (14 * 60 + 30, 15 * 60 + 30), # 14:30-15:30
                  (16 * 60, 17 * 60)],      # 16:00-17:00
        "Philip": [(9 * 60, 17 * 60)]         # 9:00-17:00
    },
    "Tuesday": {
        "Laura": [(9 * 60 + 30, 10 * 60),     # 9:30-10:00
                  (11 * 60, 11 * 60 + 30),    # 11:00-11:30
                  (13 * 60, 13 * 60 + 30),    # 13:00-13:30
                  (14 * 60 + 30, 15 * 60),    # 14:30-15:00
                  (16 * 60, 17 * 60)],        # 16:00-17:00
        "Philip": [(9 * 60, 11 * 60),         # 9:00-11:00
                   (11 * 60 + 30, 12 * 60),   # 11:30-12:00
                   (13 * 60, 13 * 60 + 30),   # 13:00-13:30
                   (14 * 60, 14 * 60 + 30),   # 14:00-14:30
                   (15 * 60, 16 * 60 + 30)]   # 15:00-16:30
    },
    "Wednesday": {
        "Laura": [(11 * 60 + 30, 12 * 60),    # 11:30-12:00
                  (12 * 60 + 30, 13 * 60),    # 12:30-13:00
                  (15 * 60 + 30, 16 * 60 + 30)], # 15:30-16:30
        "Philip": [(9 * 60, 10 * 60),          # 9:00-10:00
                   (11 * 60, 12 * 60),         # 11:00-12:00
                   (12 * 60 + 30, 16 * 60),    # 12:30-16:00
                   (16 * 60 + 30, 17 * 60)]    # 16:30-17:00
    },
    "Thursday": {
        "Laura": [(10 * 60 + 30, 11 * 60),     # 10:30-11:00
                  (12 * 60, 13 * 60 + 30),    # 12:00-13:30
                  (15 * 60, 15 * 60 + 30),    # 15:00-15:30
                  (16 * 60, 16 * 60 + 30)],   # 16:00-16:30
        "Philip": [(9 * 60, 10 * 60 + 30),      # 9:00-10:30
                   (11 * 60, 12 * 60 + 30),    # 11:00-12:30
                   (13 * 60, 17 * 60)]         # 13:00-17:00
    }
}

# Additional constraint: Philip cannot meet on Wednesday.
excluded_days = {"Wednesday"}

def is_free(start, end, busy_times):
    """
    Check if a meeting from start to end minutes does not overlap any busy interval.
    Two intervals [a, b) and [c, d) do not overlap if b <= c or d <= a.
    """
    for bstart, bend in busy_times:
        # If the meeting interval overlaps a busy interval, return False.
        if not (end <= bstart or start >= bend):
            return False
    return True

meeting_found = False

# Check each day in the order Monday, Tuesday, Wednesday, Thursday.
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    if day in excluded_days:
        continue  # skip days that are not allowed
    
    # For each valid starting minute within working hours:
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        # Check all participants for this day.
        conflict = False
        for person in schedules[day]:
            if not is_free(start, end, schedules[day][person]):
                conflict = True
                break
        if not conflict:
            # Meeting time found.
            meeting_day = day
            meeting_start_str = minutes_to_time(start)
            meeting_end_str = minutes_to_time(end)
            meeting_found = True
            break
    if meeting_found:
        break

if meeting_found:
    # Output in the required format: day and time range {HH:MM:HH:MM}
    print(f"{meeting_day} {{{meeting_start_str}:{meeting_end_str}}}")
else:
    print("No available meeting time found.")