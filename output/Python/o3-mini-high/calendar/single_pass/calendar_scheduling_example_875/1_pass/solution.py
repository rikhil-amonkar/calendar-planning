def time_to_minutes(time_str):
    # Convert "HH:MM" to total minutes
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes to "HH:MM" string format
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Given sorted busy intervals, find free intervals within work hours.
    free_intervals = []
    # Start of the day until first busy interval
    if busy_intervals:
        if work_start < busy_intervals[0][0]:
            free_intervals.append((work_start, busy_intervals[0][0]))
    else:
        free_intervals.append((work_start, work_end))
        return free_intervals

    # Gaps between busy intervals
    for i in range(len(busy_intervals) - 1):
        if busy_intervals[i][1] < busy_intervals[i+1][0]:
            free_intervals.append((busy_intervals[i][1], busy_intervals[i+1][0]))
    # Last busy interval to end of work day
    if busy_intervals[-1][1] < work_end:
        free_intervals.append((busy_intervals[-1][1], work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    # Find intersections between two sets of intervals
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def main():
    meeting_duration = 60  # in minutes
    work_start = time_to_minutes("09:00")
    work_end   = time_to_minutes("17:00")
    
    # Busy schedules for Natalie (times in "HH:MM")
    natalie_schedule = {
        "Monday": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"),
                   ("14:00", "14:30"), ("15:00", "16:30")],
        "Tuesday": [("09:00", "09:30"), ("10:00", "10:30"), ("12:30", "14:00"),
                    ("16:00", "17:00")],
        "Wednesday": [("11:00", "11:30"), ("16:00", "16:30")],
        "Thursday": [("10:00", "11:00"), ("11:30", "15:00"), ("15:30", "16:00"),
                     ("16:30", "17:00")]
    }
    
    # Busy schedules for William
    william_schedule = {
        "Monday": [("09:30", "11:00"), ("11:30", "17:00")],
        "Tuesday": [("09:00", "13:00"), ("13:30", "16:00")],
        "Wednesday": [("09:00", "12:30"), ("13:00", "14:30"),
                      ("15:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                     ("13:00", "14:00"), ("15:00", "17:00")]
    }
    
    # Convert busy schedules to minutes
    for day in natalie_schedule:
        natalie_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) 
                                 for start, end in natalie_schedule[day]]
    for day in william_schedule:
        william_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) 
                                 for start, end in william_schedule[day]]
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    for day in days:
        natalie_busy = natalie_schedule.get(day, [])
        william_busy = william_schedule.get(day, [])
        # Compute free intervals for each participant
        natalie_free = get_free_intervals(sorted(natalie_busy), work_start, work_end)
        william_free = get_free_intervals(sorted(william_busy), work_start, work_end)
        
        # Find the intersection of these free intervals
        common_free = intersect_intervals(natalie_free, william_free)
        
        # Search for an interval that can accommodate the meeting duration
        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                # Output in the format: Day HH:MM:HH:MM
                print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
                return

if __name__ == "__main__":
    main()