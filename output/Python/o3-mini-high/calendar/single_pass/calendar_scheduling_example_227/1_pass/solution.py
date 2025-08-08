#!/usr/bin/env python3

def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, start, end):
    free = []
    current = start
    # Sort busy intervals by start time
    for s, e in sorted(busy, key=lambda interval: interval[0]):
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    result = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start > 0:
                result.append((start, end))
    return result

def find_meeting_slot(availabilities, duration):
    # Find intersection across all participants
    common = availabilities[0]
    for other in availabilities[1:]:
        common = intersect_intervals(common, other)
    # Look for an interval that can host the meeting duration
    for s, e in sorted(common):
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    # Define the working day and hours
    day_of_week = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # in minutes

    # Define busy intervals for each participant (times in HH:MM)
    # Natalie is free the entire day.
    busy_natalie = []

    busy_david = [
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ]
    # David does not want to meet before 14:00, so his effective start time is 14:00.
    david_start = max(work_start, time_to_minutes("14:00"))
    
    busy_douglas = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ]
    
    busy_ralph = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    busy_jordan = [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ]

    # Compute free intervals for each participant within work hours
    free_natalie = get_free_intervals(busy_natalie, work_start, work_end)
    free_david   = get_free_intervals(busy_david, david_start, work_end)
    free_douglas = get_free_intervals(busy_douglas, work_start, work_end)
    free_ralph   = get_free_intervals(busy_ralph, work_start, work_end)
    free_jordan  = get_free_intervals(busy_jordan, work_start, work_end)

    # Combine availabilities
    availabilities = [
        free_natalie,
        free_david,
        free_douglas,
        free_ralph,
        free_jordan
    ]

    # Find a common meeting slot
    slot = find_meeting_slot(availabilities, meeting_duration)
    if slot:
        start_str = minutes_to_time(slot[0])
        end_str = minutes_to_time(slot[1])
        # Output format: {day} {HH:MM}:{HH:MM}
        print(f"{day_of_week} {start_str}:{end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()