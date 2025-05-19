def time_to_minutes(time_str):
    # time_str format is "HH:MM"
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy, work_start, work_end):
    # busy is a list of [start, end] times in minutes, sorted by start time.
    free = []
    if work_start < busy[0][0]:
        free.append([work_start, busy[0][0]])
    for i in range(len(busy) - 1):
        if busy[i][1] < busy[i+1][0]:
            free.append([busy[i][1], busy[i+1][0]])
    if busy[-1][1] < work_end:
        free.append([busy[-1][1], work_end])
    return free

def intersect_intervals(list1, list2):
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        # Find the intersection between intervals list1[i] and list2[j]
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            result.append([start, end])
        # Move the pointer that finishes earlier
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_common_free_interval(free_intervals_list, duration):
    # Start with free intervals of first participant
    common = free_intervals_list[0]
    for free in free_intervals_list[1:]:
        common = intersect_intervals(common, free)
    # Now check if one common interval can accommodate the meeting duration
    for interval in common:
        if interval[1] - interval[0] >= duration:
            # Meeting can start at interval[0] and last for duration minutes.
            return interval[0], interval[0] + duration
    return None

def main():
    # Define work day boundaries in minutes (9:00 to 17:00)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # in minutes

    # Busy schedules for each participant (all times in "HH:MM")
    # Convert them to minutes.
    # Stephanie busy: 10:00-10:30, 16:00-16:30
    stephanie_busy = [
        [time_to_minutes("10:00"), time_to_minutes("10:30")],
        [time_to_minutes("16:00"), time_to_minutes("16:30")]
    ]
    # Cheryl busy: 10:00-10:30, 11:30-12:00, 13:30-14:00, 16:30-17:00
    cheryl_busy = [
        [time_to_minutes("10:00"), time_to_minutes("10:30")],
        [time_to_minutes("11:30"), time_to_minutes("12:00")],
        [time_to_minutes("13:30"), time_to_minutes("14:00")],
        [time_to_minutes("16:30"), time_to_minutes("17:00")]
    ]
    # Bradley busy: 9:30-10:00, 10:30-11:30, 13:30-14:00, 14:30-15:00, 15:30-17:00
    bradley_busy = [
        [time_to_minutes("09:30"), time_to_minutes("10:00")],
        [time_to_minutes("10:30"), time_to_minutes("11:30")],
        [time_to_minutes("13:30"), time_to_minutes("14:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("15:30"), time_to_minutes("17:00")]
    ]
    # Steven busy: 9:00-12:00, 13:00-13:30, 14:30-17:00
    steven_busy = [
        [time_to_minutes("09:00"), time_to_minutes("12:00")],
        [time_to_minutes("13:00"), time_to_minutes("13:30")],
        [time_to_minutes("14:30"), time_to_minutes("17:00")]
    ]

    # For each person, calculate the free intervals within the work day.
    stephanie_free = get_free_intervals(stephanie_busy, work_start, work_end)
    cheryl_free = get_free_intervals(cheryl_busy, work_start, work_end)
    bradley_free = get_free_intervals(bradley_busy, work_start, work_end)
    steven_free = get_free_intervals(steven_busy, work_start, work_end)

    # Combine all free intervals into a list
    free_intervals_list = [stephanie_free, cheryl_free, bradley_free, steven_free]

    meeting_slot = find_common_free_interval(free_intervals_list, meeting_duration)
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        day = "Monday"
        # Output in the format: Day and HH:MM:HH:MM (start:end)
        print(f"{day} {{{start_time}:{end_time}}}")
    else:
        print("No common free interval found for the meeting duration.")

if __name__ == "__main__":
    main()