def time_to_minutes(time_str):
    # Convert HH:MM to minutes since midnight
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Convert minutes since midnight to HH:MM string
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Given sorted busy intervals, return free intervals between work_start and work_end
    free = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    # Given two lists of intervals, return the list of overlapping intervals
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        # Move to the next interval in the list that finishes earlier.
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def find_common_slot(free_dict, meeting_duration):
    # free_dict is a dictionary: participant -> free intervals
    # Find the intersection of free intervals among all participants and return the earliest slot (if any)
    participants = list(free_dict.keys())
    common = free_dict[participants[0]]
    for p in participants[1:]:
        common = intersect_intervals(common, free_dict[p])
        if not common:
            break
    for start, end in common:
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    return None

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # in minutes

    # Define the busy schedules for each participant in minutes.
    schedule = {
        "Monday": {
            "Bobby": [
                (time_to_minutes("14:30"), time_to_minutes("15:00")),
            ],
            "Michael": [
                (time_to_minutes("09:00"), time_to_minutes("10:00")),
                (time_to_minutes("10:30"), time_to_minutes("13:30")),
                (time_to_minutes("14:00"), time_to_minutes("15:00")),
                (time_to_minutes("15:30"), time_to_minutes("17:00")),
            ]
        },
        "Tuesday": {
            "Bobby": [
                (time_to_minutes("09:00"), time_to_minutes("11:30")),
                (time_to_minutes("12:00"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("15:00")),
                (time_to_minutes("15:30"), time_to_minutes("17:00")),
            ],
            "Michael": [
                (time_to_minutes("09:00"), time_to_minutes("10:30")),
                (time_to_minutes("11:00"), time_to_minutes("11:30")),
                (time_to_minutes("12:00"), time_to_minutes("14:00")),
                (time_to_minutes("15:00"), time_to_minutes("16:00")),
                (time_to_minutes("16:30"), time_to_minutes("17:00")),
            ]
        }
    }

    # Iterate over the days in order of preference
    for day in ["Monday", "Tuesday"]:
        # Compute free intervals for each participant for the day
        free_dict = {}
        for person, busy in schedule[day].items():
            free_dict[person] = get_free_intervals(busy, work_start, work_end)
        slot = find_common_slot(free_dict, meeting_duration)
        if slot is not None:
            start, end = slot
            start_str = minutes_to_time(start)
            end_str = minutes_to_time(end)
            # Output in the format: Day {HH:MM:HH:MM}
            print(f"{day} {{{start_str}:{end_str}}}")
            break

if __name__ == "__main__":
    main()