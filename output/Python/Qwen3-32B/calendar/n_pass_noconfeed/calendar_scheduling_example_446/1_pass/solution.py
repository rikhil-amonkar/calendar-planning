def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if prev_end < start:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def interval_intersection(a, b):
    i = 0
    j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    participants = [
        {
            'name': 'Megan',
            'busy': [
                (540, 570),
                (600, 660),
                (720, 750)
            ]
        },
        {
            'name': 'Christine',
            'busy': [
                (540, 570),
                (690, 720),
                (780, 840),
                (930, 990)
            ]
        },
        {
            'name': 'Gabriel',
            'busy': []
        },
        {
            'name': 'Sara',
            'busy': [
                (690, 720),
                (870, 900)
            ]
        },
        {
            'name': 'Bruce',
            'busy': [
                (570, 600),
                (630, 720),
                (750, 840),
                (870, 900),
                (930, 990)
            ]
        },
        {
            'name': 'Kathryn',
            'busy': [
                (600, 930),
                (960, 990)
            ]
        },
        {
            'name': 'Billy',
            'busy': [
                (540, 570),
                (660, 690),
                (720, 840),
                (870, 930)
            ]
        }
    ]

    # Get the first participant's free intervals
    common_intervals = get_free_intervals(participants[0]['busy'], work_start, work_end)
    for p in participants[1:]:
        next_intervals = get_free_intervals(p['busy'], work_start, work_end)
        common_intervals = interval_intersection(common_intervals, next_intervals)
        if not common_intervals:
            break

    # Find the first interval that can fit a 30-minute meeting
    for start, end in common_intervals:
        if end - start >= 30:
            start_time = min_to_time(start)
            end_time = min_to_time(end)
            # Since the meeting is 30 minutes, we can pick any 30 min within the interval
            # For simplicity, pick the earliest possible
            # The earliest possible is start to start + 30
            # But the end may be later than that. But the problem says to output the time range
            # However, the problem says the meeting is 30 minutes, but the output is the time range that works for all.
            # Wait, the problem says the output should be in the format {HH:MM:HH:MM} for the proposed time.
            # Since the meeting is 30 minutes, the proposed time must be a 30-minute block. So for example, if the interval is from 990 to 1020 (30 minutes), then the output is 16:30:17:00.

            # So we need to pick a 30-minute block within the interval. Since the interval is already at least 30 minutes, we can just take the first possible 30 minutes.

            # But in our code, the common_intervals are the overlapping intervals. For example, if the overlapping interval is (990, 1020), then the meeting can be 990 to 1020. So the output is 16:30:17:00.

            # So we can take the start and end of the interval, but ensure that end - start >= 30. But since we already check that, we can just output the entire interval.

            # However, the problem says the meeting is half an hour. So the output should be a time range that is exactly 30 minutes. But the code finds intervals that are at least 30 minutes. So the earliest possible is start to start + 30.

            # But the problem's example solution output is {14:30:15:30} which is a 60-minute block? Wait no, the example solution's output is {14:30:15:30} which is one hour. Wait no, maybe the example is different. Wait the example given in the problem is different from the current problem. Let me check.

            # The current problem's example is not provided. The current task is to find a 30-minute meeting. So the code needs to output a time range that is exactly 30 minutes. But the code's common_intervals may have longer intervals. So how to pick one?

            # Since the problem says there's a solution, we can just pick the first interval and output its start and start + 30.

            # However, the problem says the output should be the time range that works for everyone. So the entire interval must be free for all. For example, if the interval is from 990 (16:30) to 1020 (17:00), then the entire interval is free. So the meeting can be scheduled during that entire interval. But the problem says the meeting is 30 minutes. So the output is the start and end of the 30-minute block. But since the entire interval is free, any 30-minute block within it is acceptable. The problem's solution example in the initial message may have a different approach, but the user's task says to output the time range in the format {HH:MM:HH:MM} which is the start and end of the meeting. Since the meeting is 30 minutes, the end is start + 30 minutes.

            # However, in the code's common_intervals, the intervals are the maximum possible free time. For example, if the common interval is (990, 1020), then the meeting can be scheduled from 990 to 1020. So the output is 16:30:17:00.

            # Therefore, in the code, once we find such an interval, we can output the start and start + 30 minutes. But how to calculate that?

            # Alternatively, since the code is to find any possible 30-minute block within the common intervals, perhaps the code can just output the start and end of the interval, as long as it's at least 30 minutes. But the problem's example may require that.

            # Wait the user's example says "the output of the generated code must include both the time range (like {14:30:15:30}) and the day of the week." So the format is {HH:MM:HH:MM}, which is the start and end times of the meeting. Since the meeting is 30 minutes, the end is start + 30 minutes. However, if the common interval is longer than 30 minutes, we can choose any 30-minute block within it. For simplicity, we can choose the earliest possible, i.e., start to start + 30.

            # So in the code, once we find a start and end where end - start >= 30, we can output start and start + 30. But how to handle that?

            # For example, if the interval is from 990 (16:30) to 1020 (17:00), then the meeting can be scheduled from 990 to 1020. So the output would be 16:30:17:00.

            # So the code can output start_time and min_to_time(start + 30).

            # However, in the code, the common_intervals are the overlapping intervals. For example, the common interval is (990, 1020). So the code would take start=990, and end=1020. The end - start is 30 minutes. So output 16:30:17:00.

            # So in code:

            start_time = min_to_time(start)
            end_time = min_to_time(start + 30)
            print(f"{start_time}:{end_time} Monday")
            return

    # If no interval found (though problem says there is one)
    print("No suitable time found.")

if __name__ == "__main__":
    main()