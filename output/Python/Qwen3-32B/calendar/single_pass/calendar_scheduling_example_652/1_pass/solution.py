def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def generate_free_slots(busy_times, work_start, work_end):
    # Sort busy times by start time
    sorted_busy = sorted(busy_times, key=lambda x: x[0])
    free_slots = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    # Add the remaining free time after last busy
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    return free_slots

# Define participants' schedules
participants = {
    'Jesse': {
        'Monday': {
            'busy': [(810, 840), (870, 900)],
            'work_end': 1020
        },
        'Tuesday': {
            'busy': [(540, 570), (780, 810), (840, 900)],
            'work_end': 1020
        }
    },
    'Lawrence': {
        'Monday': {
            'busy': [(540, 1020)],
            'work_end': 1020
        },
        'Tuesday': {
            'busy': [(570, 630), (690, 750), (780, 810), (870, 900), (930, 990)],
            'work_end': 990  # 16:30
        }
    }
}

# Days to check
days = ['Monday', 'Tuesday']

meeting_duration = 30  # minutes

for day in days:
    # Get Jesse's and Lawrence's schedules for the day
    jesse_busy = participants['Jesse'][day]['busy']
    jesse_work_end = participants['Jesse'][day]['work_end']
    lawrence_busy = participants['Lawrence'][day]['busy']
    lawrence_work_end = participants['Lawrence'][day]['work_end']

    # Generate free slots
    jesse_free = generate_free_slots(jesse_busy, 540, jesse_work_end)
    lawrence_free = generate_free_slots(lawrence_busy, 540, lawrence_work_end)

    # Check for overlapping slots
    for j_slot in jesse_free:
        for l_slot in lawrence_free:
            start = max(j_slot[0], l_slot[0])
            end = min(j_slot[1], l_slot[1])
            if start < end:
                duration = end - start
                if duration >= meeting_duration:
                    # Output the earliest possible slot
                    start_time = minutes_to_time(start)
                    end_time = minutes_to_time(end)
                    print(f"{start_time}:{end_time} {day}")
                    exit()