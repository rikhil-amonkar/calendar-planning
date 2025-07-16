def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(base, busy_list):
    free = [base]
    for busy_interval in busy_list:
        new_free = []
        for interval in free:
            if busy_interval[1] <= interval[0] or busy_interval[0] >= interval[1]:
                new_free.append(interval)
            else:
                if interval[0] < busy_interval[0]:
                    new_free.append([interval[0], busy_interval[0]])
                if interval[1] > busy_interval[1]:
                    new_free.append([busy_interval[1], interval[1]])
        free = new_free
    return free

def get_common_intervals(intervals1, intervals2):
    common = []
    for i1 in intervals1:
        for i2 in intervals2:
            start = max(i1[0], i2[0])
            end = min(i1[1], i2[1])
            if start < end:
                common.append([start, end])
    return common

def main():
    work_start = 540   # 9:00
    work_end = 1020    # 17:00
    duration = 30

    betty_base = {
        'Tuesday': [900, 1020],   # 15:00 to 17:00
        'Thursday': [900, 1020],
        'Wednesday': [work_start, work_end]
    }

    scott_base = {
        'Tuesday': [work_start, work_end],
        'Wednesday': [work_start, work_end],
        'Thursday': [work_start, work_end]
    }

    busy = {
        'Tuesday': {
            'Betty': [[540, 570], [690, 720], [750, 780], [810, 840], [990, 1020]],
            'Scott': [[540, 570], [600, 660], [690, 720], [750, 810], [840, 900], [960, 990]]
        },
        'Wednesday': {
            'Betty': [[570, 630], [780, 810], [840, 870]],
            'Scott': [[570, 750], [780, 810], [840, 870], [900, 930], [960, 990]]
        },
        'Thursday': {
            'Betty': [[570, 600], [690, 720], [840, 870], [900, 930], [990, 1020]],
            'Scott': [[540, 570], [600, 630], [660, 720], [750, 780], [900, 960], [990, 1020]]
        }
    }

    days = ['Tuesday', 'Thursday', 'Wednesday']
    
    for day in days:
        betty_busy = busy[day]['Betty']
        scott_busy = busy[day]['Scott']
        
        betty_free = get_free_intervals(betty_base[day], betty_busy)
        scott_free = get_free_intervals(scott_base[day], scott_busy)
        
        common_free = get_common_intervals(betty_free, scott_free)
        
        for interval in common_free:
            start_min, end_min = interval
            if end_min - start_min >= duration:
                meeting_start = start_min
                meeting_end = start_min + duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()