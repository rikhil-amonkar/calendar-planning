def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


participants = [
    {'busy': [(11*60, 11*60+30), (12*60+30, 13*60)]},
    {'busy': [(14*60, 14*60+30), (15*60, 15*60+30)]},
    {'busy': [(9*60, 10*60), (12*60, 12*60+30), (15*60, 15*60+30)]},
    {'busy': [(9*60, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (14*60+30, 16*60+30)]},
    {'busy': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 13*60),
              (13*60+30, 14*60), (14*60+30, 16*60+30)]},
    {'busy': [(11*60, 11*60+30), (12*60, 12*60+30), (13*60, 16*60)]}
]

overall_end = 15 * 60 + 30  # 930 minutes

for p in participants:
    adjusted_busy = []
    for start, end in p['busy']:
        adjusted_end = min(end, overall_end)
        if start < overall_end:  # Only include if starts before the overall end
            adjusted_busy.append((start, adjusted_end))
    p['busy'] = adjusted_busy

free_intervals = [(540, 930)]  # initial free interval

for p in participants:
    current_busy = p['busy']
    new_free = []
    for (s, e) in free_intervals:
        temp = [(s, e)]
        for (b_s, b_e) in current_busy:
            new_temp = []
            for (int_s, int_e) in temp:
                if int_e <= b_s or int_s >= b_e:
                    new_temp.append((int_s, int_e))
                else:
                    if int_s < b_s:
                        new_temp.append((int_s, b_s))
                    if int_e > b_e:
                        new_temp.append((b_e, int_e))
            temp = new_temp
        new_free.extend(temp)
    free_intervals = new_free

# Find the first suitable interval
for interval in free_intervals:
    start, end = interval
    if end - start >= 30:
        start_time = to_time_str(start)
        end_time = to_time_str(start + 30)
        print(f"{start_time}:{end_time} Monday")
        break
