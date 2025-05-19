participants = [
    {'name': 'Nicole', 'blocks': [(630, 660), (900, 930), (780, 810), (990, 1020)]},  # Tuesday 16:00-16:30, Wednesday 15:00-15:30, Friday 12:00-12:30, 15:30-16:00
    {'name': 'Daniel', 'blocks': [(270, 300), (540, 570), (630, 660), (690, 720), (780, 840), (870, 900), (930, 960), (990, 1020)]}  # Monday: 9:00-12:30, 13:00-13:30, 14:00-16:30; Tuesday: 9:00-10:30, 11:30-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00; Wednesday: 9:00-10:00, 11:00-12:30, 13:00-13:30, 14:00-14:30, 16:30-17:00; Thursday: 11:00-12:00, 13:00-14:00, 15:00-15:30; Friday: 10:00-11:00, 11:30-12:00, 12:30-14:30, 15:00-15:30, 16:00-16:30
]

day_options = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

for day in day_options:
    if day == 'Monday':
        start_times = [900, 1050, 1170, 1260, 1380, 1500, 1710]
    elif day == 'Tuesday':
        start_times = [540, 630, 690, 780, 870, 960, 1050]
    elif day == 'Wednesday':
        start_times = [900, 1050, 1170, 1260, 1380, 1500, 1710]
    elif day == 'Thursday':
        start_times = [630, 690, 750, 840, 930, 1020, 1110]
    elif day == 'Friday':
        start_times = [600, 630, 690, 750, 870, 930, 1020]
    
    for start in start_times:
        slot = (start, start + 60)
        conflict = False
        for participant in participants:
            for block in participant['blocks']:
                if not (block[1] < slot[0] or block[0] > slot[1]):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            print(f"{start//30:02d}:{start%30:02d}-{(start+60)//30:02d}:{(start+60)%30:02d} Monday")
            exit()