participants = [
    {'name': 'Arthur', 'blocks': [(330, 360), (690, 720), (780, 780), (840, 870), (900, 930)]},  # Monday: 11:00-11:30, 13:30-14:00, 15:00-15:30; Tuesday: 13:00-13:30, 16:00-16:30; Wednesday: 10:00-10:30, 11:00-11:30, 12:00-12:30, 14:00-14:30, 16:00-16:30
    {'name': 'Michael', 'blocks': [(270, 300), (540, 600), (630, 660), (780, 780), (840, 870), (900, 930), (960, 990), (1020, 1050)]}  # Monday: 9:00-12:00, 12:30-13:00, 14:00-14:30, 15:00-17:00; Tuesday: 9:30-11:30, 12:00-13:30, 14:00-15:30; Wednesday: 10:00-12:30, 13:00-13:30
]

day_options = ['Monday', 'Tuesday', 'Wednesday']

for day in day_options:
    if day == 'Monday':
        start_times = [900, 1050, 1170, 1260, 1380, 1500, 1710]
    elif day == 'Tuesday':
        start_times = [540, 630, 690, 780, 870, 960, 1050]
    elif day == 'Wednesday':
        start_times = [900, 1050, 1170, 1260, 1380, 1500, 1710]
    
    for start in start_times:
        slot = (start, start + 30)
        conflict = False
        for participant in participants:
            for block in participant['blocks']:
                if not (block[1] < slot[0] or block[0] > slot[1]):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            print(f"{start//30:02d}:{start%30:02d}-{(start+30)//30:02d}:{(start+30)%30:02d} Monday")
            exit()