participants = [
    {'name': 'Shirley', 'blocks': [(330, 360), (420, 450), (960, 990)]},  # Monday: 10:30-11:00, 12:00-12:30, 16:00-16:30; Tuesday: 9:30-10:00
    {'name': 'Albert', 'blocks': [(270, 300), (540, 570), (630, 660), (780, 780), (840, 870), (900, 930), (960, 990), (990, 1020)]}  # Monday: 9:00-17:00; Tuesday: 9:30-11:00, 11:30-12:30, 13:00-16:00, 16:30-17:00
]

day_options = ['Monday', 'Tuesday']

for day in day_options:
    if day == 'Monday':
        start_times = [900, 1050, 1170, 1260, 1380, 1500, 1710]
    elif day == 'Tuesday':
        start_times = [540, 630, 690, 780, 870, 960, 1050]
    
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
            print(f"{start//30:02d}:{start%30:02d}-{(start+30)//30:02d}:{(start+30)%30:02d} Tuesday")
            exit()