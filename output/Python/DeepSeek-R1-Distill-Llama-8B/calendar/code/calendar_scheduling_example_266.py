participants = [
    {'name': 'Joe', 'blocks': [(90, 120), (210, 240)]},  # 9:30-10:00 and 10:30-11:00
    {'name': 'Keith', 'blocks': [(330, 360), (900, 930)]},  # 11:30-12:00 and 15:00-15:30
    {'name': 'Patricia', 'blocks': [(0, 30), (780, 810)]},  # 9:00-9:30 and 13:00-13:30
    {'name': 'Nancy', 'blocks': [(0, 90), (330, 990)]},  # 9:00-11:00 and 11:30-16:30
    {'name': 'Pamela', 'blocks': [(0, 60), (150, 180), (270, 300), (780, 840), (870, 900), (930, 960), (990, 1020)]}  # Her blocks
]

day = "Monday"

for start in range(0, 990, 30):
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
        print(f"{start//30:02d}:{start%30:02d}-{(start+30)//30:02d}:{(start+30)%30:02d} {day}")
        exit()