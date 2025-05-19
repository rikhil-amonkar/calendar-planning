participants = [
    {'name': 'Emily', 'blocks': [(180, 210), (330, 390), (600, 630), (960, 990)]},  # 10:00-10:30, 11:30-12:30, 14:00-15:00, 16:00-16:30
    {'name': 'Melissa', 'blocks': [(270, 300), (690, 750)]},  # 9:30-10:00, 14:30-15:00
    {'name': 'Frank', 'blocks': [(180, 210), (300, 330), (390, 420), (690, 750), (900, 960), (960, 990)]}  # 10:00-10:30, 11:00-11:30, 12:30-13:00, 13:30-14:30, 15:00-16:00, 16:30-17:00
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