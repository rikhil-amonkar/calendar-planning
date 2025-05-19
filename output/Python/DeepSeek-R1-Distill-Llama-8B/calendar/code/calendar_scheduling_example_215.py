participants = [
    {'name': 'Steven', 'blocks': []},  # Free the entire day
    {'name': 'Roy', 'blocks': []},    # Calendar is wide open
    {'name': 'Cynthia', 'blocks': [(330, 360), (690, 720), (780, 780), (840, 870)]},  # 9:30-10:30, 11:30-12:00, 13:00-13:30, 15:00-16:00
    {'name': 'Lauren', 'blocks': [(180, 210), (330, 360), (390, 420), (780, 780), (840, 870), (900, 930), (960, 990)]},  # 9:00-9:30, 10:30-11:00, 11:30-12:00, 13:00-13:30, 14:00-14:30, 15:00-15:30, 16:00-17:00
    {'name': 'Robert', 'blocks': [(300, 330), (690, 720), (780, 780), (840, 870), (900, 930)]}  # 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00
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
        print(f"{start//30:02d}:{start%30:02d}-{(start+30)//30:02d}:{(start+30)%30:02d} Monday")
        exit()