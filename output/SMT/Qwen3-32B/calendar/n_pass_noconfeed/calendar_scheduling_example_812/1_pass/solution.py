from z3 import *

def find_meeting_time():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    busy_mary = {
        'Monday': [],
        'Tuesday': [(60, 90), (390, 420)],
        'Wednesday': [(30, 60), (360, 390)],
        'Thursday': [(0, 60), (90, 150)],
    }
    busy_alexis = {
        'Monday': [(0, 60), (90, 180), (210, 450)],
        'Tuesday': [(0, 60), (90, 150), (180, 390), (420, 480)],
        'Wednesday': [(0, 120), (150, 480)],
        'Thursday': [(60, 180), (300, 330), (390, 420), (450, 480)],
    }
    
    for day in days:
        s = Int('s')
        opt = Optimize()
        opt.add(0 <= s, s <= 450)
        # Mary's constraints
        for b_start, b_end in busy_mary[day]:
            opt.add(Or(s + 30 <= b_start, s >= b_end))
        # Alexis's constraints
        for b_start, b_end in busy_alexis[day]:
            opt.add(Or(s + 30 <= b_start, s >= b_end))
        opt.minimize(s)
        if opt.check() == sat:
            model = opt.model()
            start_time = model[s].as_long()
            hours = 9 + start_time // 60
            mins = start_time % 60
            start_str = f"{hours:02d}:{mins:02d}"
            end_time = start_time + 30
            hours_end = 9 + end_time // 60
            mins_end = end_time % 60
            end_str = f"{hours_end:02d}:{mins_end:02d}"
            print(f"{day} {start_str}:{end_str}")
            return
    print("No solution found")

find_meeting_time()