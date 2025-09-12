from z3 import *

def main():
    s = Solver()
    
    day = Int('day')
    start_time = Int('start_time')
    
    s.add(day >= 0, day <= 2)
    s.add(start_time >= 0, start_time <= 450)
    
    def non_overlap(s_time, dur, b_start, b_end):
        return Or(s_time >= b_end, s_time + dur <= b_start)
    
    amy_busy_wed = [(120, 150), (270, 300)]
    for busy in amy_busy_wed:
        s.add(If(day == 2, non_overlap(start_time, 30, busy[0], busy[1]), True))
    
    pam_busy = {
        0: [(0, 90), (120, 450)],
        1: [(0, 30), (60, 480)],
        2: [(0, 30), (60, 120), (150, 270), (330, 360), (420, 450)]
    }
    
    for d, intervals in pam_busy.items():
        for interval in intervals:
            s.add(If(day == d, non_overlap(start_time, 30, interval[0], interval[1]), True))
    
    s.add(day != 0)
    s.add(day != 1)
    s.add(If(day == 2, start_time >= 420, True))
    
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        st_val = m[start_time].as_long()
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        start_hour = 9 + st_val // 60
        start_minute = st_val % 60
        end_time = st_val + 30
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        print(f"{day_str} {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()