from z3 import *

def convert_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    total_hours = 9 + hours
    hours_part = total_hours % 12
    if hours_part == 0:
        hours_part = 12
    am_pm = "AM" if total_hours < 12 else "PM"
    if total_hours >= 12:
        am_pm = "PM"
    return f"{hours_part}:{mins:02d} {am_pm}"

def main():
    t0 = Int('t0')
    e_start = Int('e_start')
    e_end = Int('e_end')
    t1 = Int('t1')
    
    s = Solver()
    
    s.add(t0 >= 0)
    s.add(e_start >= t0 + 7)
    s.add(e_start >= 420)
    s.add(e_end >= e_start + 45)
    s.add(e_end <= 495)
    s.add(t1 >= e_end)
    s.add(t1 + 13 <= 600)
    
    if s.check() == sat:
        m = s.model()
        t0_val = m[t0].as_long()
        e_start_val = m[e_start].as_long()
        e_end_val = m[e_end].as_long()
        t1_val = m[t1].as_long()
        print("SOLUTION:")
        print(f"Leave North Beach at {t0_val} minutes after 9:00 AM, i.e., at {convert_time(t0_val)}.")
        print(f"Meet Emily from {e_start_val} minutes ({convert_time(e_start_val)}) to {e_end_val} minutes ({convert_time(e_end_val)}) after 9:00 AM.")
        print(f"Leave Union Square at {t1_val} minutes after 9:00 AM, i.e., at {convert_time(t1_val)}.")
        print(f"Arrive at Russian Hill at {t1_val+13} minutes after 9:00 AM, i.e., at {convert_time(t1_val+13)}.")
        print(f"Meet Margaret from 600 minutes (7:00 PM) to 720 minutes (9:00 PM).")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()