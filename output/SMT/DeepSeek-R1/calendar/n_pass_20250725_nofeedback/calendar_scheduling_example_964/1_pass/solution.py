from z3 import *

def main():
    # We are only scheduling for Tuesday
    t = Int('t')   # minutes from 9:00

    s = Solver()

    # Meeting must be within [0, 420] minutes (so that it ends by 480, which is 17:00)
    s.add(t >= 0)
    s.add(t <= 420)

    # Betty's Tuesday intervals in minutes from 9:00 (start inclusive, end exclusive)
    betty_tue = [(30, 60), (90, 120), (180, 210), (270, 360), (450, 480)]
    for (start, end) in betty_tue:
        s.add(Or(t + 60 <= start, t >= end))

    # Megan's Tuesday intervals in minutes from 9:00
    megan_tue = [(0, 30), (60, 90), (180, 300), (360, 390), (420, 450)]
    for (start, end) in megan_tue:
        s.add(Or(t + 60 <= start, t >= end))

    if s.check() == sat:
        m = s.model()
        start_minutes = m[t].as_long()
        # Convert to time: 9:00 + start_minutes minutes
        hours = start_minutes // 60
        minutes = start_minutes % 60
        total_minutes = 9 * 60 + start_minutes
        start_hour = total_minutes // 60
        start_minute = total_minutes % 60
        end_minutes = start_minutes + 60
        total_end_minutes = 9 * 60 + end_minutes
        end_hour = total_end_minutes // 60
        end_minute = total_end_minutes % 60
        
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print("Day: Tuesday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()