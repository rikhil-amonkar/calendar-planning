from z3 import *

def main():
    s = Int('s')
    duration = 30

    # Hard constraints: work hours and existing schedules
    constraints = [
        s >= 0,
        s + duration <= 480,
        # Eric's blocked times: 12:00-13:00 (180-240 min) and 14:00-15:00 (300-360 min)
        Or(s + duration <= 180, s >= 240),
        Or(s + duration <= 300, s >= 360),
        # Henry's blocked times
        Or(s + duration <= 30, s >= 60),    # 9:30-10:00
        Or(s + duration <= 90, s >= 120),   # 10:30-11:00
        Or(s + duration <= 150, s >= 210),  # 11:30-12:30
        Or(s + duration <= 240, s >= 270),  # 13:00-13:30
        Or(s + duration <= 330, s >= 360),  # 14:30-15:00
        s + duration <= 420                 # 16:00-17:00
    ]
    
    # Henry's preference: meeting should end by 10:00 (60 minutes)
    preference = (s + duration <= 60)
    
    solver = Solver()
    solver.add(constraints)
    solver.add(preference)
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[s].as_long()
    else:
        solver2 = Solver()
        solver2.add(constraints)
        if solver2.check() == sat:
            model = solver2.model()
            start_minutes = model[s].as_long()
        else:
            print("No solution found")
            return

    # Convert minutes to time strings
    total_minutes_end = start_minutes + duration
    start_hour = 9 + start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = 9 + total_minutes_end // 60
    end_minute = total_minutes_end % 60

    start_time = f"{start_hour}:{start_minute:02d}"
    end_time = f"{end_hour}:{end_minute:02d}"
    
    print("Monday", start_time, end_time)

if __name__ == "__main__":
    main()