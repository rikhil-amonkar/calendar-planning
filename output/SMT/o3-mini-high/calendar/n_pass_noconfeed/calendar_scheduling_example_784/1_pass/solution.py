from z3 import Solver, Int, Or, Implies

def main():
    s = Solver()
    
    duration = 60  # meeting duration in minutes

    # Define variables:
    # day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    # t: meeting start time in minutes after 9:00 (so t = 0 => 9:00, and t must be such that t+60 <= 480)
    day = Int('day')
    t = Int('t')
    
    # The day must be one of Monday, Tuesday or Wednesday.
    s.add(Or(day == 0, day == 1, day == 2))
    # Meeting must finish by 17:00 (9:00 + 480 minutes), so t+duration <= 480
    s.add(t >= 0, t <= 480 - duration)

    # Preferences from Judith:
    # She would like to avoid more meetings on Monday.
    s.add(day != 0)
    # And if on Wednesday, she prefers not to have meetings before 12:00 (i.e. before 180 minutes after 9:00)
    s.add(Implies(day == 2, t >= 180))
    
    # Judith's busy schedule:
    # Monday: busy 12:00-12:30  --> [180, 210]
    s.add(Implies(day == 0, Or(t + duration <= 180, t >= 210)))
    # Wednesday: busy 11:30-12:00  --> [150, 180]
    s.add(Implies(day == 2, Or(t + duration <= 150, t >= 180)))
    
    # Timothy's busy schedule:
    # Monday busy intervals:
    # 9:30-10:00 --> [30, 60]
    s.add(Implies(day == 0, Or(t + duration <= 30, t >= 60)))
    # 10:30-11:30 --> [90, 150]
    s.add(Implies(day == 0, Or(t + duration <= 90, t >= 150)))
    # 12:30-14:00 --> [210, 300]
    s.add(Implies(day == 0, Or(t + duration <= 210, t >= 300)))
    # 15:30-17:00 --> [390, 480]
    s.add(Implies(day == 0, Or(t + duration <= 390, t >= 480)))
    
    # Tuesday busy intervals:
    # 9:30-13:00 --> [30, 240]
    s.add(Implies(day == 1, Or(t + duration <= 30, t >= 240)))
    # 13:30-14:00 --> [270, 300]
    s.add(Implies(day == 1, Or(t + duration <= 270, t >= 300)))
    # 14:30-17:00 --> [330, 480]
    s.add(Implies(day == 1, Or(t + duration <= 330, t >= 480)))
    
    # Wednesday busy intervals:
    # 9:00-9:30 --> [0, 30]
    s.add(Implies(day == 2, Or(t + duration <= 0, t >= 30)))
    # 10:30-11:00 --> [90, 120]
    s.add(Implies(day == 2, Or(t + duration <= 90, t >= 120)))
    # 13:30-14:30 --> [270, 330]
    s.add(Implies(day == 2, Or(t + duration <= 270, t >= 330)))
    # 15:00-15:30 --> [360, 390]
    s.add(Implies(day == 2, Or(t + duration <= 360, t >= 390)))
    # 16:00-16:30 --> [420, 450]
    s.add(Implies(day == 2, Or(t + duration <= 420, t >= 450)))
    
    if s.check() == 'sat':
        m = s.model()
        meeting_day = m[day].as_long()
        meeting_start = m[t].as_long()
        
        # Map day integer to day name.
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_names[meeting_day]
        
        # Convert meeting start time from minutes after 9:00 to HH:MM.
        start_hour = 9 + meeting_start // 60
        start_min = meeting_start % 60
        end_time = meeting_start + duration
        end_hour = 9 + end_time // 60
        end_min = end_time % 60
        
        # Format the time range as HH:MM:HH:MM
        time_range = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
        
        print(day_str, time_range)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()