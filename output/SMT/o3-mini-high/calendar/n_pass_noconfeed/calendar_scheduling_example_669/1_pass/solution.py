from z3 import *

def format_time(total_minutes):
    # Convert meeting time (minutes after 9:00) to an HH:MM string.
    # For example, 150 -> 9:00 + 150 minutes = 11:30.
    absolute = 9 * 60 + total_minutes
    hh = absolute // 60
    mm = absolute % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    s = Solver()
    
    # day: 0 means Monday, 1 means Tuesday.
    day = Int('day')
    # start: meeting start time in minutes after 9:00.
    start = Int('start')
    duration = 30
    
    work_start = 0     # 9:00 is 0 minutes after 9:00
    work_end = 480     # 17:00 is 480 minutes after 9:00

    # The meeting must start within work hours.
    s.add(start >= work_start, start + duration <= work_end)
    # The meeting day is either Monday (0) or Tuesday (1).
    s.add(Or(day == 0, day == 1))

    # ----- Participant Jean's constraints -----
    # Jean's schedule:
    #   Tuesday busy: 11:30-12:00 (150-180) and 16:00-16:30 (420-450)
    s.add(Implies(day == 1, Or(start + duration <= 150, start >= 180)))
    s.add(Implies(day == 1, Or(start + duration <= 420, start >= 450)))
    # (Jean is free on Monday, so no constraint is needed for day==0.)
    
    # ----- Participant Doris's constraints -----
    # Doris's schedule on Monday:
    #   Busy: 9:00-11:30 (0-150)
    #         12:00-12:30 (180-210)
    #         13:30-16:00 (270-420)
    #         16:30-17:00 (450-480) is taken care of by the work hours constraint.
    #
    # Also, Doris prefers not to meet on Monday after 14:00 
    # i.e. the meeting should finish by 14:00 (300 minutes after 9:00).
    #
    # On Tuesday, Doris is busy the entire day (9:00-17:00).
    #
    # Monday constraints:
    s.add(Implies(day == 0, start >= 150))  # Meeting must start after 11:30.
    s.add(Implies(day == 0, Or(start + duration <= 180, start >= 210)))  # Avoid 12:00-12:30.
    s.add(Implies(day == 0, Or(start + duration <= 270, start >= 420)))  # Avoid 13:30-16:00.
    # Preference: finish the meeting by 14:00.
    s.add(Implies(day == 0, start + duration <= 300))
    
    # Tuesday constraint:
    s.add(Implies(day == 1, False))  # Doris is busy all day Tuesday.
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        chosen_day = m[day].as_long()
        chosen_start = m[start].as_long()
        chosen_end = chosen_start + duration
        
        day_str = "Monday" if chosen_day == 0 else "Tuesday"
        time_range = f"{format_time(chosen_start)}:{format_time(chosen_end)}"
        print(f"{day_str} {time_range}")
    else:
        print("No valid meeting time found.")

if __name__ == "__main__":
    main()