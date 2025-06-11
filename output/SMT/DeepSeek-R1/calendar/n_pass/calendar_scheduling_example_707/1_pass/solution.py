from z3 import *

def main():
    # Define the variables
    day = Int('day')
    start = Int('start')
    
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    meeting_duration = 30
    max_start = work_end - meeting_duration  # 450 minutes (16:30)
    
    # Define busy intervals for each participant on each day (in minutes from 9:00)
    # Monday
    ryan_monday = [(30, 60), (120, 180), (240, 270), (390, 420)]
    adam_monday = [(0, 90), (120, 270), (300, 420), (450, 480)]
    # Tuesday
    ryan_tuesday = [(150, 210), (390, 420)]
    adam_tuesday = [(0, 60), (90, 390), (420, 480)]
    
    # Function to generate non-overlap constraints for a list of busy intervals
    def non_overlap_constraints(busy_intervals, s):
        constraints = []
        for (a, b) in busy_intervals:
            constraints.append(Or(s + meeting_duration <= a, s >= b))
        return And(constraints)
    
    # Constraints for Monday and Tuesday
    monday_constraint = And(
        non_overlap_constraints(ryan_monday, start),
        non_overlap_constraints(adam_monday, start)
    )
    
    tuesday_constraint = And(
        non_overlap_constraints(ryan_tuesday, start),
        non_overlap_constraints(adam_tuesday, start)
    )
    
    # Hard constraints: day is 0 (Monday) or 1 (Tuesday), start within [0, 450]
    hard_constraints = [
        Or(day == 0, day == 1),
        start >= work_start,
        start <= max_start,
        If(day == 0, monday_constraint, tuesday_constraint)
    ]
    
    # Preference constraint: if Monday, start >= 330 (14:30)
    preference_constraint = If(day == 0, start >= 330, True)
    
    # Try with preference first
    s_pref = Solver()
    s_pref.add(hard_constraints)
    s_pref.add(preference_constraint)
    
    if s_pref.check() == sat:
        model = s_pref.model()
        d = model[day].as_long()
        s_val = model[start].as_long()
        day_str = "Monday" if d == 0 else "Tuesday"
        # Convert start minutes to time string
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        end_minutes = s_val + meeting_duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        start_time = f"{start_hour}:{start_minute:02d}"
        end_time = f"{end_hour}:{end_minute:02d}"
        print(f"Day: {day_str}, Start: {start_time}, End: {end_time}")
    else:
        # Without preference constraint
        s = Solver()
        s.add(hard_constraints)
        if s.check() == sat:
            model = s.model()
            d = model[day].as_long()
            s_val = model[start].as_long()
            day_str = "Monday" if d == 0 else "Tuesday"
            start_hour = 9 + s_val // 60
            start_minute = s_val % 60
            end_minutes = s_val + meeting_duration
            end_hour = 9 + end_minutes // 60
            end_minute = end_minutes % 60
            start_time = f"{start_hour}:{start_minute:02d}"
            end_time = f"{end_hour}:{end_minute:02d}"
            print(f"Day: {day_str}, Start: {start_time}, End: {end_time}")
        else:
            print("No solution found")

if __name__ == "__main__":
    main()