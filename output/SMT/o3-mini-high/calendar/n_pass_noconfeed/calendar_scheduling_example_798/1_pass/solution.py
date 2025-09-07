from z3 import *

def format_time(minutes):
    # Convert minutes (offset from 9:00) to HH:MM format.
    hour = 9 + minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    duration = 30  # Meeting duration in minutes

    # Define variables:
    # day: 0 = Monday, 1 = Tuesday, 2 = Wednesday
    # start: meeting start time in minutes after 9:00 (so 0 means 09:00, 450 means 16:30)
    day = Int('day')
    start = Int('start')

    # Use Optimize to minimize the day and time (earliest availability)
    opt = Optimize()
    
    # Domain constraints: valid day and meeting must finish by 17:00.
    opt.add(Or(day == 0, day == 1, day == 2))
    opt.add(start >= 0, start <= 480 - duration)

    # Helper: For a given busy interval, the meeting should not overlap it:
    # Either the meeting ends at or before the busy interval starts,
    # or the meeting starts at or after the busy interval ends.
    def no_overlap(busy_start, busy_end):
        return Or(start + duration <= busy_start, start >= busy_end)

    # Helper to add busy constraints for a particular day value.
    def add_busy_constraints(day_val, busy_list):
        for (b_start, b_end) in busy_list:
            opt.add(Implies(day == day_val, no_overlap(b_start, b_end)))
    
    # Existing schedules for Nancy:
    # Monday (day==0)
    nancy_monday = [(60, 90), (150, 210), (270, 300), (330, 390), (420, 480)]
    add_busy_constraints(0, nancy_monday)
    # Tuesday (day==1)
    nancy_tuesday = [(30, 90), (120, 150), (180, 210), (240, 270), (390, 420)]
    add_busy_constraints(1, nancy_tuesday)
    # Wednesday (day==2)
    nancy_wednesday = [(60, 150), (270, 420)]
    add_busy_constraints(2, nancy_wednesday)
    
    # Existing schedules for Jose:
    # Monday (day==0): busy the entire day.
    jose_monday = [(0, 480)]
    add_busy_constraints(0, jose_monday)
    # Tuesday (day==1): busy the entire day.
    jose_tuesday = [(0, 480)]
    add_busy_constraints(1, jose_tuesday)
    # Wednesday (day==2)
    jose_wednesday = [(0, 30), (60, 210), (270, 330), (360, 480)]
    add_busy_constraints(2, jose_wednesday)
    
    # Objective: schedule the meeting at the earliest availability.
    # We minimize a weighted sum where the day is primary and the start time secondary.
    opt.minimize(day * 10000 + start)
    
    if opt.check() == sat:
        model = opt.model()
        chosen_day = model[day].as_long()
        chosen_start = model[start].as_long()
        chosen_end = chosen_start + duration
        
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
        day_str = day_names[chosen_day]
        start_str = format_time(chosen_start)
        end_str = format_time(chosen_end)
        
        # Output in the format: Day {HH:MM:HH:MM}
        print(f"{day_str} {{{start_str}:{end_str}}}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()