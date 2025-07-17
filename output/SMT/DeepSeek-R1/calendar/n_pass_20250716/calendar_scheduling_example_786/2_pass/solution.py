from z3 import *

def main():
    day = Int('day')
    start = Int('start')
    
    s_hard = Solver()
    s_pref = Solver()
    
    s_hard.add(Or(day == 0, day == 1, day == 2))
    s_hard.add(start >= 540)  # 9:00
    s_hard.add(start <= 990)  # 16:30 (so meeting ends by 17:00)
    
    # Amy's constraints
    amy_wed = And(Or(start + 30 <= 660, start >= 690),  # Avoid 11:00-11:30
                  Or(start + 30 <= 810, start >= 840))  # Avoid 13:30-14:00
    amy_constraint = If(day == 2, amy_wed, True)
    s_hard.add(amy_constraint)
    
    # Pamela's constraints
    pam_mon = Or(start + 30 <= 540, And(start >= 630, start + 30 <= 990))
    pam_tue = (start == 570)  # Only free at 9:30-10:00
    pam_wed = And(start >= 570,
                  Or(start + 30 <= 600, start >= 660),
                  Or(start + 30 <= 690, start >= 810),
                  Or(start + 30 <= 870, start >= 900),
                  Or(start + 30 <= 960, start >= 990))
    pam_constraint = If(day == 0, pam_mon, If(day == 1, pam_tue, If(day == 2, pam_wed, False)))
    s_hard.add(pam_constraint)
    
    for c in s_hard.assertions():
        s_pref.add(c)
    
    s_pref.add(day != 0)  # Avoid Monday
    s_pref.add(If(Or(day == 1, day == 2), start >= 960, True))  # After 16:00 on Tue/Wed
    
    if s_pref.check() == sat:
        model = s_pref.model()
    else:
        s_hard.check()
        model = s_hard.model()
    
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30
    
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[day_val]
    
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_time = format_time(start_val)
    end_time = format_time(end_val)
    
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()