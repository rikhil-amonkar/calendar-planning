from z3 import *

def solve_order1():
    d1 = Int('d1_order1')
    d2 = Int('d2_order1')
    s = Solver()

    s.add(d1 > 0, d2 > 0)
    
    arrive_U = 17
    leave_U = arrive_U + d1
    arrive_P = leave_U + 24
    start_P = If(arrive_P >= 45, arrive_P, 45)
    leave_P = start_P + d2

    s.add(leave_U <= 240)
    s.add(leave_P <= 240)
    
    shortfall_r = If(d1 >= 120, 0, 120 - d1)
    shortfall_c = If(d2 >= 120, 0, 120 - d2)
    total_shortfall = shortfall_r + shortfall_c

    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(total_shortfall)
    
    if opt.check() == sat:
        m = opt.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        start_P_val = m.evaluate(start_P).as_long()
        leave_P_val = m.evaluate(leave_P).as_long()
        total_shortfall_val = m.evaluate(total_shortfall).as_long()
        schedule = {
            'Richard_start': arrive_U,
            'Richard_end': arrive_U + d1_val,
            'Richard_duration': d1_val,
            'Charles_start': start_P_val,
            'Charles_end': leave_P_val,
            'Charles_duration': d2_val,
            'total_shortfall': total_shortfall_val,
            'order': 1
        }
        return schedule
    else:
        return None

def solve_order2():
    d1 = Int('d1_order2')
    d2 = Int('d2_order2')
    s = Solver()

    s.add(d1 > 0, d2 > 0)
    
    arrive_P = 31
    start_P = If(arrive_P >= 45, arrive_P, 45)
    leave_P = start_P + d1
    arrive_U = leave_P + 22
    leave_U = arrive_U + d2

    s.add(leave_P <= 240)
    s.add(leave_U <= 240)
    
    shortfall_c = If(d1 >= 120, 0, 120 - d1)
    shortfall_r = If(d2 >= 120, 0, 120 - d2)
    total_shortfall = shortfall_c + shortfall_r

    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(total_shortfall)
    
    if opt.check() == sat:
        m = opt.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        start_P_val = m.evaluate(start_P).as_long()
        leave_P_val = m.evaluate(leave_P).as_long()
        total_shortfall_val = m.evaluate(total_shortfall).as_long()
        arrive_U_val = leave_P_val + 22
        schedule = {
            'Charles_start': start_P_val,
            'Charles_end': leave_P_val,
            'Charles_duration': d1_val,
            'Richard_start': arrive_U_val,
            'Richard_end': arrive_U_val + d2_val,
            'Richard_duration': d2_val,
            'total_shortfall': total_shortfall_val,
            'order': 2
        }
        return schedule
    else:
        return None

def main():
    schedule1 = solve_order1()
    schedule2 = solve_order2()
    
    if schedule1 is None and schedule2 is None:
        print("SOLUTION: No valid schedule found.")
        return
    
    if schedule1 is not None and schedule2 is not None:
        if schedule1['total_shortfall'] <= schedule2['total_shortfall']:
            best_schedule = schedule1
        else:
            best_schedule = schedule2
    elif schedule1 is not None:
        best_schedule = schedule1
    else:
        best_schedule = schedule2
        
    def format_time(minutes):
        total_minutes = minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        absolute_hours = 9 + hours
        am_pm = "AM" if absolute_hours < 12 else "PM"
        if absolute_hours > 12:
            absolute_hours -= 12
        return f"{absolute_hours}:{mins:02d}{am_pm}"

    if best_schedule['order'] == 1:
        print("SOLUTION: Visit Richard first, then Charles")
        print(f"Meet Richard at Union Square from {format_time(best_schedule['Richard_start'])} to {format_time(best_schedule['Richard_end'])} (duration: {best_schedule['Richard_duration']} minutes).")
        print(f"Then meet Charles at Presidio from {format_time(best_schedule['Charles_start'])} to {format_time(best_schedule['Charles_end'])} (duration: {best_schedule['Charles_duration']} minutes).")
        print(f"Total shortfall: {best_schedule['total_shortfall']} minutes.")
    else:
        print("SOLUTION: Visit Charles first, then Richard")
        print(f"Meet Charles at Presidio from {format_time(best_schedule['Charles_start'])} to {format_time(best_schedule['Charles_end'])} (duration: {best_schedule['Charles_duration']} minutes).")
        print(f"Then meet Richard at Union Square from {format_time(best_schedule['Richard_start'])} to {format_time(best_schedule['Richard_end'])} (duration: {best_schedule['Richard_duration']} minutes).")
        print(f"Total shortfall: {best_schedule['total_shortfall']} minutes.")

if __name__ == '__main__':
    main()