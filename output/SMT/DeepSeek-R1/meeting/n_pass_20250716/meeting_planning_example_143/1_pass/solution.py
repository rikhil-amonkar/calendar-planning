from z3 import *

def main():
    # Convert times to minutes from midnight
    start_day = 9 * 60  # 9:00 AM
    mark_start_avail = 13 * 60      # 1:00 PM (780 minutes)
    mark_end_avail = 17 * 60 + 45   # 5:45 PM (1065 minutes)
    karen_start = 18 * 60 + 45      # 6:45 PM (1125 minutes)
    karen_end = 20 * 60 + 15        # 8:15 PM (1215 minutes)

    # Travel times
    NB_to_Emb = 6    # North Beach to Embarcadero
    Emb_to_PH = 11   # Embarcadero to Pacific Heights

    # Create optimizer
    opt = Optimize()

    # Define variables
    start_Mark = Int('start_Mark')
    t_leave_NB = Int('t_leave_NB')

    # Constraints for Mark's meeting
    opt.add(start_Mark >= mark_start_avail)
    opt.add(start_Mark + 120 <= mark_end_avail)
    
    # Travel from North Beach to Embarcadero
    opt.add(t_leave_NB >= start_day)
    opt.add(t_leave_NB + NB_to_Emb <= start_Mark)
    
    # Travel to Pacific Heights for Karen
    opt.add(start_Mark + 120 + Emb_to_PH <= karen_start)
    
    # Maximize start_Mark to minimize waiting time before Karen
    opt.maximize(start_Mark)

    if opt.check() == sat:
        m = opt.model()
        start_mark_val = m.evaluate(start_Mark).as_long()
        t_leave_NB_val = m.evaluate(t_leave_NB).as_long()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            display_hour = hours % 12
            if display_hour == 0:
                display_hour = 12
            return f"{display_hour}:{mins:02d}{am_pm}"
        
        print("SOLUTION:")
        print(f"Leave North Beach at {format_time(t_leave_NB_val)}")
        print(f"Arrive at Embarcadero at {format_time(t_leave_NB_val + NB_to_Emb)}")
        print(f"Meet Mark from {format_time(start_mark_val)} to {format_time(start_mark_val + 120)}")
        print(f"Leave Embarcadero at {format_time(start_mark_val + 120)}")
        print(f"Arrive at Pacific Heights at {format_time(start_mark_val + 120 + Emb_to_PH)}")
        print(f"Meet Karen from {format_time(karen_start)} to {format_time(karen_end)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()