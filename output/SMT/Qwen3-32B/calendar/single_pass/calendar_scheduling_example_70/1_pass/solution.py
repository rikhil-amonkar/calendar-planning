from z3 import *

def main():
    opt = Optimize()
    s = Int('s')
    
    # Work hours are 9:00 to 17:00. Meeting duration is 30 mins.
    # So start time must be between 9:00 (540) and 16:30 (990)
    opt.add(s >= 9*60)
    opt.add(s <= 17*60 - 30)  # 17*60 is 1020, minus 30 is 990
    
    # Denise's busy intervals (start and end in minutes since midnight)
    denise_buses = [ (12*60, 12*60 + 30), (15*60 + 30, 16*60) ]
    for b_start, b_end in denise_buses:
        opt.add( Or(s + 30 <= b_start, b_end <= s) )
    
    # Natalie's busy intervals
    natalie_buses = [
        (9*60, 11*60 + 30),  # 9:00-11:30
        (12*60, 13*60),      # 12:00-13:00
        (14*60, 14*60 + 30), # 14:00-14:30
        (15*60, 17*60)       # 15:00-17:00
    ]
    for b_start, b_end in natalie_buses:
        opt.add( Or(s + 30 <= b_start, b_end <= s) )
    
    # Angela has no constraints
    
    # Minimize the start time
    opt.minimize(s)
    
    if opt.check() == sat:
        model = opt.model()
        s_val = model[s].as_long()
        
        # Convert start time
        start_h = s_val // 60
        start_m = s_val % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        
        # Convert end time
        end_val = s_val + 30
        end_h = end_val // 60
        end_m = end_val % 60
        end_time = f"{end_h:02d}:{end_m:02d}"
        
        print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()