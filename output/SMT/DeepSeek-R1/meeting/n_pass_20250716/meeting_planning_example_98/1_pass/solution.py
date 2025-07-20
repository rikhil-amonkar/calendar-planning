from z3 import *

def main():
    # Convert times to minutes from midnight
    start_time = 9 * 60  # 9:00 AM
    timothy_start = 20 * 60 + 45  # 20:45 (8:45 PM)
    timothy_end = 21 * 60 + 30  # 21:30 (9:30 PM)
    travel_to_richmond = 12  # minutes
    
    # Declare variables
    t1 = Int('t1')  # departure time from Alamo Square
    t2 = Int('t2')  # departure time from Richmond District
    
    s = Optimize()
    
    # Constraints
    s.add(t1 >= start_time)
    s.add(t1 + travel_to_richmond <= timothy_start)
    s.add(t2 >= t1 + travel_to_richmond)
    s.add(t2 >= timothy_end)
    
    # Optimization objectives
    s.maximize(t1)
    s.minimize(t2)
    
    if s.check() == sat:
        m = s.model()
        t1_val = m.eval(t1).as_long()
        t2_val = m.eval(t2).as_long()
        
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        print(f"Leave Alamo Square at {format_time(t1_val)}")
        print(f"Arrive at Richmond District at {format_time(t1_val + travel_to_richmond)}")
        print(f"Leave Richmond District at {format_time(t2_val)}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()