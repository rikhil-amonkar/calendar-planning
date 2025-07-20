from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    period = "AM" if hours < 12 else "PM"
    h = hours % 12
    if h == 0:
        h = 12
    return f"{h}:{mins:02d} {period}"

def main():
    # Initialize solver with optimization
    opt = Optimize()
    
    # Departure time from Russian Hill (in minutes from midnight)
    depart_rh = Int('depart_rh')
    
    # Constraints
    # Must leave Russian Hill at or after 9:00 AM (540 minutes)
    opt.add(depart_rh >= 540)
    
    # Calculate meeting start and end times
    arrive_ph = depart_rh + 7  # Travel time to Pacific Heights
    meet_end = arrive_ph + 60   # Meeting duration of 60 minutes
    
    # Meeting must end by 10:00 PM (1320 minutes)
    opt.add(meet_end <= 1320)
    
    # Barbara is available from 7:15 AM (435 minutes), but constraint is redundant since depart_rh>=540
    # Optimize: minimize departure time to meet as early as possible
    opt.minimize(depart_rh)
    
    # Solve and output
    if opt.check() == sat:
        m = opt.model()
        depart_val = m[depart_rh].as_long()
        arrive_val = depart_val + 7
        end_val = arrive_val + 60
        
        print("Optimal Schedule:")
        print(f"Depart Russian Hill at {format_time(depart_val)}")
        print(f"Arrive at Pacific Heights at {format_time(arrive_val)}")
        print(f"Meet Barbara from {format_time(arrive_val)} to {format_time(end_val)}")
    else:
        print("No valid schedule found")

if __name__ == '__main__':
    main()