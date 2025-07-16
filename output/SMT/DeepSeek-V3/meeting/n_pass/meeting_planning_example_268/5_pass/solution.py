from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Convert all times to minutes since midnight
    arrival_time = 540  # 9:00AM (540 minutes)
    timothy_window_start = 720  # 12:00PM (720 minutes)
    timothy_window_end = 975    # 4:15PM (975 minutes)
    mark_window_start = 1185    # 6:45PM (1185 minutes)
    mark_window_end = 1260      # 9:00PM (1260 minutes)
    joseph_window_start = 1005  # 4:45PM (1005 minutes)
    joseph_window_end = 1290    # 9:30PM (1290 minutes)

    # Meeting durations
    min_timothy_duration = 105  # 1 hour 45 minutes
    min_mark_duration = 60      # 1 hour
    min_joseph_duration = 60    # 1 hour

    # Travel times (minutes)
    travel_G_to_A = 10  # Golden Gate Park to Alamo Square
    travel_A_to_P = 18  # Alamo Square to Presidio
    travel_A_to_R = 13  # Alamo Square to Russian Hill
    travel_P_to_R = 14  # Presidio to Russian Hill
    travel_R_to_P = 14  # Russian Hill to Presidio
    travel_R_to_A = 15  # Russian Hill to Alamo Square
    travel_P_to_A = 18  # Presidio to Alamo Square

    # Base constraints for each meeting
    # Timothy must meet during his window
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end - timothy_start >= min_timothy_duration)
    # Can't meet Timothy before arriving + travel time
    s.add(timothy_start >= arrival_time + travel_G_to_A)

    # Mark must meet during his window
    s.add(mark_start >= mark_window_start)
    s.add(mark_end <= mark_window_end)
    s.add(mark_end - mark_start >= min_mark_duration)

    # Joseph must meet during his window
    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= min_joseph_duration)

    # Try different meeting orders
    # Option 1: Timothy -> Joseph -> Mark
    s.push()
    s.add(joseph_start >= timothy_end + travel_A_to_R)
    s.add(mark_start >= joseph_end + travel_R_to_P)
    
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Joseph -> Mark):")
        print(f"Meet Timothy: {minutes_to_time(m[timothy_start].as_long())} to {minutes_to_time(m[timothy_end].as_long())}")
        print(f"Meet Joseph: {minutes_to_time(m[joseph_start].as_long())} to {minutes_to_time(m[joseph_end].as_long())}")
        print(f"Meet Mark: {minutes_to_time(m[mark_start].as_long())} to {minutes_to_time(m[mark_end].as_long())}")
        return
    
    s.pop()

    # Option 2: Timothy -> Mark -> Joseph
    s.push()
    s.add(mark_start >= timothy_end + travel_A_to_P)
    s.add(joseph_start >= mark_end + travel_P_to_R)
    
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Mark -> Joseph):")
        print(f"Meet Timothy: {minutes_to_time(m[timothy_start].as_long())} to {minutes_to_time(m[timothy_end].as_long())}")
        print(f"Meet Mark: {minutes_to_time(m[mark_start].as_long())} to {minutes_to_time(m[mark_end].as_long())}")
        print(f"Meet Joseph: {minutes_to_time(m[joseph_start].as_long())} to {minutes_to_time(m[joseph_end].as_long())}")
        return
    
    s.pop()

    print("No feasible schedule found to meet all friends.")

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    period = "AM" if hours < 12 else "PM"
    if hours > 12:
        hours -= 12
    elif hours == 0:
        hours = 12
    return f"{hours}:{mins:02d} {period}"

solve_scheduling()