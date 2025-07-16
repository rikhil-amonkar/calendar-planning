from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Timothy at Alamo Square: 12:00PM to 4:15PM, min 105 minutes
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')

    # Mark at Presidio: 6:45PM to 9:00PM, min 60 minutes
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')

    # Joseph at Russian Hill: 4:45PM to 9:30PM, min 60 minutes
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Convert all times to minutes since 9:00AM (540 minutes since midnight)
    # Arrival time at Golden Gate Park: 9:00AM (540 minutes)
    arrival_time = 540

    # Friends' availability windows in minutes since midnight
    timothy_window_start = 720  # 12:00PM
    timothy_window_end = 975    # 4:15PM (16:15)
    mark_window_start = 1185    # 6:45PM (18:45)
    mark_window_end = 1260      # 9:00PM (21:00)
    joseph_window_start = 1005  # 4:45PM (16:45)
    joseph_window_end = 1290    # 9:30PM (21:30)

    # Meeting duration constraints
    min_timothy_duration = 105
    min_mark_duration = 60
    min_joseph_duration = 60

    # Travel times from Golden Gate Park to Alamo Square: 10 minutes
    travel_G_to_A = 10

    # Travel times between locations
    travel_A_to_P = 18  # Alamo Square to Presidio
    travel_A_to_R = 13  # Alamo Square to Russian Hill
    travel_P_to_R = 14  # Presidio to Russian Hill
    travel_R_to_P = 14  # Russian Hill to Presidio
    travel_R_to_A = 15  # Russian Hill to Alamo Square
    travel_P_to_A = 18  # Presidio to Alamo Square

    # Constraints for Timothy's meeting
    s.add(timothy_start >= timothy_window_start)
    s.add(timothy_end <= timothy_window_end)
    s.add(timothy_end - timothy_start >= min_timothy_duration)
    # Arrival at Alamo Square must be after leaving Golden Gate Park and traveling
    s.add(timothy_start >= arrival_time + travel_G_to_A)

    # Option 1: Timothy -> Joseph -> Mark
    s.push()
    # Joseph's meeting must start after Timothy's meeting ends + travel to Russian Hill
    s.add(joseph_start >= timothy_end + travel_A_to_R)
    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= min_joseph_duration)

    # Mark's meeting must start after Joseph's meeting ends + travel to Presidio
    s.add(mark_start >= joseph_end + travel_R_to_P)
    s.add(mark_start >= mark_window_start)
    s.add(mark_end <= mark_window_end)
    s.add(mark_end - mark_start >= min_mark_duration)

    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Joseph -> Mark):")
        print(f"Meet Timothy: {m[timothy_start].as_long()} to {m[timothy_end].as_long()}")
        print(f"Meet Joseph: {m[joseph_start].as_long()} to {m[joseph_end].as_long()}")
        print(f"Meet Mark: {m[mark_start].as_long()} to {m[mark_end].as_long()}")
        return

    s.pop()

    # Option 2: Timothy -> Mark -> Joseph
    s.push()
    # Mark's meeting must start after Timothy's meeting ends + travel to Presidio
    s.add(mark_start >= timothy_end + travel_A_to_P)
    s.add(mark_start >= mark_window_start)
    s.add(mark_end <= mark_window_end)
    s.add(mark_end - mark_start >= min_mark_duration)

    # Joseph's meeting must start after Mark's meeting ends + travel to Russian Hill
    s.add(joseph_start >= mark_end + travel_P_to_R)
    s.add(joseph_start >= joseph_window_start)
    s.add(joseph_end <= joseph_window_end)
    s.add(joseph_end - joseph_start >= min_joseph_duration)

    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Timothy -> Mark -> Joseph):")
        print(f"Meet Timothy: {m[timothy_start].as_long()} to {m[timothy_end].as_long()}")
        print(f"Meet Mark: {m[mark_start].as_long()} to {m[mark_end].as_long()}")
        print(f"Meet Joseph: {m[joseph_start].as_long()} to {m[joseph_end].as_long()}")
        return

    s.pop()

    print("No feasible schedule found to meet all friends.")

solve_scheduling()