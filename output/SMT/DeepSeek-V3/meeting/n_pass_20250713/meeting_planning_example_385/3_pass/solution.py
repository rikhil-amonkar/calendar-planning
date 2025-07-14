from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    current_time = 540  # minutes since midnight

    # Jeffrey: Presidio, 8:00 AM - 10:00 AM (480 - 600 minutes since midnight)
    # Since we arrive at Nob Hill at 9:00 AM (540), we can't meet Jeffrey before 9:00 AM.
    # So Jeffrey's window is 540 - 600 minutes (9:00 AM - 10:00 AM)
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    jeffrey_duration = 105  # minutes

    # Steven: North Beach, 1:30 PM - 10:00 PM (810 - 1320 minutes since midnight)
    steven_start = Int('steven_start')
    steven_end = Int('steven_end')
    steven_duration = 45  # minutes

    # Barbara: Fisherman's Wharf, 6:00 PM - 9:30 PM (1080 - 1290 minutes since midnight)
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    barbara_duration = 30  # minutes

    # John: Pacific Heights, 9:00 AM - 1:30 PM (540 - 810 minutes since midnight)
    john_start = Int('john_start')
    john_end = Int('john_end')
    john_duration = 15  # minutes

    # Variables to track whether each friend is met
    meet_jeffrey = Bool('meet_jeffrey')
    meet_steven = Bool('meet_steven')
    meet_barbara = Bool('meet_barbara')
    meet_john = Bool('meet_john')

    # Constraints for Jeffrey
    s.add(Implies(meet_jeffrey, jeffrey_start >= 540))
    s.add(Implies(meet_jeffrey, jeffrey_end <= 600))
    s.add(Implies(meet_jeffrey, jeffrey_end == jeffrey_start + jeffrey_duration))
    # Travel from Nob Hill to Presidio takes 17 minutes
    s.add(Implies(meet_jeffrey, jeffrey_start >= current_time + 17))

    # Constraints for John
    s.add(Implies(meet_john, john_start >= 540))
    s.add(Implies(meet_john, john_end <= 810))
    s.add(Implies(meet_john, john_end == john_start + john_duration))
    # Travel from Nob Hill to Pacific Heights takes 8 minutes
    s.add(Implies(meet_john, john_start >= current_time + 8))

    # Constraints for Steven
    s.add(Implies(meet_steven, steven_start >= 810))
    s.add(Implies(meet_steven, steven_end <= 1320))
    s.add(Implies(meet_steven, steven_end == steven_start + steven_duration))

    # Constraints for Barbara
    s.add(Implies(meet_barbara, barbara_start >= 1080))
    s.add(Implies(meet_barbara, barbara_end <= 1290))
    s.add(Implies(meet_barbara, barbara_end == barbara_start + barbara_duration))

    # Exactly three friends must be met
    s.add(Sum([If(meet_jeffrey, 1, 0), If(meet_steven, 1, 0), If(meet_barbara, 1, 0), If(meet_john, 1, 0)]) == 3)

    # Define possible sequences of meetings
    # Option 1: Meet John, then Steven, then Barbara
    # Option 2: Meet Jeffrey, then Steven, then Barbara
    # Let's try Option 1 first

    # Option 1: Meet John first
    s.add(meet_john == True)
    s.add(john_start == current_time + 8)  # Travel to Pacific Heights
    john_current_time = john_end

    # After John, meet Steven
    s.add(meet_steven == True)
    # Travel from Pacific Heights to North Beach: 9 minutes
    s.add(steven_start >= john_current_time + 9)
    s.add(steven_start >= 810)  # Steven's window starts at 1:30 PM
    steven_current_time = steven_end

    # After Steven, meet Barbara
    s.add(meet_barbara == True)
    # Travel from North Beach to Fisherman's Wharf: 5 minutes
    s.add(barbara_start >= steven_current_time + 5)
    s.add(barbara_start >= 1080)  # Barbara's window starts at 6:00 PM

    # Ensure Jeffrey is not met
    s.add(meet_jeffrey == False)

    # Check if all constraints are satisfied
    if s.check() == sat:
        m = s.model()
        print("Schedule:")
        if m[meet_john]:
            print(f"Meet John at Pacific Heights from {m[john_start].as_long() // 60}:{m[john_start].as_long() % 60:02d} to {m[john_end].as_long() // 60}:{m[john_end].as_long() % 60:02d}")
        if m[meet_steven]:
            print(f"Meet Steven at North Beach from {m[steven_start].as_long() // 60}:{m[steven_start].as_long() % 60:02d} to {m[steven_end].as_long() // 60}:{m[steven_end].as_long() % 60:02d}")
        if m[meet_barbara]:
            print(f"Meet Barbara at Fisherman's Wharf from {m[barbara_start].as_long() // 60}:{m[barbara_start].as_long() % 60:02d} to {m[barbara_end].as_long() // 60}:{m[barbara_end].as_long() % 60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()