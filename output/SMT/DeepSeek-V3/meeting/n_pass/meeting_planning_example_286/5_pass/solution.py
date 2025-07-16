from z3 import *

def solve_scheduling():
    # Initialize solver with optimization
    opt = Optimize()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Availability windows (minutes since 9:00 AM)
    carol_min, carol_max = 75, 165    # 10:15 AM - 11:45 AM
    rebecca_min, rebecca_max = 150, 675  # 11:30 AM - 8:15 PM
    karen_min, karen_max = 225, 360    # 12:45 PM - 3:00 PM

    # Minimum meeting durations
    min_carol = 30
    min_rebecca = 120
    min_karen = 120

    # Meeting duration constraints
    opt.add(carol_end - carol_start >= min_carol)
    opt.add(rebecca_end - rebecca_start >= min_rebecca)
    opt.add(karen_end - karen_start >= min_karen)

    # Availability constraints
    opt.add(carol_start >= carol_min, carol_end <= carol_max)
    opt.add(rebecca_start >= rebecca_min, rebecca_end <= rebecca_max)
    opt.add(karen_start >= karen_min, karen_end <= karen_max)

    # Travel times between locations (minutes)
    travel = {
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Mission District'): 13
    }

    # We'll consider all possible meeting orders that make sense
    # Order 1: Carol → Rebecca → Karen
    order1 = And(
        carol_start >= travel[('Union Square', 'Sunset District')],
        rebecca_start >= carol_end + travel[('Sunset District', 'Mission District')],
        karen_start >= rebecca_end + travel[('Mission District', 'Bayview')]
    )

    # Order 2: Carol → Karen → Rebecca
    order2 = And(
        carol_start >= travel[('Union Square', 'Sunset District')],
        karen_start >= carol_end + travel[('Sunset District', 'Bayview')],
        rebecca_start >= karen_end + travel[('Bayview', 'Mission District')]
    )

    # Order 3: Rebecca → Carol → Karen
    order3 = And(
        rebecca_start >= travel[('Union Square', 'Mission District')],
        carol_start >= rebecca_end + travel[('Mission District', 'Sunset District')],
        karen_start >= carol_end + travel[('Sunset District', 'Bayview')]
    )

    # Add all possible orders to the solver
    opt.add(Or(order1, order2, order3))

    # Maximize total meeting time
    total_time = (carol_end - carol_start) + (rebecca_end - rebecca_start) + (karen_end - karen_start)
    opt.maximize(total_time)

    if opt.check() == sat:
        m = opt.model()
        
        def format_time(minutes):
            total = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total // 60
            mins = total % 60
            period = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{hours}:{mins:02d} {period}"

        # Get the actual meeting times
        c_start = m[carol_start].as_long()
        c_end = m[carol_end].as_long()
        r_start = m[rebecca_start].as_long()
        r_end = m[rebecca_end].as_long()
        k_start = m[karen_start].as_long()
        k_end = m[karen_end].as_long()

        print("SOLUTION:")
        print(f"1. Meet Carol at Sunset District from {format_time(c_start)} to {format_time(c_end)}")
        print(f"2. Meet Rebecca at Mission District from {format_time(r_start)} to {format_time(r_end)}")
        print(f"3. Meet Karen at Bayview from {format_time(k_start)} to {format_time(k_end)}")
        print(f"\nTotal meeting time: {m.eval(total_time).as_long()} minutes")
        
        # Determine which order was used
        if m.eval(order1):
            print("Meeting sequence: Carol → Rebecca → Karen")
        elif m.eval(order2):
            print("Meeting sequence: Carol → Karen → Rebecca")
        else:
            print("Meeting sequence: Rebecca → Carol → Karen")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()