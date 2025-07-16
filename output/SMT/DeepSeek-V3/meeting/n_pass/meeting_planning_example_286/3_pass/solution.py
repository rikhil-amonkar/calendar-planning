from z3 import *

def solve_scheduling():
    # Initialize solver with optimization capabilities
    opt = Optimize()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Carol: 10:15 AM (615) to 11:45 AM (705) → 75 to 165 minutes
    # Rebecca: 11:30 AM (690) to 8:15 PM (1215) → 150 to 675 minutes
    # Karen: 12:45 PM (765) to 3:00 PM (900) → 225 to 360 minutes

    # Meeting duration constraints
    opt.add(carol_end - carol_start >= 30)    # Minimum 30 minutes with Carol
    opt.add(rebecca_end - rebecca_start >= 120)  # Minimum 120 minutes with Rebecca
    opt.add(karen_end - karen_start >= 120)   # Minimum 120 minutes with Karen

    # Availability constraints
    opt.add(carol_start >= 75)    # 10:15 AM
    opt.add(carol_end <= 165)     # 11:45 AM
    opt.add(rebecca_start >= 150) # 11:30 AM
    opt.add(rebecca_end <= 675)   # 8:15 PM
    opt.add(karen_start >= 225)   # 12:45 PM
    opt.add(karen_end <= 360)     # 3:00 PM

    # Travel times between locations (in minutes)
    travel_times = {
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23
    }

    # We'll consider two possible meeting orders:
    # 1. Carol → Rebecca → Karen
    # 2. Carol → Karen → Rebecca

    # Create boolean variables to represent which order we choose
    order1 = Bool('order1')  # Carol → Rebecca → Karen
    order2 = Bool('order2')  # Carol → Karen → Rebecca

    # Exactly one order must be selected
    opt.add(Or(order1, order2))
    opt.add(Not(And(order1, order2)))

    # Constraints for order1 (Carol → Rebecca → Karen)
    opt.add(Implies(order1,
        And(
            carol_start >= travel_times[('Union Square', 'Sunset District')],
            rebecca_start >= carol_end + travel_times[('Sunset District', 'Mission District')],
            karen_start >= rebecca_end + travel_times[('Mission District', 'Bayview')]
        )
    ))

    # Constraints for order2 (Carol → Karen → Rebecca)
    opt.add(Implies(order2,
        And(
            carol_start >= travel_times[('Union Square', 'Sunset District')],
            karen_start >= carol_end + travel_times[('Sunset District', 'Bayview')],
            rebecca_start >= karen_end + travel_times[('Bayview', 'Mission District')]
        )
    ))

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

        print("SOLUTION:")
        print(f"Meet Carol at Sunset District from {format_time(m[carol_start].as_long())} to {format_time(m[carol_end].as_long())}")
        print(f"Meet Rebecca at Mission District from {format_time(m[rebecca_start].as_long())} to {format_time(m[rebecca_end].as_long())}")
        print(f"Meet Karen at Bayview from {format_time(m[karen_start].as_long())} to {format_time(m[karen_end].as_long())}")
        print(f"Total meeting time: {m.eval(total_time).as_long()} minutes")
        
        # Print which order was selected
        if is_true(m[order1]):
            print("Meeting order: Carol → Rebecca → Karen")
        else:
            print("Meeting order: Carol → Karen → Rebecca")
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()