from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM
    karen_start = 18 * 60 + 45  # 6:45 PM
    karen_end = 20 * 60 + 15    # 8:15 PM
    mark_start = 13 * 60 + 0    # 1:00 PM
    mark_end = 17 * 60 + 45     # 5:45 PM

    # Travel times in minutes
    travel = {
        ('NB', 'PH'): 8,
        ('NB', 'EM'): 6,
        ('PH', 'NB'): 9,
        ('PH', 'EM'): 10,
        ('EM', 'NB'): 5,
        ('EM', 'PH'): 11
    }

    # Meeting variables (minutes since midnight)
    meet_mark_start = Int('meet_mark_start')
    meet_mark_end = Int('meet_mark_end')
    meet_karen_start = Int('meet_karen_start')
    meet_karen_end = Int('meet_karen_end')

    # Meeting duration constraints
    s.add(meet_mark_end - meet_mark_start >= 120)
    s.add(meet_karen_end - meet_karen_start >= 90)

    # Availability constraints
    s.add(meet_mark_start >= mark_start)
    s.add(meet_mark_end <= mark_end)
    s.add(meet_karen_start >= karen_start)
    s.add(meet_karen_end <= karen_end)

    # Possible meeting orders
    order1 = And(
        meet_mark_start >= arrival_time + travel[('NB', 'EM')],
        meet_karen_start >= meet_mark_end + travel[('EM', 'PH')]
    )

    order2 = And(
        meet_karen_start >= arrival_time + travel[('NB', 'PH')],
        meet_mark_start >= meet_karen_end + travel[('PH', 'EM')]
    )

    s.add(Or(order1, order2))

    # Check for solution
    if s.check() == sat:
        m = s.model()
        mark_s = m[meet_mark_start].as_long()
        mark_e = m[meet_mark_end].as_long()
        karen_s = m[meet_karen_start].as_long()
        karen_e = m[meet_karen_end].as_long()

        # Determine meeting order
        if mark_s < karen_s:
            order = "Mark first, then Karen"
        else:
            order = "Karen first, then Mark"

        # Format time output
        def fmt_time(mins):
            return f"{mins//60}:{mins%60:02d}"

        print("SOLUTION:")
        print(f"Meeting order: {order}")
        print(f"Meet Mark: {fmt_time(mark_s)} to {fmt_time(mark_e)}")
        print(f"Meet Karen: {fmt_time(karen_s)} to {fmt_time(karen_e)}")
    else:
        print("No feasible schedule found")

solve_scheduling()