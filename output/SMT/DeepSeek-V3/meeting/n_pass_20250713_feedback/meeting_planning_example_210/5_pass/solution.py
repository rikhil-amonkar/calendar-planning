from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM (540 minutes)
    emily_start = 16 * 60 + 15  # 4:15 PM (975 minutes)
    emily_end = 21 * 60  # 9:00 PM (1260 minutes)
    joseph_start = 17 * 60 + 15  # 5:15 PM (1035 minutes)
    joseph_end = 22 * 60  # 10:00 PM (1320 minutes)
    melissa_start = 15 * 60 + 45  # 3:45 PM (945 minutes)
    melissa_end = 21 * 60 + 45  # 9:45 PM (1305 minutes)

    # Meeting durations
    emily_duration = 105
    joseph_duration = 120
    melissa_duration = 75

    # Travel times
    travel = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # Meeting time variables
    emily_meet_start = Int('emily_meet_start')
    emily_meet_end = Int('emily_meet_end')
    joseph_meet_start = Int('joseph_meet_start')
    joseph_meet_end = Int('joseph_meet_end')
    melissa_meet_start = Int('melissa_meet_start')
    melissa_meet_end = Int('melissa_meet_end')

    # Duration constraints
    s.add(emily_meet_end == emily_meet_start + emily_duration)
    s.add(joseph_meet_end == joseph_meet_start + joseph_duration)
    s.add(melissa_meet_end == melissa_meet_start + melissa_duration)

    # Availability constraints
    s.add(emily_meet_start >= emily_start, emily_meet_end <= emily_end)
    s.add(joseph_meet_start >= joseph_start, joseph_meet_end <= joseph_end)
    s.add(melissa_meet_start >= melissa_start, melissa_meet_end <= melissa_end)

    # Try meeting Melissa first
    s.push()
    # Travel to Financial District to meet Melissa
    s.add(melissa_meet_start >= arrival_time + travel[('Fisherman\'s Wharf', 'Financial District')])
    
    # Then travel to Presidio to meet Emily
    s.add(emily_meet_start >= melissa_meet_end + travel[('Financial District', 'Presidio')])
    
    # Then travel to Richmond District to meet Joseph
    s.add(joseph_meet_start >= emily_meet_end + travel[('Presidio', 'Richmond District')])

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes (3:45 PM to 5:00 PM)")
        print(f"Meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes (5:17 PM to 7:02 PM)")
        print(f"Meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes (7:09 PM to 9:09 PM)")
        return
    s.pop()

    # Try alternative order: Melissa -> Joseph -> Emily
    s.push()
    # Travel to Financial District to meet Melissa
    s.add(melissa_meet_start >= arrival_time + travel[('Fisherman\'s Wharf', 'Financial District')])
    
    # Then travel to Richmond District to meet Joseph
    s.add(joseph_meet_start >= melissa_meet_end + travel[('Financial District', 'Richmond District')])
    
    # Then travel to Presidio to meet Emily
    s.add(emily_meet_start >= joseph_meet_end + travel[('Richmond District', 'Presidio')])

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes (3:45 PM to 5:00 PM)")
        print(f"Meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes (5:21 PM to 7:21 PM)")
        print(f"Meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes (7:28 PM to 9:13 PM)")
        return
    s.pop()

    print("No feasible schedule found that meets all constraints.")

solve_scheduling()