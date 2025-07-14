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

    # Try different meeting orders
    orders = [
        ['melissa', 'emily', 'joseph'],
        ['melissa', 'joseph', 'emily'],
        ['emily', 'melissa', 'joseph'],
        ['emily', 'joseph', 'melissa'],
        ['joseph', 'melissa', 'emily'],
        ['joseph', 'emily', 'melissa']
    ]

    for order in orders:
        s.push()
        current_time = arrival_time
        prev_location = 'Fisherman\'s Wharf'
        
        for friend in order:
            if friend == 'melissa':
                dest = 'Financial District'
                start = melissa_meet_start
                end = melissa_meet_end
            elif friend == 'emily':
                dest = 'Presidio'
                start = emily_meet_start
                end = emily_meet_end
            else:  # joseph
                dest = 'Richmond District'
                start = joseph_meet_start
                end = joseph_meet_end
            
            # Add travel time
            travel_time = travel[(prev_location, dest)]
            s.add(start >= current_time + travel_time)
            
            # Update current time to end of meeting
            current_time = end
            prev_location = dest

        if s.check() == sat:
            m = s.model()
            print("SOLUTION:")
            for friend in order:
                if friend == 'melissa':
                    print(f"Meet Melissa at Financial District from {m[melissa_meet_start]} to {m[melissa_meet_end]} minutes.")
                elif friend == 'emily':
                    print(f"Meet Emily at Presidio from {m[emily_meet_start]} to {m[emily_meet_end]} minutes.")
                else:
                    print(f"Meet Joseph at Richmond District from {m[joseph_meet_start]} to {m[joseph_meet_end]} minutes.")
            return
        s.pop()

    print("No feasible schedule found.")

solve_scheduling()