from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since 9:00 AM)
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Travel times between locations (in minutes)
    travel = {
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Financial District', 'Presidio'): 23,
        ('Financial District', 'Richmond District'): 22,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Richmond District'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Presidio'): 7
    }

    # Convert availability times to minutes since 9:00 AM
    emily_avail_start = (16*60 + 15) - 9*60  # 4:15 PM
    emily_avail_end = (21*60) - 9*60         # 9:00 PM
    joseph_avail_start = (17*60 + 15) - 9*60 # 5:15 PM
    joseph_avail_end = (22*60) - 9*60        # 10:00 PM
    melissa_avail_start = (15*60 + 45) - 9*60 # 3:45 PM
    melissa_avail_end = (21*60 + 45) - 9*60   # 9:45 PM

    # Meeting duration constraints
    s.add(melissa_end - melissa_start >= 75)
    s.add(emily_end - emily_start >= 105)
    s.add(joseph_end - joseph_start >= 120)

    # Availability constraints
    s.add(melissa_start >= melissa_avail_start)
    s.add(melissa_end <= melissa_avail_end)
    s.add(emily_start >= emily_avail_start)
    s.add(emily_end <= emily_avail_end)
    s.add(joseph_start >= joseph_avail_start)
    s.add(joseph_end <= joseph_avail_end)

    # Define possible meeting orders
    orders = [
        ['melissa', 'emily', 'joseph'],
        ['melissa', 'joseph', 'emily'],
        ['emily', 'melissa', 'joseph'],
        ['emily', 'joseph', 'melissa'],
        ['joseph', 'melissa', 'emily'],
        ['joseph', 'emily', 'melissa']
    ]

    # Helper function to get travel time
    def get_travel(from_loc, to_loc):
        return travel[(from_loc, to_loc)]

    # Try each possible order
    for order in orders:
        temp_s = Solver()
        temp_s.add(melissa_end - melissa_start >= 75)
        temp_s.add(emily_end - emily_start >= 105)
        temp_s.add(joseph_end - joseph_start >= 120)
        temp_s.add(melissa_start >= melissa_avail_start)
        temp_s.add(melissa_end <= melissa_avail_end)
        temp_s.add(emily_start >= emily_avail_start)
        temp_s.add(emily_end <= emily_avail_end)
        temp_s.add(joseph_start >= joseph_avail_start)
        temp_s.add(joseph_end <= joseph_avail_end)

        first, second, third = order

        # First meeting constraints
        if first == 'melissa':
            first_start = melissa_start
            first_end = melissa_end
            first_loc = 'Financial District'
            temp_s.add(first_start >= get_travel('Fisherman\'s Wharf', first_loc))
        elif first == 'emily':
            first_start = emily_start
            first_end = emily_end
            first_loc = 'Presidio'
            temp_s.add(first_start >= get_travel('Fisherman\'s Wharf', first_loc))
        elif first == 'joseph':
            first_start = joseph_start
            first_end = joseph_end
            first_loc = 'Richmond District'
            temp_s.add(first_start >= get_travel('Fisherman\'s Wharf', first_loc))

        # Second meeting constraints
        if second == 'melissa':
            second_start = melissa_start
            second_end = melissa_end
            second_loc = 'Financial District'
            temp_s.add(second_start >= first_end + get_travel(first_loc, second_loc))
        elif second == 'emily':
            second_start = emily_start
            second_end = emily_end
            second_loc = 'Presidio'
            temp_s.add(second_start >= first_end + get_travel(first_loc, second_loc))
        elif second == 'joseph':
            second_start = joseph_start
            second_end = joseph_end
            second_loc = 'Richmond District'
            temp_s.add(second_start >= first_end + get_travel(first_loc, second_loc))

        # Third meeting constraints
        if third == 'melissa':
            third_start = melissa_start
            third_end = melissa_end
            third_loc = 'Financial District'
            temp_s.add(third_start >= second_end + get_travel(second_loc, third_loc))
        elif third == 'emily':
            third_start = emily_start
            third_end = emily_end
            third_loc = 'Presidio'
            temp_s.add(third_start >= second_end + get_travel(second_loc, third_loc))
        elif third == 'joseph':
            third_start = joseph_start
            third_end = joseph_end
            third_loc = 'Richmond District'
            temp_s.add(third_start >= second_end + get_travel(second_loc, third_loc))

        # Check if this order is feasible
        if temp_s.check() == sat:
            model = temp_s.model()
            
            # Convert times to readable format
            def to_time(minutes):
                hours = 9 + minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            
            print("SOLUTION:")
            print(f"Order of meetings: {order}")
            print(f"Meet Melissa: {to_time(model[melissa_start].as_long())} to {to_time(model[melissa_end].as_long())}")
            print(f"Meet Emily: {to_time(model[emily_start].as_long())} to {to_time(model[emily_end].as_long())}")
            print(f"Meet Joseph: {to_time(model[joseph_start].as_long())} to {to_time(model[joseph_end].as_long())}")
            return

    print("No feasible schedule found that meets all constraints.")

solve_scheduling()