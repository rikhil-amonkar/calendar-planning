from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Define travel times (in minutes)
    travel_times = {
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

    # Convert friend availability times to minutes since 9:00 AM
    emily_available_start = (16 * 60 + 15) - (9 * 60)  # 4:15 PM is 16:15
    emily_available_end = (21 * 60) - (9 * 60)         # 9:00 PM is 21:00
    joseph_available_start = (17 * 60 + 15) - (9 * 60)  # 5:15 PM is 17:15
    joseph_available_end = (22 * 60) - (9 * 60)         # 10:00 PM is 22:00
    melissa_available_start = (15 * 60 + 45) - (9 * 60) # 3:45 PM is 15:45
    melissa_available_end = (21 * 60 + 45) - (9 * 60)   # 9:45 PM is 21:45

    # Meeting duration constraints
    s.add(melissa_end - melissa_start >= 75)
    s.add(emily_end - emily_start >= 105)
    s.add(joseph_end - joseph_start >= 120)

    # Meeting must be within friend's availability
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)

    # Define possible orders of meetings
    orders = [
        ['melissa', 'emily', 'joseph'],
        ['melissa', 'joseph', 'emily'],
        ['emily', 'melissa', 'joseph'],
        ['emily', 'joseph', 'melissa'],
        ['joseph', 'melissa', 'emily'],
        ['joseph', 'emily', 'melissa']
    ]

    # Function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        if from_loc == 'Fisherman\'s Wharf':
            if to_loc == 'Financial District':
                return 11
            elif to_loc == 'Presidio':
                return 17
            elif to_loc == 'Richmond District':
                return 18
        elif from_loc == 'Financial District':
            if to_loc == 'Presidio':
                return 23
            elif to_loc == 'Richmond District':
                return 22
        elif from_loc == 'Presidio':
            if to_loc == 'Financial District':
                return 23
            elif to_loc == 'Richmond District':
                return 7
        elif from_loc == 'Richmond District':
            if to_loc == 'Financial District':
                return 22
            elif to_loc == 'Presidio':
                return 7
        return 0  # Should not happen if locations are correct

    # Iterate over all possible orders
    for order in orders:
        temp_s = Solver()

        # Add base constraints
        temp_s.add(melissa_end - melissa_start >= 75)
        temp_s.add(emily_end - emily_start >= 105)
        temp_s.add(joseph_end - joseph_start >= 120)
        temp_s.add(melissa_start >= melissa_available_start)
        temp_s.add(melissa_end <= melissa_available_end)
        temp_s.add(emily_start >= emily_available_start)
        temp_s.add(emily_end <= emily_available_end)
        temp_s.add(joseph_start >= joseph_available_start)
        temp_s.add(joseph_end <= joseph_available_end)

        # Define the order of meetings
        first, second, third = order

        # First meeting
        if first == 'melissa':
            first_start = melissa_start
            first_end = melissa_end
            first_loc = 'Financial District'
            temp_s.add(first_start >= get_travel_time('Fisherman\'s Wharf', first_loc))
        elif first == 'emily':
            first_start = emily_start
            first_end = emily_end
            first_loc = 'Presidio'
            temp_s.add(first_start >= get_travel_time('Fisherman\'s Wharf', first_loc))
        elif first == 'joseph':
            first_start = joseph_start
            first_end = joseph_end
            first_loc = 'Richmond District'
            temp_s.add(first_start >= get_travel_time('Fisherman\'s Wharf', first_loc))

        # Second meeting
        if second == 'melissa':
            second_start = melissa_start
            second_end = melissa_end
            second_loc = 'Financial District'
            temp_s.add(second_start >= first_end + get_travel_time(first_loc, second_loc))
        elif second == 'emily':
            second_start = emily_start
            second_end = emily_end
            second_loc = 'Presidio'
            temp_s.add(second_start >= first_end + get_travel_time(first_loc, second_loc))
        elif second == 'joseph':
            second_start = joseph_start
            second_end = joseph_end
            second_loc = 'Richmond District'
            temp_s.add(second_start >= first_end + get_travel_time(first_loc, second_loc))

        # Third meeting
        if third == 'melissa':
            third_start = melissa_start
            third_end = melissa_end
            third_loc = 'Financial District'
            temp_s.add(third_start >= second_end + get_travel_time(second_loc, third_loc))
        elif third == 'emily':
            third_start = emily_start
            third_end = emily_end
            third_loc = 'Presidio'
            temp_s.add(third_start >= second_end + get_travel_time(second_loc, third_loc))
        elif third == 'joseph':
            third_start = joseph_start
            third_end = joseph_end
            third_loc = 'Richmond District'
            temp_s.add(third_start >= second_end + get_travel_time(second_loc, third_loc))

        # Check if this order is feasible
        if temp_s.check() == sat:
            model = temp_s.model()
            # Convert to human-readable times
            def minutes_to_time(minutes):
                hours = 9 + minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            
            print("SOLUTION:")
            print(f"Order of meetings: {order}")
            print(f"Meet Melissa from {minutes_to_time(model[melissa_start].as_long())} to {minutes_to_time(model[melissa_end].as_long())}")
            print(f"Meet Emily from {minutes_to_time(model[emily_start].as_long())} to {minutes_to_time(model[emily_end].as_long())}")
            print(f"Meet Joseph from {minutes_to_time(model[joseph_start].as_long())} to {minutes_to_time(model[joseph_end].as_long())}")
            return

    print("No feasible schedule found.")

# Call the function to solve the problem
solve_scheduling()