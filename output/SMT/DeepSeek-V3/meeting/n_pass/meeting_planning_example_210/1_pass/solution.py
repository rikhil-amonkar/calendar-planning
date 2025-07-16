from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Melissa at Financial District
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')
    # Emily at Presidio
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    # Joseph at Richmond District
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Define travel time variables (in minutes since 9:00 AM)
    travel_to_melissa = 11  # Fisherman's Wharf to Financial District
    travel_to_emily = 17    # Fisherman's Wharf to Presidio
    travel_to_joseph = 18   # Fisherman's Wharf to Richmond District
    travel_melissa_to_emily = 23  # Financial District to Presidio
    travel_melissa_to_joseph = 22 # Financial District to Richmond District
    travel_emily_to_melissa = 23  # Presidio to Financial District
    travel_emily_to_joseph = 7    # Presidio to Richmond District
    travel_joseph_to_melissa = 22 # Richmond District to Financial District
    travel_joseph_to_emily = 7    # Richmond District to Presidio

    # Convert friend availability times to minutes since 9:00 AM
    emily_available_start = (16 * 60 + 15) - (9 * 60)  # 4:15 PM is 16:15, 9:00 AM is 9:00
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

    # The initial location is Fisherman's Wharf at time 0 (9:00 AM)
    # We need to decide the order of meetings. There are 3! = 6 possible orders.
    # We'll model the order as a choice between the possible permutations.

    # Let's define variables to represent the order.
    # We'll use three integers to represent the order of meetings:
    # 1: Melissa, 2: Emily, 3: Joseph
    # So the order could be 1-2-3, 1-3-2, 2-1-3, etc.

    # To model the order, we'll create auxiliary variables and constraints.
    # Alternatively, we can try all possible orders by creating separate constraints for each order.

    # We'll model the order as follows: first, second, third meetings.
    # Each meeting is assigned a position in the sequence.

    # Create a list to hold the possible orders
    orders = [
        ('melissa', 'emily', 'joseph'),
        ('melissa', 'joseph', 'emily'),
        ('emily', 'melissa', 'joseph'),
        ('emily', 'joseph', 'melissa'),
        ('joseph', 'melissa', 'emily'),
        ('joseph', 'emily', 'melissa')
    ]

    # We'll create a sub-solver for each order and check satisfiability
    # Alternatively, we can use a single solver with disjunctions, but it's more complex.

    # For simplicity, we'll iterate over possible orders and check each one.
    # This is less elegant but straightforward.

    found_solution = False
    solution = None

    for order in orders:
        # Create a new solver for this order
        temp_s = Solver()

        # Add the same base constraints
        temp_s.add(melissa_end - melissa_start >= 75)
        temp_s.add(emily_end - emily_start >= 105)
        temp_s.add(joseph_end - joseph_start >= 120)
        temp_s.add(melissa_start >= melissa_available_start)
        temp_s.add(melissa_end <= melissa_available_end)
        temp_s.add(emily_start >= emily_available_start)
        temp_s.add(emily_end <= emily_available_end)
        temp_s.add(joseph_start >= joseph_available_start)
        temp_s.add(joseph_end <= joseph_available_end)

        first, second, third = order

        # Constraints for the first meeting
        if first == 'melissa':
            # Start at Fisherman's Wharf, travel to Financial District (11 minutes)
            temp_s.add(melissa_start >= travel_to_melissa)
            first_end = melissa_end
            first_location = 'melissa'
        elif first == 'emily':
            # Travel to Presidio (17 minutes)
            temp_s.add(emily_start >= travel_to_emily)
            first_end = emily_end
            first_location = 'emily'
        elif first == 'joseph':
            # Travel to Richmond District (18 minutes)
            temp_s.add(joseph_start >= travel_to_joseph)
            first_end = joseph_end
            first_location = 'joseph'

        # Constraints for the second meeting
        if second == 'melissa':
            # Travel from first_location to Financial District
            if first_location == 'emily':
                travel_time = travel_emily_to_melissa
            elif first_location == 'joseph':
                travel_time = travel_joseph_to_melissa
            else:
                travel_time = 0  # shouldn't happen
            temp_s.add(melissa_start >= first_end + travel_time)
            second_end = melissa_end
            second_location = 'melissa'
        elif second == 'emily':
            # Travel from first_location to Presidio
            if first_location == 'melissa':
                travel_time = travel_melissa_to_emily
            elif first_location == 'joseph':
                travel_time = travel_joseph_to_emily
            else:
                travel_time = 0
            temp_s.add(emily_start >= first_end + travel_time)
            second_end = emily_end
            second_location = 'emily'
        elif second == 'joseph':
            # Travel from first_location to Richmond District
            if first_location == 'melissa':
                travel_time = travel_melissa_to_joseph
            elif first_location == 'emily':
                travel_time = travel_emily_to_joseph
            else:
                travel_time = 0
            temp_s.add(joseph_start >= first_end + travel_time)
            second_end = joseph_end
            second_location = 'joseph'

        # Constraints for the third meeting
        if third == 'melissa':
            # Travel from second_location to Financial District
            if second_location == 'emily':
                travel_time = travel_emily_to_melissa
            elif second_location == 'joseph':
                travel_time = travel_joseph_to_melissa
            else:
                travel_time = 0
            temp_s.add(melissa_start >= second_end + travel_time)
        elif third == 'emily':
            # Travel from second_location to Presidio
            if second_location == 'melissa':
                travel_time = travel_melissa_to_emily
            elif second_location == 'joseph':
                travel_time = travel_joseph_to_emily
            else:
                travel_time = 0
            temp_s.add(emily_start >= second_end + travel_time)
        elif third == 'joseph':
            # Travel from second_location to Richmond District
            if second_location == 'melissa':
                travel_time = travel_melissa_to_joseph
            elif second_location == 'emily':
                travel_time = travel_emily_to_joseph
            else:
                travel_time = 0
            temp_s.add(joseph_start >= second_end + travel_time)

        # Check if this order is feasible
        if temp_s.check() == sat:
            model = temp_s.model()
            # Extract the solution
            solution = {
                'order': order,
                'melissa_start': model[melissa_start].as_long(),
                'melissa_end': model[melissa_end].as_long(),
                'emily_start': model[emily_start].as_long(),
                'emily_end': model[emily_end].as_long(),
                'joseph_start': model[joseph_start].as_long(),
                'joseph_end': model[joseph_end].as_long()
            }
            found_solution = True
            break

    if not found_solution:
        print("No feasible schedule found.")
        return None

    # Convert the solution to human-readable times
    def minutes_to_time(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    print("SOLUTION:")
    print(f"Order of meetings: {solution['order']}")
    print(f"Meet Melissa from {minutes_to_time(solution['melissa_start'])} to {minutes_to_time(solution['melissa_end'])}")
    print(f"Meet Emily from {minutes_to_time(solution['emily_start'])} to {minutes_to_time(solution['emily_end'])}")
    print(f"Meet Joseph from {minutes_to_time(solution['joseph_start'])} to {minutes_to_time(solution['joseph_end'])}")

    return solution

# Call the function to solve the problem
solve_scheduling()