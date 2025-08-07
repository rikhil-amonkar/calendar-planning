from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    melissa_start = Int('melissa_start')
    melissa_end = Int('melissa_end')

    # Convert friends' availability windows to minutes since 9:00 AM
    # Emily: 4:15 PM to 9:00 PM -> 15:15 to 21:00 -> 6*60 + 15 = 375 to 12*60 + 60*9 = 720
    emily_available_start = 15 * 60 + 15  # 15:15 is 6 hours and 15 minutes after 9:00 AM (9*60 + 6*60 +15 = 540 + 15 = 555 minutes since midnight, but since we start at 9:00 AM, it's 6*60 +15 = 375 minutes)
    emily_available_end = 21 * 60  # 21:00 is 12 hours after 9:00 AM (12*60 = 720 minutes)

    # Joseph: 5:15 PM to 10:00 PM -> 17:15 to 22:00 -> 8*60 +15 = 495 to 13*60 = 780
    joseph_available_start = 17 * 60 + 15  # 8*60 +15 = 495
    joseph_available_end = 22 * 60  # 13*60 = 780

    # Melissa: 3:45 PM to 9:45 PM -> 15:45 to 21:45 -> 6*60 +45 = 405 to 12*60 +45 = 765
    melissa_available_start = 15 * 60 + 45  # 6*60 +45 = 405
    melissa_available_end = 21 * 60 + 45  # 12*60 +45 = 765

    # Minimum durations in minutes
    emily_min_duration = 105
    joseph_min_duration = 120
    melissa_min_duration = 75

    # Add constraints for each meeting's duration and availability
    s.add(emily_end - emily_start >= emily_min_duration)
    s.add(emily_start >= emily_available_start)
    s.add(emily_end <= emily_available_end)

    s.add(joseph_end - joseph_start >= joseph_min_duration)
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)

    s.add(melissa_end - melissa_start >= melissa_min_duration)
    s.add(melissa_start >= melissa_available_start)
    s.add(melissa_end <= melissa_available_end)

    # Initial location: Fisherman's Wharf at time 0 (9:00 AM)
    # The first meeting can be any of the three, but we need to ensure travel times are considered.

    # Define the order of meetings. We'll try all possible permutations of the three meetings and pick the feasible one.
    # But since Z3 can't directly handle permutations, we'll model the sequence with variables indicating the order.

    # We'll model the sequence as a list where each meeting is assigned a position (1, 2, 3)
    # Then, the start time of each meeting must be after the previous meeting's end time plus travel time.

    # Define position variables for each meeting (1, 2, or 3)
    emily_pos = Int('emily_pos')
    joseph_pos = Int('joseph_pos')
    melissa_pos = Int('melissa_pos')

    # Each position is between 1 and 3
    s.add(emily_pos >= 1, emily_pos <= 3)
    s.add(joseph_pos >= 1, joseph_pos <= 3)
    s.add(melissa_pos >= 1, melissa_pos <= 3)

    # All positions are distinct
    s.add(Distinct(emily_pos, joseph_pos, melissa_pos))

    # Travel times between locations (in minutes)
    travel = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # The first meeting's start time must be >= travel time from Fisherman's Wharf to its location.
    # For each meeting, if it's first, its start time >= travel from Fisherman's Wharf to its location.
    s.add(Implies(emily_pos == 1, emily_start >= travel[('Fisherman\'s Wharf', 'Presidio')]))
    s.add(Implies(joseph_pos == 1, joseph_start >= travel[('Fisherman\'s Wharf', 'Richmond District')]))
    s.add(Implies(melissa_pos == 1, melissa_start >= travel[('Fisherman\'s Wharf', 'Financial District')]))

    # For meetings that are not first, their start time must be >= the end time of the previous meeting plus travel time.
    # We need to model the travel time based on the previous meeting's location.

    # Previous location for each meeting:
    # If a meeting is in position 2:
    #   its previous location is the location of the meeting in position 1.
    # Similarly for position 3.

    # We'll create variables to represent the location at each position (1, 2, 3).
    # Locations are represented as integers: 1 = Presidio, 2 = Richmond District, 3 = Financial District.

    # Location variables for each position
    loc1 = Int('loc1')
    loc2 = Int('loc2')
    loc3 = Int('loc3')

    s.add(loc1 >= 1, loc1 <= 3)
    s.add(loc2 >= 1, loc2 <= 3)
    s.add(loc3 >= 1, loc3 <= 3)

    # Link meeting positions to locations
    s.add(Implies(emily_pos == 1, loc1 == 1))
    s.add(Implies(joseph_pos == 1, loc1 == 2))
    s.add(Implies(melissa_pos == 1, loc1 == 3))

    s.add(Implies(emily_pos == 2, loc2 == 1))
    s.add(Implies(joseph_pos == 2, loc2 == 2))
    s.add(Implies(melissa_pos == 2, loc2 == 3))

    s.add(Implies(emily_pos == 3, loc3 == 1))
    s.add(Implies(joseph_pos == 3, loc3 == 2))
    s.add(Implies(melissa_pos == 3, loc3 == 3))

    # Now, for meetings in position 2: their start time >= end time of position 1 meeting + travel time from loc1 to their location.
    s.add(Implies(And(emily_pos == 2, loc1 == 1), emily_start >= (melissa_pos == 1, melissa_end) + travel[('Presidio', 'Presidio')]))  # Not possible, but for completeness.
    s.add(Implies(And(emily_pos == 2, loc1 == 2), emily_start >= If(joseph_pos == 1, joseph_end, 0) + travel[('Richmond District', 'Presidio')]))
    s.add(Implies(And(emily_pos == 2, loc1 == 3), emily_start >= If(melissa_pos == 1, melissa_end, 0) + travel[('Financial District', 'Presidio')]))

    s.add(Implies(And(joseph_pos == 2, loc1 == 1), joseph_start >= If(emily_pos == 1, emily_end, 0) + travel[('Presidio', 'Richmond District')]))
    s.add(Implies(And(joseph_pos == 2, loc1 == 2), joseph_start >= If(joseph_pos == 1, joseph_end, 0) + travel[('Richmond District', 'Richmond District')]))  # Not possible.
    s.add(Implies(And(joseph_pos == 2, loc1 == 3), joseph_start >= If(melissa_pos == 1, melissa_end, 0) + travel[('Financial District', 'Richmond District')]))

    s.add(Implies(And(melissa_pos == 2, loc1 == 1), melissa_start >= If(emily_pos == 1, emily_end, 0) + travel[('Presidio', 'Financial District')]))
    s.add(Implies(And(melissa_pos == 2, loc1 == 2), melissa_start >= If(joseph_pos == 1, joseph_end, 0) + travel[('Richmond District', 'Financial District')]))
    s.add(Implies(And(melissa_pos == 2, loc1 == 3), melissa_start >= If(melissa_pos == 1, melissa_end, 0) + travel[('Financial District', 'Financial District')]))  # Not possible.

    # Similarly for position 3 meetings.
    s.add(Implies(And(emily_pos == 3, loc2 == 1), emily_start >= If(Or(And(emily_pos == 2, loc1 == 1), And(joseph_pos == 2, loc1 == 1), And(melissa_pos == 2, loc1 == 1)), 
                                                                    If(emily_pos == 2, emily_end, If(joseph_pos == 2, joseph_end, melissa_end)), 0) + travel[('Presidio', 'Presidio')]))
    s.add(Implies(And(emily_pos == 3, loc2 == 2), emily_start >= If(Or(And(emily_pos == 2, loc1 == 2), And(joseph_pos == 2, loc1 == 2), And(melissa_pos == 2, loc1 == 2)), 
                                                                    If(emily_pos == 2, emily_end, If(joseph_pos == 2, joseph_end, melissa_end)), 0) + travel[('Richmond District', 'Presidio')]))
    s.add(Implies(And(emily_pos == 3, loc2 == 3), emily_start >= If(Or(And(emily_pos == 2, loc1 == 3), And(joseph_pos == 2, loc1 == 3), And(melissa_pos == 2, loc1 == 3)), 
                                                                    If(emily_pos == 2, emily_end, If(joseph_pos == 2, joseph_end, melissa_end)), 0) + travel[('Financial District', 'Presidio')]))

    # Similarly for Joseph and Melissa in position 3. This is getting complex; perhaps a better approach is needed.

    # Alternatively, since there are only 3! = 6 possible orders, we can check each one.
    # Let's try a different approach: enumerate all possible orders and check feasibility for each.

    # We'll create a list of all possible permutations of the three meetings.
    from itertools import permutations
    possible_orders = list(permutations(['Emily', 'Joseph', 'Melissa']))

    # We'll use the solver to check each order.
    # For each order, we'll set the positions accordingly and check if the schedule is feasible.

    # We'll loop through each possible order and attempt to find a feasible schedule.
    feasible_schedule = None
    for order in possible_orders:
        s.push()  # Save the current solver state

        # Assign positions based on the current order
        emily_p = order.index('Emily') + 1
        joseph_p = order.index('Joseph') + 1
        melissa_p = order.index('Melissa') + 1

        s.add(emily_pos == emily_p)
        s.add(joseph_pos == joseph_p)
        s.add(melissa_pos == melissa_p)

        # Check if the current order is feasible
        if s.check() == sat:
            model = s.model()
            # Extract the meeting times
            emily_s = model[emily_start].as_long()
            emily_e = model[emily_end].as_long()
            joseph_s = model[joseph_start].as_long()
            joseph_e = model[joseph_end].as_long()
            melissa_s = model[melissa_start].as_long()
            melissa_e = model[melissa_end].as_long()

            # Convert minutes since 9:00 AM to HH:MM format
            def minutes_to_time(minutes):
                hours = 9 + minutes // 60
                mins = minutes % 60
                return f"{hours:02d}:{mins:02d}"

            itinerary = []
            # Add meetings in the order of the current permutation
            for person in order:
                if person == 'Emily':
                    itinerary.append({
                        "action": "meet",
                        "person": "Emily",
                        "start_time": minutes_to_time(emily_s),
                        "end_time": minutes_to_time(emily_e)
                    })
                elif person == 'Joseph':
                    itinerary.append({
                        "action": "meet",
                        "person": "Joseph",
                        "start_time": minutes_to_time(joseph_s),
                        "end_time": minutes_to_time(joseph_e)
                    })
                elif person == 'Melissa':
                    itinerary.append({
                        "action": "meet",
                        "person": "Melissa",
                        "start_time": minutes_to_time(melissa_s),
                        "end_time": minutes_to_time(melissa_e)
                    })

            feasible_schedule = {"itinerary": itinerary}
            s.pop()
            break  # Stop at the first feasible schedule found
        else:
            s.pop()  # Restore the solver state

    if feasible_schedule is None:
        return {"itinerary": []}
    else:
        return feasible_schedule

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))