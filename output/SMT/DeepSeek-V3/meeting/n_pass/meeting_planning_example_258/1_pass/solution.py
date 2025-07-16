from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Betty at Presidio
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    # David at Richmond District
    david_start = Int('david_start')
    david_end = Int('david_end')
    # Barbara at Fisherman's Wharf
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')

    # Define travel times (in minutes)
    travel_emb_presidio = 20
    travel_emb_richmond = 21
    travel_emb_wharf = 6
    travel_presidio_richmond = 7
    travel_presidio_wharf = 19
    travel_richmond_wharf = 18

    # Convert all times to minutes since 9:00 AM (540 minutes)
    arrival_time = 540  # 9:00 AM in minutes

    # Friends' availability windows in minutes since midnight
    betty_available_start = 615  # 10:15 AM
    betty_available_end = 1290   # 9:30 PM
    david_available_start = 780  # 1:00 PM
    david_available_end = 1215   # 8:15 PM
    barbara_available_start = 555  # 9:15 AM
    barbara_available_end = 1215   # 8:15 PM

    # Meeting durations in minutes
    betty_duration = 45
    david_duration = 90
    barbara_duration = 120

    # Constraints for each meeting
    # Betty's meeting must be within her availability and duration
    s.add(betty_start >= betty_available_start)
    s.add(betty_end <= betty_available_end)
    s.add(betty_end == betty_start + betty_duration)

    # David's meeting
    s.add(david_start >= david_available_start)
    s.add(david_end <= david_available_end)
    s.add(david_end == david_start + david_duration)

    # Barbara's meeting
    s.add(barbara_start >= barbara_available_start)
    s.add(barbara_end <= barbara_available_end)
    s.add(barbara_end == barbara_start + barbara_duration)

    # Initial location is Embarcadero at 540 (9:00 AM)
    # We need to sequence the meetings considering travel times

    # There are 3! = 6 possible orders to visit the friends.
    # We'll model the possible orders and let Z3 find a feasible one.

    # Let's define variables to represent the order.
    # We'll use integers to represent the position in the sequence (1, 2, 3)
    order_betty = Int('order_betty')
    order_david = Int('order_david')
    order_barbara = Int('order_barbara')

    # Each order variable must be 1, 2, or 3
    s.add(Or(order_betty == 1, order_betty == 2, order_betty == 3))
    s.add(Or(order_david == 1, order_david == 2, order_david == 3))
    s.add(Or(order_barbara == 1, order_barbara == 2, order_barbara == 3))

    # All orders must be distinct
    s.add(Distinct(order_betty, order_david, order_barbara))

    # Now, we need to ensure that the start times respect the order and travel times.

    # For each possible order, we'll add constraints that the start time of a later meeting is after the previous meeting's end time plus travel time.

    # We'll create variables to represent the end time plus travel time to the next location.
    # For each friend, the next travel depends on the next location in the sequence.

    # We'll also need to track the current location after each step.
    # Let's model the location after each step as an integer (0: Embarcadero, 1: Presidio, 2: Richmond, 3: Fisherman's Wharf)

    # Variables for location after each step
    loc_after_1 = Int('loc_after_1')  # after first meeting
    loc_after_2 = Int('loc_after_2')  # after second meeting
    loc_after_3 = Int('loc_after_3')  # after third meeting

    # Initial location is 0 (Embarcadero)
    # The first meeting's location depends on order_betty, order_david, order_barbara being 1.

    # For each possible first meeting, set loc_after_1 accordingly.
    s.add(If(order_betty == 1, loc_after_1 == 1, 
          If(order_david == 1, loc_after_1 == 2, 
          If(order_barbara == 1, loc_after_1 == 3, False))))

    # Similarly for the second and third meetings.
    s.add(If(order_betty == 2, loc_after_2 == 1, 
          If(order_david == 2, loc_after_2 == 2, 
          If(order_barbara == 2, loc_after_2 == 3, False))))
    s.add(If(order_betty == 3, loc_after_3 == 1, 
          If(order_david == 3, loc_after_3 == 2, 
          If(order_barbara == 3, loc_after_3 == 3, False))))

    # Now, the start time of each meeting must be after the previous meeting's end time plus travel time from the previous location.

    # Define variables for the start times relative to order.
    # For example, the first meeting's start time must be >= arrival_time + travel from Embarcadero to the first location.

    # First meeting's start time constraints.
    first_start = Int('first_start')
    s.add(first_start == If(order_betty == 1, betty_start,
                         If(order_david == 1, david_start,
                         If(order_barbara == 1, barbara_start, -1))))

    # Travel time to first location depends on the location.
    travel_to_first = Int('travel_to_first')
    s.add(travel_to_first == If(order_betty == 1, travel_emb_presidio,
                             If(order_david == 1, travel_emb_richmond,
                             If(order_barbara == 1, travel_emb_wharf, -1))))

    s.add(first_start >= arrival_time + travel_to_first)

    # Second meeting's start time must be after first's end time plus travel from first location to second.
    second_start = Int('second_start')
    s.add(second_start == If(order_betty == 2, betty_start,
                          If(order_david == 2, david_start,
                          If(order_barbara == 2, barbara_start, -1))))

    first_end = Int('first_end')
    s.add(first_end == If(order_betty == 1, betty_end,
                       If(order_david == 1, david_end,
                       If(order_barbara == 1, barbara_end, -1))))

    travel_first_to_second = Int('travel_first_to_second')
    # The travel depends on loc_after_1 and the second location.
    s.add(travel_first_to_second == 
          If(And(order_betty == 2, loc_after_1 == 1), 0,  # from Presidio to Presidio (invalid)
          If(And(order_betty == 2, loc_after_1 == 0), travel_emb_presidio,
          If(And(order_betty == 2, loc_after_1 == 2), travel_richmond_presidio,
          If(And(order_betty == 2, loc_after_1 == 3), travel_wharf_presidio,
          If(And(order_david == 2, loc_after_1 == 0), travel_emb_richmond,
          If(And(order_david == 2, loc_after_1 == 1), travel_presidio_richmond,
          If(And(order_david == 2, loc_after_1 == 3), travel_wharf_richmond,
          If(And(order_barbara == 2, loc_after_1 == 0), travel_emb_wharf,
          If(And(order_barbara == 2, loc_after_1 == 1), travel_presidio_wharf,
          If(And(order_barbara == 2, loc_after_1 == 2), travel_richmond_wharf, -1))))))))))

    # Fixing travel times between locations (some were not defined in the original problem)
    travel_wharf_presidio = 17
    travel_wharf_richmond = 18
    travel_richmond_presidio = 7

    s.add(travel_first_to_second == 
          If(And(order_betty == 2, loc_after_1 == 0), travel_emb_presidio,
          If(And(order_betty == 2, loc_after_1 == 2), travel_richmond_presidio,
          If(And(order_betty == 2, loc_after_1 == 3), travel_wharf_presidio,
          If(And(order_david == 2, loc_after_1 == 0), travel_emb_richmond,
          If(And(order_david == 2, loc_after_1 == 1), travel_presidio_richmond,
          If(And(order_david == 2, loc_after_1 == 3), travel_wharf_richmond,
          If(And(order_barbara == 2, loc_after_1 == 0), travel_emb_wharf,
          If(And(order_barbara == 2, loc_after_1 == 1), travel_presidio_wharf,
          If(And(order_barbara == 2, loc_after_1 == 2), travel_richmond_wharf, -1)))))))))

    s.add(second_start >= first_end + travel_first_to_second)

    # Third meeting's start time must be after second's end time plus travel from second location to third.
    third_start = Int('third_start')
    s.add(third_start == If(order_betty == 3, betty_start,
                         If(order_david == 3, david_start,
                         If(order_barbara == 3, barbara_start, -1))))

    second_end = Int('second_end')
    s.add(second_end == If(order_betty == 2, betty_end,
                        If(order_david == 2, david_end,
                        If(order_barbara == 2, barbara_end, -1))))

    travel_second_to_third = Int('travel_second_to_third')
    s.add(travel_second_to_third == 
          If(And(order_betty == 3, loc_after_2 == 0), travel_emb_presidio,
          If(And(order_betty == 3, loc_after_2 == 2), travel_richmond_presidio,
          If(And(order_betty == 3, loc_after_2 == 3), travel_wharf_presidio,
          If(And(order_david == 3, loc_after_2 == 0), travel_emb_richmond,
          If(And(order_david == 3, loc_after_2 == 1), travel_presidio_richmond,
          If(And(order_david == 3, loc_after_2 == 3), travel_wharf_richmond,
          If(And(order_barbara == 3, loc_after_2 == 0), travel_emb_wharf,
          If(And(order_barbara == 3, loc_after_2 == 1), travel_presidio_wharf,
          If(And(order_barbara == 3, loc_after_2 == 2), travel_richmond_wharf, -1)))))))))

    s.add(third_start >= second_end + travel_second_to_third)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Extract the meeting times
        betty_s = m.eval(betty_start).as_long()
        betty_e = m.eval(betty_end).as_long()
        david_s = m.eval(david_start).as_long()
        david_e = m.eval(david_end).as_long()
        barbara_s = m.eval(barbara_start).as_long()
        barbara_e = m.eval(barbara_end).as_long()

        # Convert minutes back to time strings
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"

        print("SOLUTION:")
        print(f"Meet Betty at Presidio from {minutes_to_time(betty_s)} to {minutes_to_time(betty_e)}")
        print(f"Meet David at Richmond District from {minutes_to_time(david_s)} to {minutes_to_time(david_e)}")
        print(f"Meet Barbara at Fisherman's Wharf from {minutes_to_time(barbara_s)} to {minutes_to_time(barbara_e)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()