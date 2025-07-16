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
    travel_wharf_presidio = 17
    travel_wharf_richmond = 18
    travel_richmond_presidio = 7

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

    # Define variables to represent the order of meetings
    order_betty = Int('order_betty')
    order_david = Int('order_david')
    order_barbara = Int('order_barbara')

    # Each order variable must be 1, 2, or 3
    s.add(Or(order_betty == 1, order_betty == 2, order_betty == 3))
    s.add(Or(order_david == 1, order_david == 2, order_david == 3))
    s.add(Or(order_barbara == 1, order_barbara == 2, order_barbara == 3))

    # All orders must be distinct
    s.add(Distinct(order_betty, order_david, order_barbara))

    # Define variables for the start times relative to order
    first_start = Int('first_start')
    second_start = Int('second_start')
    third_start = Int('third_start')

    # Define variables for the end times relative to order
    first_end = Int('first_end')
    second_end = Int('second_end')
    third_end = Int('third_end')

    # Define variables for the travel times between meetings
    travel_first_to_second = Int('travel_first_to_second')
    travel_second_to_third = Int('travel_second_to_third')

    # Constraints for the first meeting
    s.add(first_start == If(order_betty == 1, betty_start,
                         If(order_david == 1, david_start,
                         If(order_barbara == 1, barbara_start, -1))))

    s.add(first_end == If(order_betty == 1, betty_end,
                       If(order_david == 1, david_end,
                       If(order_barbara == 1, barbara_end, -1))))

    # Travel time to first location depends on the location
    s.add(If(order_betty == 1, first_start >= arrival_time + travel_emb_presidio,
          If(order_david == 1, first_start >= arrival_time + travel_emb_richmond,
          If(order_barbara == 1, first_start >= arrival_time + travel_emb_wharf, False))))

    # Constraints for the second meeting
    s.add(second_start == If(order_betty == 2, betty_start,
                          If(order_david == 2, david_start,
                          If(order_barbara == 2, barbara_start, -1))))

    s.add(second_end == If(order_betty == 2, betty_end,
                        If(order_david == 2, david_end,
                        If(order_barbara == 2, barbara_end, -1))))

    # Travel time from first to second location
    s.add(travel_first_to_second == 
          If(And(order_betty == 1, order_david == 2), travel_presidio_richmond,
          If(And(order_betty == 1, order_barbara == 2), travel_presidio_wharf,
          If(And(order_david == 1, order_betty == 2), travel_richmond_presidio,
          If(And(order_david == 1, order_barbara == 2), travel_richmond_wharf,
          If(And(order_barbara == 1, order_betty == 2), travel_wharf_presidio,
          If(And(order_barbara == 1, order_david == 2), travel_wharf_richmond, -1))))))

    s.add(second_start >= first_end + travel_first_to_second)

    # Constraints for the third meeting
    s.add(third_start == If(order_betty == 3, betty_start,
                         If(order_david == 3, david_start,
                         If(order_barbara == 3, barbara_start, -1))))

    s.add(third_end == If(order_betty == 3, betty_end,
                       If(order_david == 3, david_end,
                       If(order_barbara == 3, barbara_end, -1))))

    # Travel time from second to third location
    s.add(travel_second_to_third == 
          If(And(order_betty == 2, order_david == 3), travel_presidio_richmond,
          If(And(order_betty == 2, order_barbara == 3), travel_presidio_wharf,
          If(And(order_david == 2, order_betty == 3), travel_richmond_presidio,
          If(And(order_david == 2, order_barbara == 3), travel_richmond_wharf,
          If(And(order_barbara == 2, order_betty == 3), travel_wharf_presidio,
          If(And(order_barbara == 2, order_david == 3), travel_wharf_richmond, -1))))))

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