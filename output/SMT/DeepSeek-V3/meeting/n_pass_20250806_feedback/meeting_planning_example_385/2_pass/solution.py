from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables for each meeting in minutes since 9:00 AM (540 minutes since midnight)
    # Meetings: John, Steven, Barbara
    start_john = Int('start_john')
    end_john = Int('end_john')
    start_steven = Int('start_steven')
    end_steven = Int('end_steven')
    start_barbara = Int('start_barbara')
    end_barbara = Int('end_barbara')

    # Convert all time windows to minutes since midnight for easier arithmetic
    # John: 9:00 AM - 1:30 PM (540 - 810 minutes)
    # Minimum duration: 15 minutes
    # Location: Pacific Heights. Travel time from Nob Hill: 8 minutes.
    s.add(start_john >= 540 + 8)  # earliest start after travel
    s.add(end_john == start_john + 15)
    s.add(end_john <= 810)  # John's window ends at 1:30 PM (810 minutes)

    # Steven: 1:30 PM - 10:00 PM (810 - 1320 minutes)
    # Minimum duration: 45 minutes
    # Location: North Beach. Travel time from Pacific Heights: 9 minutes.
    s.add(start_steven >= end_john + 9)  # travel from Pacific Heights to North Beach
    s.add(start_steven >= 810)  # Steven's window starts at 1:30 PM (810 minutes)
    s.add(end_steven == start_steven + 45)
    s.add(end_steven <= 1320)  # Steven's window ends at 10:00 PM (1320 minutes)

    # Barbara: 6:00 PM - 9:30 PM (1080 - 1290 minutes)
    # Minimum duration: 30 minutes
    # Location: Fisherman's Wharf. Travel time from North Beach: 6 minutes.
    s.add(start_barbara >= end_steven + 6)  # travel from North Beach to Fisherman's Wharf
    s.add(start_barbara >= 1080)  # Barbara's window starts at 6:00 PM (1080 minutes)
    s.add(end_barbara == start_barbara + 30)
    s.add(end_barbara <= 1290)  # Barbara's window ends at 9:30 PM (1290 minutes)

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = minutes  # since variables are in minutes since midnight
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"

        # Collect meetings
        itinerary = []

        # John's meeting
        start_john_val = m.evaluate(start_john).as_long()
        end_john_val = m.evaluate(end_john).as_long()
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": minutes_to_time(start_john_val),
            "end_time": minutes_to_time(end_john_val)
        })

        # Steven's meeting
        start_steven_val = m.evaluate(start_steven).as_long()
        end_steven_val = m.evaluate(end_steven).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Steven",
            "start_time": minutes_to_time(start_steven_val),
            "end_time": minutes_to_time(end_steven_val)
        })

        # Barbara's meeting
        start_barbara_val = m.evaluate(start_barbara).as_long()
        end_barbara_val = m.evaluate(end_barbara).as_long()
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_time(start_barbara_val),
            "end_time": minutes_to_time(end_barbara_val)
        })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver and print the result
result = solve_scheduling()
print(result)