from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the time variables for each meeting
    # Kevin at Alamo Square
    kevin_start = Int('kevin_start')
    kevin_end = Int('kevin_end')
    # Kimberly at Russian Hill
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    # Joseph at Presidio
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    # Thomas at Financial District
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Convert all times to minutes since midnight for easier calculations
    # Kevin's availability: 8:15 AM (495) to 9:30 PM (1290)
    s.add(kevin_start >= 495, kevin_end <= 1290)
    s.add(kevin_end - kevin_start >= 75)  # At least 75 minutes

    # Kimberly's availability: 8:45 AM (525) to 12:30 PM (750)
    s.add(kimberly_start >= 525, kimberly_end <= 750)
    s.add(kimberly_end - kimberly_start >= 30)  # At least 30 minutes

    # Joseph's availability: 6:30 PM (1170) to 7:15 PM (1185)
    s.add(joseph_start >= 1170, joseph_end <= 1185)
    s.add(joseph_end - joseph_start >= 45)  # At least 45 minutes

    # Thomas's availability: 7:00 PM (1200) to 9:45 PM (1305)
    s.add(thomas_start >= 1200, thomas_end <= 1305)
    s.add(thomas_end - thomas_start >= 45)  # At least 45 minutes

    # Starting at Sunset District at 9:00 AM (540)
    # Define the order of meetings and travel times
    # We need to ensure that the travel times are accounted for between meetings

    # Possible orderings:
    # 1. Kevin -> Kimberly -> Joseph -> Thomas
    # 2. Kimberly -> Kevin -> Joseph -> Thomas
    # 3. Kevin -> Kimberly -> Thomas -> Joseph (but Joseph's time is before Thomas's)
    # etc. We'll try to find a feasible order.

    # Let's try the order: Kimberly -> Kevin -> Joseph -> Thomas

    # Travel from Sunset to Russian Hill: 24 minutes
    s.add(kimberly_start >= 540 + 24)

    # After Kimberly, travel to Alamo Square: 13 minutes
    s.add(kevin_start >= kimberly_end + 13)

    # After Kevin, travel to Presidio: 18 minutes
    s.add(joseph_start >= kevin_end + 18)

    # After Joseph, travel to Financial District: 22 minutes
    s.add(thomas_start >= joseph_end + 22)

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []

        # Helper function to convert minutes to HH:MM
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        # Add Kimberly's meeting
        itinerary.append({
            "action": "meet",
            "person": "Kimberly",
            "start_time": to_time(m[kimberly_start].as_long()),
            "end_time": to_time(m[kimberly_end].as_long())
        })

        # Add Kevin's meeting
        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": to_time(m[kevin_start].as_long()),
            "end_time": to_time(m[kevin_end].as_long())
        })

        # Add Joseph's meeting
        itinerary.append({
            "action": "meet",
            "person": "Joseph",
            "start_time": to_time(m[joseph_start].as_long()),
            "end_time": to_time(m[joseph_end].as_long())
        })

        # Add Thomas's meeting
        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": to_time(m[thomas_start].as_long()),
            "end_time": to_time(m[thomas_end].as_long())
        })

        return {"itinerary": itinerary}
    else:
        # If the first order fails, try another order: Kevin -> Kimberly -> Joseph -> Thomas
        s.reset()
        s = Solver()

        # Re-add all constraints
        s.add(kevin_start >= 495, kevin_end <= 1290)
        s.add(kevin_end - kevin_start >= 75)
        s.add(kimberly_start >= 525, kimberly_end <= 750)
        s.add(kimberly_end - kimberly_start >= 30)
        s.add(joseph_start >= 1170, joseph_end <= 1185)
        s.add(joseph_end - joseph_start >= 45)
        s.add(thomas_start >= 1200, thomas_end <= 1305)
        s.add(thomas_end - thomas_start >= 45)

        # Travel from Sunset to Alamo Square: 17 minutes
        s.add(kevin_start >= 540 + 17)

        # After Kevin, travel to Russian Hill: 13 minutes
        s.add(kimberly_start >= kevin_end + 13)

        # After Kimberly, travel to Presidio: 14 minutes
        s.add(joseph_start >= kimberly_end + 14)

        # After Joseph, travel to Financial District: 22 minutes
        s.add(thomas_start >= joseph_end + 22)

        if s.check() == sat:
            m = s.model()
            itinerary = []

            def to_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"

            itinerary.append({
                "action": "meet",
                "person": "Kevin",
                "start_time": to_time(m[kevin_start].as_long()),
                "end_time": to_time(m[kevin_end].as_long())
            })

            itinerary.append({
                "action": "meet",
                "person": "Kimberly",
                "start_time": to_time(m[kimberly_start].as_long()),
                "end_time": to_time(m[kimberly_end].as_long())
            })

            itinerary.append({
                "action": "meet",
                "person": "Joseph",
                "start_time": to_time(m[joseph_start].as_long()),
                "end_time": to_time(m[joseph_end].as_long())
            })

            itinerary.append({
                "action": "meet",
                "person": "Thomas",
                "start_time": to_time(m[thomas_start].as_long()),
                "end_time": to_time(m[thomas_end].as_long())
            })

            return {"itinerary": itinerary}
        else:
            return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))