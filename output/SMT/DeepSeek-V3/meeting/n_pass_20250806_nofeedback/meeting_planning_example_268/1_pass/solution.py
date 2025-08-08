from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Timothy at Alamo Square
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    # Meeting with Mark at Presidio
    mark_start = Int('mark_start')
    mark_end = Int('mark_end')
    # Meeting with Joseph at Russian Hill
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Constraints for Timothy: available 12:00 (720) to 16:15 (975), duration >= 105
    s.add(timothy_start >= 720)
    s.add(timothy_end <= 975)
    s.add(timothy_end - timothy_start >= 105)

    # Constraints for Mark: available 18:45 (1125) to 21:00 (1260), duration >= 60
    s.add(mark_start >= 1125)
    s.add(mark_end <= 1260)
    s.add(mark_end - mark_start >= 60)

    # Constraints for Joseph: available 16:45 (1005) to 21:30 (1290), duration >= 60
    s.add(joseph_start >= 1005)
    s.add(joseph_end <= 1290)
    s.add(joseph_end - joseph_start >= 60)

    # Define travel times (in minutes)
    # From Golden Gate Park (starting point at 9:00 AM, 540 minutes)
    # Assume the first activity is to go to Timothy at Alamo Square
    # Travel from Golden Gate Park to Alamo Square: 10 minutes
    # So arrival at Alamo Square at 540 + 10 = 550 (9:10 AM)
    # But Timothy is available only from 12:00 PM (720). So we have to wait until 720.
    # So the earliest we can start meeting Timothy is 720.
    # So the time before meeting Timothy is from 540 to 720 (180 minutes), during which we can travel (10 minutes) and wait (170 minutes).
    # Alternatively, we can do other things before meeting Timothy, but since no other friends are available before 12:00 PM, we can only wait.

    # Now, the order of meetings could be Timothy -> Joseph -> Mark, or Timothy -> Mark -> Joseph, etc.
    # Let's model the possible sequences.

    # We need to choose between possible sequences of meetings and ensure travel times are respected.

    # Let's assume the order is Timothy -> Joseph -> Mark.

    # Then:
    # 1. Start at Golden Gate Park at 540.
    # 2. Travel to Alamo Square: 10 minutes, arrive at 550.
    # 3. Wait until 720 to meet Timothy.
    # 4. Meet Timothy from 720 to (720 + 105) = 825 (13:45 PM).
    # 5. Travel from Alamo Square to Russian Hill: 13 minutes, arrive at 825 + 13 = 838.
    # 6. Joseph is available from 1005, so wait until 1005.
    # 7. Meet Joseph from 1005 to 1005 + 60 = 1065.
    # 8. Travel from Russian Hill to Presidio: 14 minutes, arrive at 1065 + 14 = 1079.
    # 9. Mark is available from 1125, so wait until 1125.
    # 10. Meet Mark from 1125 to 1125 + 60 = 1185.

    # This sequence fits all constraints.

    # Alternatively, let's check if other sequences are possible.

    # Another possible sequence is Timothy -> Mark -> Joseph.
    # 1. Start at Golden Gate Park at 540.
    # 2. Travel to Alamo Square: 10 minutes, arrive at 550.
    # 3. Wait until 720 to meet Timothy.
    # 4. Meet Timothy from 720 to 825.
    # 5. Travel from Alamo Square to Presidio: 18 minutes, arrive at 825 + 18 = 843.
    # 6. Mark is available from 1125, so wait until 1125 (long wait).
    # 7. Meet Mark from 1125 to 1185.
    # 8. Travel from Presidio to Russian Hill: 14 minutes, arrive at 1185 + 14 = 1199.
    # 9. Joseph's availability ends at 1290, so meet from 1199 to 1199 + 60 = 1259, which is within his availability.
    # This also works but has a long wait time between Timothy and Mark.

    # The first sequence seems more efficient with less waiting time.

    # So, let's proceed with the first sequence: Timothy -> Joseph -> Mark.

    # Now, let's model this in Z3.

    # We can define the order as a fixed sequence and add constraints accordingly.

    # Sequence: Timothy (Alamo) -> Joseph (Russian) -> Mark (Presidio)

    # Start at Golden Gate Park at 540.
    # Travel to Alamo Square: 10 minutes, arrive at 550.
    s.add(timothy_start >= 720)  # must wait until 720

    # Meet Timothy from 720 to 825.
    s.add(timothy_end == timothy_start + 105)
    s.add(timothy_start == 720)  # earliest possible

    # Travel from Alamo Square to Russian Hill: 13 minutes, arrive at 825 + 13 = 838.
    # Joseph is available from 1005, so wait until 1005.
    s.add(joseph_start >= 1005)
    s.add(joseph_start >= timothy_end + 13)  # travel time

    # Meet Joseph from 1005 to 1065.
    s.add(joseph_end == joseph_start + 60)
    s.add(joseph_start == 1005)  # earliest possible

    # Travel from Russian Hill to Presidio: 14 minutes, arrive at 1065 + 14 = 1079.
    # Mark is available from 1125, so wait until 1125.
    s.add(mark_start >= 1125)
    s.add(mark_start >= joseph_end + 14)  # travel time

    # Meet Mark from 1125 to 1185.
    s.add(mark_end == mark_start + 60)
    s.add(mark_start == 1125)  # earliest possible

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            total_minutes = minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": minutes_to_time(m[timothy_start].as_long()), "end_time": minutes_to_time(m[timothy_end].as_long())},
            {"action": "meet", "person": "Joseph", "start_time": minutes_to_time(m[joseph_start].as_long()), "end_time": minutes_to_time(m[joseph_end].as_long())},
            {"action": "meet", "person": "Mark", "start_time": minutes_to_time(m[mark_start].as_long()), "end_time": minutes_to_time(m[mark_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Execute and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))