from z3 import *
import datetime

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (540 minutes since midnight)
    # Meeting start and end times
    meet_barbara_start = Int('meet_barbara_start')
    meet_barbara_end = Int('meet_barbara_end')
    meet_betty_start = Int('meet_betty_start')
    meet_betty_end = Int('meet_betty_end')
    meet_david_start = Int('meet_david_start')
    meet_david_end = Int('meet_david_end')

    # Travel times
    # From Embarcadero (starting point) to Fisherman's Wharf: 6 minutes
    # Possible travels:
    # After meeting Barbara, can go to Presidio (Fisherman's Wharf to Presidio: 17) or Richmond (18)
    # After meeting Betty, can go to Richmond (7) or back to Embarcadero (20) or Fisherman's Wharf (19)
    # After meeting David, can go to Presidio (7) or Fisherman's Wharf (18) or Embarcadero (19)

    # Constraints for Barbara (Fisherman's Wharf: 9:15 AM to 8:15 PM)
    barbara_window_start = 15  # 9:15 AM is 540 + 15 = 555 minutes since midnight
    barbara_window_end = 1215  # 8:15 PM is 20*60 +15 = 1215 minutes since midnight
    s.add(meet_barbara_start >= 540 + 15)  # can't start before 9:15 AM
    s.add(meet_barbara_end <= barbara_window_end)
    s.add(meet_barbara_end - meet_barbara_start >= 120)  # at least 120 minutes

    # Constraints for Betty (Presidio: 10:15 AM to 9:30 PM)
    betty_window_start = 615  # 10:15 AM is 600 +15 =615
    betty_window_end = 1290  # 9:30 PM is 21*60 +30 =1290
    s.add(meet_betty_start >= betty_window_start)
    s.add(meet_betty_end <= betty_window_end)
    s.add(meet_betty_end - meet_betty_start >= 45)

    # Constraints for David (Richmond District: 1:00 PM to 8:15 PM)
    david_window_start = 780  # 1:00 PM is 13*60 =780
    david_window_end = 1215  # 8:15 PM is 20*60 +15 =1215
    s.add(meet_david_start >= david_window_start)
    s.add(meet_david_end <= david_window_end)
    s.add(meet_david_end - meet_david_start >= 90)

    # Starting at Embarcadero at 9:00 AM (540 minutes since midnight)
    # Possible first action: go to Fisherman's Wharf (6 minutes), arrive at 9:06 AM (546)
    # Then meet Barbara starting at earliest 9:15 AM (555)
    # So possible to start meeting Barbara at 555 (9:15 AM), end at 555 +120 = 675 (11:15 AM)

    # Alternatively, go to Presidio (20 minutes), arrive at 9:20 AM (560)
    # Betty is available from 10:15 AM (615), so wait until then.

    # Or go to Richmond (21 minutes), arrive at 9:21 AM (561)
    # David is available from 1:00 PM (780), so this is not optimal for first meeting.

    # So the first meeting should be either Barbara or Betty.

    # Let's model the possible sequences.

    # Sequence 1: Barbara first, then Betty, then David
    # Barbara: start at 555 (9:15 AM), end at 675 (11:15 AM)
    # Travel from Fisherman's Wharf to Presidio: 17 minutes
    # Arrive at Presidio at 675 +17 = 692 (11:32 AM)
    # Betty available from 10:15 AM (615), so can start at 692 (11:32 AM)
    # Meet Betty until 692 +45 = 737 (12:17 PM)
    # Travel from Presidio to Richmond: 7 minutes
    # Arrive at Richmond at 737 +7 = 744 (12:24 PM)
    # David available from 1:00 PM (780), so wait until then.
    # Meet David from 780 to 780 +90 = 870 (2:30 PM)

    # This sequence fits all constraints.

    # Alternatively, other sequences may not fit or may have overlaps.

    # Let's encode this sequence as constraints.

    # Barbara first
    s.add(meet_barbara_start == 555)
    s.add(meet_barbara_end == 675)

    # Travel to Presidio: 17 minutes
    arrive_presidio = meet_barbara_end + 17
    s.add(meet_betty_start >= arrive_presidio)
    s.add(meet_betty_start >= 615)  # Betty's window starts at 615

    # Meet Betty
    s.add(meet_betty_end == meet_betty_start + 45)

    # Travel to Richmond: 7 minutes
    arrive_richmond = meet_betty_end + 7
    s.add(meet_david_start >= arrive_richmond)
    s.add(meet_david_start >= 780)  # David's window starts at 780

    # Meet David
    s.add(meet_david_end == meet_david_start + 90)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        barbara_start = m.eval(meet_barbara_start).as_long()
        barbara_end = m.eval(meet_barbara_end).as_long()
        betty_start = m.eval(meet_betty_start).as_long()
        betty_end = m.eval(meet_betty_end).as_long()
        david_start = m.eval(meet_david_start).as_long()
        david_end = m.eval(meet_david_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_start), "end_time": minutes_to_time(barbara_end)},
            {"action": "meet", "person": "Betty", "start_time": minutes_to_time(betty_start), "end_time": minutes_to_time(betty_end)},
            {"action": "meet", "person": "David", "start_time": minutes_to_time(david_start), "end_time": minutes_to_time(david_end)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Run the solver and print the result
result = solve_scheduling()
print(result)