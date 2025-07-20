from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables in minutes since 9:00 AM (540 minutes)
    # Meeting with Carol at Sunset District (10:15-11:45, min 30 mins)
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')

    # Meeting with Rebecca at Mission District (11:30-20:15, min 120 mins)
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Meeting with Karen at Bayview (12:45-15:00, min 120 mins)
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Convert all times to minutes since 9:00 AM (540)
    # Carol's window: 10:15 (75 mins) to 11:45 (165 mins)
    carol_window_start = 75  # 10:15 - 9:00 = 1:15 = 75 mins
    carol_window_end = 165   # 11:45 - 9:00 = 2:45 = 165 mins

    # Rebecca's window: 11:30 (150 mins) to 20:15 (675 mins)
    rebecca_window_start = 150  # 11:30 - 9:00 = 2:30 = 150 mins
    rebecca_window_end = 675    # 20:15 - 9:00 = 11:15 = 675 mins

    # Karen's window: 12:45 (225 mins) to 15:00 (360 mins)
    karen_window_start = 225    # 12:45 - 9:00 = 3:45 = 225 mins
    karen_window_end = 360      # 15:00 - 9:00 = 6:00 = 360 mins

    # Add constraints for Carol
    s.add(carol_start >= carol_window_start)
    s.add(carol_end <= carol_window_end)
    s.add(carol_end - carol_start >= 30)  # min 30 mins

    # Add constraints for Rebecca
    s.add(rebecca_start >= rebecca_window_start)
    s.add(rebecca_end <= rebecca_window_end)
    s.add(rebecca_end - rebecca_start >= 120)  # min 120 mins

    # Add constraints for Karen
    s.add(karen_start >= karen_window_start)
    s.add(karen_end <= karen_window_end)
    s.add(karen_end - karen_start >= 120)  # min 120 mins

    # Travel times from Union Square to Sunset District (26 mins)
    # So Carol's meeting must start at least 26 mins after 9:00 AM (i.e., carol_start >= 26)
    s.add(carol_start >= 26)

    # After Carol, travel to Mission District (Sunset to Mission: 24 mins)
    # So rebecca_start >= carol_end + 24
    s.add(rebecca_start >= carol_end + 24)

    # After Rebecca, travel to Bayview (Mission to Bayview: 15 mins)
    # So karen_start >= rebecca_end + 15
    s.add(karen_start >= rebecca_end + 15)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def to_time(minutes):
            total_mins = 540 + minutes  # 9:00 AM + minutes
            h = total_mins // 60
            m = total_mins % 60
            return f"{h:02d}:{m:02d}"

        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()
        karen_s = m.eval(karen_start).as_long()
        karen_e = m.eval(karen_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": to_time(carol_s), "end_time": to_time(carol_e)},
            {"action": "meet", "person": "Rebecca", "start_time": to_time(rebecca_s), "end_time": to_time(rebecca_e)},
            {"action": "meet", "person": "Karen", "start_time": to_time(karen_s), "end_time": to_time(karen_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute and print the solution
solution = solve_scheduling()
print(solution)