from z3 import *
import datetime

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define time variables for each meeting in minutes since 9:00 AM (540 minutes)
    # Meeting with Mary in Richmond District
    mary_start = Int('mary_start')
    mary_end = Int('mary_end')

    # Meeting with Sarah in Fisherman's Wharf
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')

    # Meeting with Thomas in Bayview
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Meeting with Helen in Mission District
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')

    # Convert all time windows to minutes since 9:00 AM (540)
    # Sarah: 2:45 PM (14:45) to 5:30 PM (17:30) -> 885 to 1050
    sarah_window_start = 14 * 60 + 45 - (9 * 60)  # 885 - 540 = 345
    sarah_window_end = 17 * 60 + 30 - (9 * 60)    # 1050 - 540 = 510
    sarah_min_duration = 105

    # Mary: 1:00 PM (13:00) to 7:15 PM (19:15) -> 780 to 1155 -> 240 to 615
    mary_window_start = 13 * 60 + 0 - (9 * 60)    # 780 - 540 = 240
    mary_window_end = 19 * 60 + 15 - (9 * 60)     # 1155 - 540 = 615
    mary_min_duration = 75

    # Helen: 9:45 PM (21:45) to 10:30 PM (22:30) -> 1305 to 1350 -> 765 to 810
    helen_window_start = 21 * 60 + 45 - (9 * 60)  # 1305 - 540 = 765
    helen_window_end = 22 * 60 + 30 - (9 * 60)    # 1350 - 540 = 810
    helen_min_duration = 30

    # Thomas: 3:15 PM (15:15) to 6:45 PM (18:45) -> 915 to 1125 -> 375 to 585
    thomas_window_start = 15 * 60 + 15 - (9 * 60) # 915 - 540 = 375
    thomas_window_end = 18 * 60 + 45 - (9 * 60)   # 1125 - 540 = 585
    thomas_min_duration = 120

    # Initial location: Haight-Ashbury at time 0 (9:00 AM)

    # Constraints for each meeting:
    # Mary in Richmond
    s.add(mary_start >= 0)  # Can start any time after 9:00 AM (time 0)
    s.add(mary_start >= mary_window_start)
    s.add(mary_end <= mary_window_end)
    s.add(mary_end == mary_start + mary_min_duration)

    # Sarah in Fisherman's Wharf
    s.add(sarah_start >= sarah_window_start)
    s.add(sarah_end <= sarah_window_end)
    s.add(sarah_end == sarah_start + sarah_min_duration)

    # Thomas in Bayview
    s.add(thomas_start >= thomas_window_start)
    s.add(thomas_end <= thomas_window_end)
    s.add(thomas_end == thomas_start + thomas_min_duration)

    # Helen in Mission District
    s.add(helen_start >= helen_window_start)
    s.add(helen_end <= helen_window_end)
    s.add(helen_end == helen_start + helen_min_duration)

    # Order of meetings and travel times:
    # We need to sequence the meetings such that travel times are respected.
    # We'll assume the order is Mary -> Sarah -> Thomas -> Helen.
    # This is one possible order; others may be possible, but this seems plausible given time windows.

    # Travel times:
    # From Haight-Ashbury to Richmond: 10 minutes.
    # So Mary's start >= 10.
    s.add(mary_start >= 10)

    # From Richmond to Fisherman's Wharf: 18 minutes.
    # So Sarah's start >= mary_end + 18.
    s.add(sarah_start >= mary_end + 18)

    # From Fisherman's Wharf to Bayview: 26 minutes.
    # So Thomas's start >= sarah_end + 26.
    s.add(thomas_start >= sarah_end + 26)

    # From Bayview to Mission District: 13 minutes.
    # So Helen's start >= thomas_end + 13.
    s.add(helen_start >= thomas_end + 13)

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract times
        mary_s = model[mary_start].as_long()
        mary_e = model[mary_end].as_long()
        sarah_s = model[sarah_start].as_long()
        sarah_e = model[sarah_end].as_long()
        thomas_s = model[thomas_start].as_long()
        thomas_e = model[thomas_end].as_long()
        helen_s = model[helen_start].as_long()
        helen_e = model[helen_end].as_long()

        # Convert times back to HH:MM format from minutes since 9:00 AM
        def to_time_str(minutes):
            time = datetime.datetime.strptime("09:00", "%H:%M") + datetime.timedelta(minutes=minutes)
            return time.strftime("%H:%M")

        itinerary = [
            {"action": "meet", "person": "Mary", "start_time": to_time_str(mary_s), "end_time": to_time_str(mary_e)},
            {"action": "meet", "person": "Sarah", "start_time": to_time_str(sarah_s), "end_time": to_time_str(sarah_e)},
            {"action": "meet", "person": "Thomas", "start_time": to_time_str(thomas_s), "end_time": to_time_str(thomas_e)},
            {"action": "meet", "person": "Helen", "start_time": to_time_str(helen_s), "end_time": to_time_str(helen_e)}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(result)