from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times
    # Carol at Sunset District (10:15AM - 11:45AM), min 30 mins
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')

    # Rebecca at Mission District (11:30AM - 8:15PM), min 120 mins
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')

    # Karen at Bayview (12:45PM - 3:00PM), min 120 mins
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')

    # Convert all times to minutes since 9:00AM (540 minutes since midnight)
    # Carol's availability: 10:15AM (615) to 11:45AM (705)
    carol_available_start = 615 - 540  # 75
    carol_available_end = 705 - 540    # 165

    # Rebecca's availability: 11:30AM (690) to 8:15PM (1215)
    rebecca_available_start = 690 - 540  # 150
    rebecca_available_end = 1215 - 540   # 675

    # Karen's availability: 12:45PM (765) to 3:00PM (900)
    karen_available_start = 765 - 540    # 225
    karen_available_end = 900 - 540      # 360

    # Travel times (in minutes)
    travel_union_sunset = 26
    travel_sunset_mission = 24
    travel_mission_bayview = 15
    travel_bayview_mission = 13
    travel_mission_union = 15

    # Constraints for Carol (Sunset District)
    s.add(carol_start >= carol_available_start)
    s.add(carol_end <= carol_available_end)
    s.add(carol_end - carol_start >= 30)  # min 30 mins

    # Constraints for Rebecca (Mission District)
    s.add(rebecca_start >= rebecca_available_start)
    s.add(rebecca_end <= rebecca_available_end)
    s.add(rebecca_end - rebecca_start >= 120)  # min 120 mins

    # Constraints for Karen (Bayview)
    s.add(karen_start >= karen_available_start)
    s.add(karen_end <= karen_available_end)
    s.add(karen_end - karen_start >= 120)  # min 120 mins

    # Initial location: Union Square at time 0 (9:00AM)
    # Carol is first, so travel from Union Square to Sunset District (26 mins)
    s.add(carol_start >= 0 + travel_union_sunset)

    # After Carol, travel to Mission District to meet Rebecca (24 mins)
    s.add(rebecca_start >= carol_end + travel_sunset_mission)

    # After Rebecca, travel to Bayview to meet Karen (15 mins)
    s.add(karen_start >= rebecca_end + travel_mission_bayview)

    # Alternatively, if we meet Karen before Rebecca:
    # This is another possible schedule, but we'll let Z3 find the best order

    # Ensure no overlapping meetings
    s.add(Or(
        # Order: Carol -> Rebecca -> Karen
        And(
            carol_end <= rebecca_start,
            rebecca_end <= karen_start
        ),
        # Order: Carol -> Karen -> Rebecca
        And(
            carol_end <= karen_start,
            karen_end <= rebecca_start
        )
    ))

    # Also, if we don't meet Carol first, but let's assume we do for simplicity

    # Maximize total time with friends (sum of all meeting durations)
    total_time = (carol_end - carol_start) + (rebecca_end - rebecca_start) + (karen_end - karen_start)
    s.maximize(total_time)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Convert back to hours and minutes
        def to_time(minutes):
            total = 540 + minutes  # 9:00AM is 540 minutes
            h = total // 60
            m = total % 60
            return f"{h}:{m:02d}"

        carol_s = m.eval(carol_start).as_long()
        carol_e = m.eval(carol_end).as_long()
        rebecca_s = m.eval(rebecca_start).as_long()
        rebecca_e = m.eval(rebecca_end).as_long()
        karen_s = m.eval(karen_start).as_long()
        karen_e = m.eval(karen_end).as_long()

        print("SOLUTION:")
        print(f"Meet Carol at Sunset District from {to_time(carol_s)} to {to_time(carol_e)}")
        print(f"Meet Rebecca at Mission District from {to_time(rebecca_s)} to {to_time(rebecca_e)}")
        print(f"Meet Karen at Bayview from {to_time(karen_s)} to {to_time(karen_e)}")
        print(f"Total time with friends: {m.eval(total_time).as_long()} minutes")
    else:
        print("No valid schedule found.")

solve_scheduling()