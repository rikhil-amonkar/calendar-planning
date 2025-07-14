from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Variables for arrival and departure times at each location (in minutes since 9:00AM)
    # Union Square is the starting point at time 0 (9:00AM)
    arrival_mission = Int('arrival_mission')
    departure_mission = Int('departure_mission')
    arrival_bayview = Int('arrival_bayview')
    departure_bayview = Int('departure_bayview')
    arrival_sunset = Int('arrival_sunset')
    departure_sunset = Int('departure_sunset')

    # Travel times (in minutes)
    travel_union_to_mission = 14
    travel_union_to_bayview = 15
    travel_union_to_sunset = 26
    travel_mission_to_union = 15
    travel_mission_to_bayview = 15
    travel_mission_to_sunset = 24
    travel_bayview_to_union = 17
    travel_bayview_to_mission = 13
    travel_bayview_to_sunset = 23
    travel_sunset_to_union = 30
    travel_sunset_to_mission = 24
    travel_sunset_to_bayview = 22

    # Friend availability windows (in minutes since 9:00AM)
    rebecca_start = 150  # 11:30AM is 150 minutes after 9:00AM
    rebecca_end = 555    # 8:15PM is 555 minutes after 9:00AM
    karen_start = 225    # 12:45PM is 225 minutes after 9:00AM
    karen_end = 360      # 3:00PM is 360 minutes after 9:00AM
    carol_start = 75     # 10:15AM is 75 minutes after 9:00AM
    carol_end = 165      # 11:45AM is 165 minutes after 9:00AM

    # Minimum meeting durations (in minutes)
    min_rebecca = 120
    min_karen = 120
    min_carol = 30

    # Constraints for meeting Rebecca in Mission District
    s.add(arrival_mission >= 0)
    s.add(departure_mission >= arrival_mission)
    s.add(arrival_mission >= rebecca_start)
    s.add(departure_mission <= rebecca_end)
    s.add(departure_mission - arrival_mission >= min_rebecca)

    # Constraints for meeting Karen in Bayview
    s.add(arrival_bayview >= 0)
    s.add(departure_bayview >= arrival_bayview)
    s.add(arrival_bayview >= karen_start)
    s.add(departure_bayview <= karen_end)
    s.add(departure_bayview - arrival_bayview >= min_karen)

    # Constraints for meeting Carol in Sunset District
    s.add(arrival_sunset >= 0)
    s.add(departure_sunset >= arrival_sunset)
    s.add(arrival_sunset >= carol_start)
    s.add(departure_sunset <= carol_end)
    s.add(departure_sunset - arrival_sunset >= min_carol)

    # Travel constraints (sequence of visits)
    # Assume the order is Union -> Sunset -> Mission -> Bayview
    # This is one possible order; we may need to try others if this is unsatisfiable
    s.add(arrival_sunset >= travel_union_to_sunset)  # Travel from Union to Sunset
    s.add(arrival_mission >= departure_sunset + travel_sunset_to_mission)  # Sunset to Mission
    s.add(arrival_bayview >= departure_mission + travel_mission_to_bayview)  # Mission to Bayview

    # Ensure no overlapping meetings
    s.add(departure_sunset <= arrival_mission - travel_sunset_to_mission)
    s.add(departure_mission <= arrival_bayview - travel_mission_to_bayview)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes back to time format
        def minutes_to_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}AM" if hours < 12 else f"{hours-12}:{mins:02d}PM" if hours < 24 else f"{hours-12}:{mins:02d}AM"

        print("SOLUTION:")
        print(f"Meet Carol at Sunset District from {minutes_to_time(m[arrival_sunset].as_long())} to {minutes_to_time(m[departure_sunset].as_long())}")
        print(f"Meet Rebecca at Mission District from {minutes_to_time(m[arrival_mission].as_long())} to {minutes_to_time(m[departure_mission].as_long())}")
        print(f"Meet Karen at Bayview from {minutes_to_time(m[arrival_bayview].as_long())} to {minutes_to_time(m[departure_bayview].as_long())}")
    else:
        print("No valid schedule found.")

solve_scheduling()