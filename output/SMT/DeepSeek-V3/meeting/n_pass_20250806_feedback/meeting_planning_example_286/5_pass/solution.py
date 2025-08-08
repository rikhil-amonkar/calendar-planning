from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations as constants
    UNION_SQUARE = 0
    MISSION_DISTRICT = 1
    BAYVIEW = 2
    SUNSET_DISTRICT = 3

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    rebecca_start = Int('rebecca_start')
    rebecca_end = Int('rebecca_end')
    karen_start = Int('karen_start')
    karen_end = Int('karen_end')
    carol_start = Int('carol_start')
    carol_end = Int('carol_end')

    # Travel times in minutes
    travel = {
        (UNION_SQUARE, MISSION_DISTRICT): 14,
        (UNION_SQUARE, BAYVIEW): 15,
        (UNION_SQUARE, SUNSET_DISTRICT): 26,
        (MISSION_DISTRICT, UNION_SQUARE): 15,
        (MISSION_DISTRICT, BAYVIEW): 15,
        (MISSION_DISTRICT, SUNSET_DISTRICT): 24,
        (BAYVIEW, UNION_SQUARE): 17,
        (BAYVIEW, MISSION_DISTRICT): 13,
        (BAYVIEW, SUNSET_DISTRICT): 23,
        (SUNSET_DISTRICT, UNION_SQUARE): 30,
        (SUNSET_DISTRICT, MISSION_DISTRICT): 24,
        (SUNSET_DISTRICT, BAYVIEW): 22,
    }

    # Convert availability windows to minutes since 9:00 AM
    rebecca_min_start = 690  # 11:30 AM (11*60 + 30)
    rebecca_max_end = 1215   # 8:15 PM (20*60 + 15)
    karen_min_start = 765    # 12:45 PM
    karen_max_end = 900      # 3:00 PM
    carol_min_start = 615    # 10:15 AM
    carol_max_end = 705      # 11:45 AM

    # Meeting durations in minutes
    rebecca_duration = 120
    karen_duration = 120
    carol_duration = 30

    # Constraints for each meeting
    # Rebecca must be between 11:30 AM and 8:15 PM
    s.add(rebecca_start >= rebecca_min_start)
    s.add(rebecca_end <= rebecca_max_end)
    s.add(rebecca_end == rebecca_start + rebecca_duration)

    # Karen must be between 12:45 PM and 3:00 PM
    s.add(karen_start >= karen_min_start)
    s.add(karen_end <= karen_max_end)
    s.add(karen_end == karen_start + karen_duration)

    # Carol must be between 10:15 AM and 11:45 AM
    s.add(carol_start >= carol_min_start)
    s.add(carol_end <= carol_max_end)
    s.add(carol_end == carol_start + carol_duration)

    # Define possible meeting orders
    orders = [[0, 1, 2], [0, 2, 1], [1, 0, 2], 
              [1, 2, 0], [2, 0, 1], [2, 1, 0]]  # 0=Carol, 1=Karen, 2=Rebecca

    # Try each possible order until we find a valid schedule
    for order in orders:
        s.push()
        
        # Assign meeting times based on order
        meetings = []
        prev_location = UNION_SQUARE
        prev_end = 0  # Start at 9:00 AM (0 minutes)
        
        for i in order:
            if i == 0:  # Carol
                s.add(carol_start >= prev_end + travel[(prev_location, SUNSET_DISTRICT)])
                meetings.append(("Carol", carol_start, carol_end, SUNSET_DISTRICT))
                prev_end = carol_end
                prev_location = SUNSET_DISTRICT
            elif i == 1:  # Karen
                s.add(karen_start >= prev_end + travel[(prev_location, BAYVIEW)])
                meetings.append(("Karen", karen_start, karen_end, BAYVIEW))
                prev_end = karen_end
                prev_location = BAYVIEW
            else:  # Rebecca
                s.add(rebecca_start >= prev_end + travel[(prev_location, MISSION_DISTRICT)])
                meetings.append(("Rebecca", rebecca_start, rebecca_end, MISSION_DISTRICT))
                prev_end = rebecca_end
                prev_location = MISSION_DISTRICT

        # Check if this order works
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for person, start, end, loc in meetings:
                # Convert minutes to HH:MM format
                start_time = (540 + m[start].as_long()) % 1440
                end_time = (540 + m[end].as_long()) % 1440
                start_str = f"{start_time//60:02d}:{start_time%60:02d}"
                end_str = f"{end_time//60:02d}:{end_time%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_str,
                    "end_time": end_str
                })
            return {"itinerary": itinerary}
        s.pop()
    
    return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)