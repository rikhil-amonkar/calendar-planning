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
    # Convert all times to minutes from 9:00 AM (540 minutes in 24-hour format)
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
    # Rebecca: 11:30 AM to 8:15 PM (11:30 = 11*60 + 30 = 690, 8:15 PM = 20*60 + 15 = 1215)
    rebecca_min_start = 690  # 11:30 AM
    rebecca_max_end = 1215   # 8:15 PM

    # Karen: 12:45 PM to 3:00 PM (12:45 = 12*60 + 45 = 765, 3:00 PM = 15*60 = 900)
    karen_min_start = 765
    karen_max_end = 900

    # Carol: 10:15 AM to 11:45 AM (10:15 = 10*60 + 15 = 615, 11:45 AM = 11*60 + 45 = 705)
    carol_min_start = 615
    carol_max_end = 705

    # Meeting durations in minutes
    rebecca_duration = 120
    karen_duration = 120
    carol_duration = 30

    # Constraints for each meeting
    # Rebecca
    s.add(rebecca_start >= rebecca_min_start)
    s.add(rebecca_end <= rebecca_max_end)
    s.add(rebecca_end == rebecca_start + rebecca_duration)

    # Karen
    s.add(karen_start >= karen_min_start)
    s.add(karen_end <= karen_max_end)
    s.add(karen_end == karen_start + karen_duration)

    # Carol
    s.add(carol_start >= carol_min_start)
    s.add(carol_end <= carol_max_end)
    s.add(carol_end == carol_start + carol_duration)

    # Define the order of meetings
    order = [Int(f'order_{i}') for i in range(3)]
    s.add(Distinct(order[0], order[1], order[2]))
    for i in range(3):
        s.add(order[i] >= 0, order[i] <= 2)

    # Variables to represent the start and end times of each meeting in the sequence
    seq_start = [Int(f'seq_start_{i}') for i in range(3)]
    seq_end = [Int(f'seq_end_{i}') for i in range(3)]
    seq_location = [Int(f'seq_location_{i}') for i in range(3)]

    # Initial state: at Union Square at time 0
    prev_location = UNION_SQUARE
    prev_time = 0

    # Constraints for each position in the sequence
    for i in range(3):
        # The i-th meeting in the sequence is determined by order[i]
        # meeting 0: Carol (Sunset District, location 3)
        # meeting 1: Karen (Bayview, location 2)
        # meeting 2: Rebecca (Mission District, location 1)
        s.add(Or(
            And(order[i] == 0, seq_location[i] == SUNSET_DISTRICT, seq_start[i] == carol_start, seq_end[i] == carol_end),
            And(order[i] == 1, seq_location[i] == BAYVIEW, seq_start[i] == karen_start, seq_end[i] == karen_end),
            And(order[i] == 2, seq_location[i] == MISSION_DISTRICT, seq_start[i] == rebecca_start, seq_end[i] == rebecca_end)
        ))

        # Travel time from previous location to current location
        if i == 0:
            # From Union Square (0) to seq_location[i]
            s.add(Or(
                And(seq_location[i] == MISSION_DISTRICT, seq_start[i] >= prev_time + travel[(UNION_SQUARE, MISSION_DISTRICT)]),
                And(seq_location[i] == BAYVIEW, seq_start[i] >= prev_time + travel[(UNION_SQUARE, BAYVIEW)]),
                And(seq_location[i] == SUNSET_DISTRICT, seq_start[i] >= prev_time + travel[(UNION_SQUARE, SUNSET_DISTRICT)])
            ))
        else:
            # From seq_location[i-1] to seq_location[i]
            s.add(Or(
                And(seq_location[i-1] == UNION_SQUARE, seq_location[i] == MISSION_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(UNION_SQUARE, MISSION_DISTRICT)]),
                And(seq_location[i-1] == UNION_SQUARE, seq_location[i] == BAYVIEW, seq_start[i] >= seq_end[i-1] + travel[(UNION_SQUARE, BAYVIEW)]),
                And(seq_location[i-1] == UNION_SQUARE, seq_location[i] == SUNSET_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(UNION_SQUARE, SUNSET_DISTRICT)]),
                And(seq_location[i-1] == MISSION_DISTRICT, seq_location[i] == UNION_SQUARE, seq_start[i] >= seq_end[i-1] + travel[(MISSION_DISTRICT, UNION_SQUARE)]),
                And(seq_location[i-1] == MISSION_DISTRICT, seq_location[i] == BAYVIEW, seq_start[i] >= seq_end[i-1] + travel[(MISSION_DISTRICT, BAYVIEW)]),
                And(seq_location[i-1] == MISSION_DISTRICT, seq_location[i] == SUNSET_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(MISSION_DISTRICT, SUNSET_DISTRICT)]),
                And(seq_location[i-1] == BAYVIEW, seq_location[i] == UNION_SQUARE, seq_start[i] >= seq_end[i-1] + travel[(BAYVIEW, UNION_SQUARE)]),
                And(seq_location[i-1] == BAYVIEW, seq_location[i] == MISSION_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(BAYVIEW, MISSION_DISTRICT)]),
                And(seq_location[i-1] == BAYVIEW, seq_location[i] == SUNSET_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(BAYVIEW, SUNSET_DISTRICT)]),
                And(seq_location[i-1] == SUNSET_DISTRICT, seq_location[i] == UNION_SQUARE, seq_start[i] >= seq_end[i-1] + travel[(SUNSET_DISTRICT, UNION_SQUARE)]),
                And(seq_location[i-1] == SUNSET_DISTRICT, seq_location[i] == MISSION_DISTRICT, seq_start[i] >= seq_end[i-1] + travel[(SUNSET_DISTRICT, MISSION_DISTRICT)]),
                And(seq_location[i-1] == SUNSET_DISTRICT, seq_location[i] == BAYVIEW, seq_start[i] >= seq_end[i-1] + travel[(SUNSET_DISTRICT, BAYVIEW)])
            ))

    # Ensure all meeting times are within the valid 24-hour format (0 to 1439 minutes)
    s.add(rebecca_start >= 0, rebecca_end <= 1439)
    s.add(karen_start >= 0, karen_end <= 1439)
    s.add(carol_start >= 0, carol_end <= 1439)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the order of meetings
        meeting_order = []
        for i in range(3):
            meeting_order.append(m[order[i]].as_long())
        # Create a list of meetings in the order they are scheduled
        meetings = []
        for i in range(3):
            if meeting_order[i] == 0:
                meetings.append(("Carol", m[carol_start].as_long(), m[carol_end].as_long(), SUNSET_DISTRICT))
            elif meeting_order[i] == 1:
                meetings.append(("Karen", m[karen_start].as_long(), m[karen_end].as_long(), BAYVIEW))
            elif meeting_order[i] == 2:
                meetings.append(("Rebecca", m[rebecca_start].as_long(), m[rebecca_end].as_long(), MISSION_DISTRICT))
        # Sort meetings by start time to generate the itinerary
        meetings.sort(key=lambda x: x[1])
        itinerary = []
        for person, start, end, loc in meetings:
            # Convert start and end times from minutes to HH:MM format
            total_minutes_start = 540 + start
            total_minutes_end = 540 + end
            # Ensure the times wrap around if they exceed 1440 minutes (24 hours)
            total_minutes_start = total_minutes_start % 1440
            total_minutes_end = total_minutes_end % 1440
            start_h = total_minutes_start // 60
            start_m = total_minutes_start % 60
            end_h = total_minutes_end // 60
            end_m = total_minutes_end % 60
            start_str = f"{start_h:02d}:{start_m:02d}"
            end_str = f"{end_h:02d}:{end_m:02d}"
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": start_str,
                "end_time": end_str
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)