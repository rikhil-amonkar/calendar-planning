from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')
    brian_start = Int('brian_start')
    brian_end = Int('brian_end')

    # Convert friend availability windows to minutes since 9:00 AM
    # Sarah: 4:00 PM to 6:15 PM (16:00 to 18:15) -> 420 to 555 minutes (since 9:00 AM is 0)
    sarah_available_start = 16 * 60 - 9 * 60  # 7 hours * 60 = 420 minutes
    sarah_available_end = 18 * 60 + 15 - 9 * 60  # 555 minutes
    # Jeffrey: 3:00 PM to 10:00 PM (15:00 to 22:00) -> 360 to 780 minutes
    jeffrey_available_start = 15 * 60 - 9 * 60  # 360 minutes
    jeffrey_available_end = 22 * 60 - 9 * 60  # 780 minutes
    # Brian: 4:00 PM to 5:30 PM (16:00 to 17:30) -> 420 to 510 minutes
    brian_available_start = 16 * 60 - 9 * 60  # 420 minutes
    brian_available_end = 17 * 60 + 30 - 9 * 60  # 510 minutes

    # Meeting durations in minutes
    sarah_duration = 60
    jeffrey_duration = 75
    brian_duration = 75

    # Add constraints for each meeting's duration and availability
    s.add(sarah_start >= sarah_available_start)
    s.add(sarah_end <= sarah_available_end)
    s.add(sarah_end == sarah_start + sarah_duration)

    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end == jeffrey_start + jeffrey_duration)

    s.add(brian_start >= brian_available_start)
    s.add(brian_end <= brian_available_end)
    s.add(brian_end == brian_start + brian_duration)

    # Initial location is Sunset District (time 0)
    # We need to model the travel times between locations.
    # The order of meetings affects travel times. We need to sequence them properly.
    # Possible sequences: 
    # 1. Jeffrey -> Sarah -> Brian
    # 2. Jeffrey -> Brian -> Sarah
    # 3. Sarah -> Jeffrey -> Brian
    # etc. We'll model the constraints for possible sequences.

    # Let's assume the order is flexible. We'll need to ensure that the travel times between meetings are accounted for.
    # For example, if meeting Jeffrey first, then traveling to Sarah or Brian, etc.

    # We'll introduce variables to represent the order or use constraints to ensure feasible transitions.

    # Define the travel times between locations (in minutes)
    travel_times = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Alamo Square'): 16,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Alamo Square'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Union Square'): 14,
    }

    # We'll model the sequence of meetings and their locations.
    # Each meeting is at a specific location:
    # Sarah: North Beach
    # Jeffrey: Union Square
    # Brian: Alamo Square

    # We need to ensure that the time to travel from one meeting to another is accounted for.
    # For example, if meeting Jeffrey first (Union Square), then Sarah (North Beach), the travel time is 10 minutes.

    # Let's introduce variables to represent the order of meetings.
    # We'll use three variables to indicate the order (1, 2, 3 for first, second, third).

    order_sarah = Int('order_sarah')
    order_jeffrey = Int('order_jeffrey')
    order_brian = Int('order_brian')

    s.add(Distinct(order_sarah, order_jeffrey, order_brian))
    s.add(order_sarah >= 1, order_sarah <= 3)
    s.add(order_jeffrey >= 1, order_jeffrey <= 3)
    s.add(order_brian >= 1, order_brian <= 3)

    # Now, we need to model the start times based on the order.
    # The first meeting must start after travel time from Sunset District.
    # Subsequent meetings must start after the previous meeting's end time plus travel time.

    # Location of each friend:
    sarah_loc = 'North Beach'
    jeffrey_loc = 'Union Square'
    brian_loc = 'Alamo Square'

    # Initial location is 'Sunset District'
    # For each meeting, the start time must be >= previous end time + travel time from previous location.

    # We'll model the start times based on the order.
    # For each possible order, we'll add constraints.

    # For example, if order_jeffrey == 1 (Jeffrey is first):
    # jeffrey_start >= travel from Sunset to Union Square (30 minutes)
    # Then, if order_sarah == 2:
    # sarah_start >= jeffrey_end + travel from Union Square to North Beach (10 minutes)
    # Similarly for Brian.

    # We'll use If-then-else constructs to model this.

    # Define the start time constraints based on order.
    # For each possible first meeting:
    # First meeting:
    first_meeting_start = Int('first_meeting_start')
    first_meeting_loc = Int('first_meeting_loc')  # 1: Union Square, 2: North Beach, 3: Alamo Square
    s.add(Or(
        And(first_meeting_loc == 1, first_meeting_start == jeffrey_start, first_meeting_start >= 30),  # travel to Union Square: 30
        And(first_meeting_loc == 2, first_meeting_start == sarah_start, first_meeting_start >= 29),    # travel to North Beach: 29
        And(first_meeting_loc == 3, first_meeting_start == brian_start, first_meeting_start >= 17)      # travel to Alamo Square: 17
    ))

    # Second meeting:
    second_meeting_start = Int('second_meeting_start')
    second_meeting_loc = Int('second_meeting_loc')
    s.add(Or(
        # If first was Jeffrey (Union Square), second could be Sarah (North Beach) or Brian (Alamo Square)
        And(first_meeting_loc == 1, 
            Or(
                And(second_meeting_loc == 2, second_meeting_start == sarah_start, 
                    sarah_start >= jeffrey_end + 10),  # Union Square to North Beach: 10
                And(second_meeting_loc == 3, second_meeting_start == brian_start,
                    brian_start >= jeffrey_end + 15)   # Union Square to Alamo Square: 15
            )),
        # If first was Sarah (North Beach), second could be Jeffrey (Union Square) or Brian (Alamo Square)
        And(first_meeting_loc == 2,
            Or(
                And(second_meeting_loc == 1, second_meeting_start == jeffrey_start,
                    jeffrey_start >= sarah_end + 7),   # North Beach to Union Square: 7
                And(second_meeting_loc == 3, second_meeting_start == brian_start,
                    brian_start >= sarah_end + 16)      # North Beach to Alamo Square: 16
            )),
        # If first was Brian (Alamo Square), second could be Jeffrey (Union Square) or Sarah (North Beach)
        And(first_meeting_loc == 3,
            Or(
                And(second_meeting_loc == 1, second_meeting_start == jeffrey_start,
                    jeffrey_start >= brian_end + 14),    # Alamo Square to Union Square: 14
                And(second_meeting_loc == 2, second_meeting_start == sarah_start,
                    sarah_start >= brian_end + 15)       # Alamo Square to North Beach: 15
            ))
    ))

    # Third meeting:
    third_meeting_start = Int('third_meeting_start')
    third_meeting_loc = Int('third_meeting_loc')
    s.add(Or(
        # If first was Jeffrey and second was Sarah, third is Brian (Alamo Square)
        And(first_meeting_loc == 1, second_meeting_loc == 2,
            third_meeting_loc == 3, third_meeting_start == brian_start,
            brian_start >= sarah_end + 16),  # North Beach to Alamo Square: 16
        # If first was Jeffrey and second was Brian, third is Sarah (North Beach)
        And(first_meeting_loc == 1, second_meeting_loc == 3,
            third_meeting_loc == 2, third_meeting_start == sarah_start,
            sarah_start >= brian_end + 15),  # Alamo Square to North Beach: 15
        # If first was Sarah and second was Jeffrey, third is Brian (Alamo Square)
        And(first_meeting_loc == 2, second_meeting_loc == 1,
            third_meeting_loc == 3, third_meeting_start == brian_start,
            brian_start >= jeffrey_end + 15),  # Union Square to Alamo Square: 15
        # If first was Sarah and second was Brian, third is Jeffrey (Union Square)
        And(first_meeting_loc == 2, second_meeting_loc == 3,
            third_meeting_loc == 1, third_meeting_start == jeffrey_start,
            jeffrey_start >= brian_end + 14),  # Alamo Square to Union Square: 14
        # If first was Brian and second was Jeffrey, third is Sarah (North Beach)
        And(first_meeting_loc == 3, second_meeting_loc == 1,
            third_meeting_loc == 2, third_meeting_start == sarah_start,
            sarah_start >= jeffrey_end + 10),  # Union Square to North Beach: 10
        # If first was Brian and second was Sarah, third is Jeffrey (Union Square)
        And(first_meeting_loc == 3, second_meeting_loc == 2,
            third_meeting_loc == 1, third_meeting_start == jeffrey_start,
            jeffrey_start >= sarah_end + 7)    # North Beach to Union Square: 7
    ))

    # Ensure all meetings are scheduled
    s.add(jeffrey_start >= 0, sarah_start >= 0, brian_start >= 0)

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        # Extract start times
        js = m.eval(jeffrey_start).as_long()
        je = m.eval(jeffrey_end).as_long()
        ss = m.eval(sarah_start).as_long()
        se = m.eval(sarah_end).as_long()
        bs = m.eval(brian_start).as_long()
        be = m.eval(brian_end).as_long()

        # Convert minutes back to HH:MM format (from 9:00 AM base)
        def to_time_str(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        jeffrey_start_str = to_time_str(js)
        jeffrey_end_str = to_time_str(je)
        sarah_start_str = to_time_str(ss)
        sarah_end_str = to_time_str(se)
        brian_start_str = to_time_str(bs)
        brian_end_str = to_time_str(be)

        # Create itinerary
        itinerary = [
            {"action": "meet", "person": "Jeffrey", "start_time": jeffrey_start_str, "end_time": jeffrey_end_str},
            {"action": "meet", "person": "Sarah", "start_time": sarah_start_str, "end_time": sarah_end_str},
            {"action": "meet", "person": "Brian", "start_time": brian_start_str, "end_time": brian_end_str}
        ]

        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))