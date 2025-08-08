from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

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
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Sunset District'): 26,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22,
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

    # Initial location is Union Square at time 0 (9:00 AM)
    # We need to sequence the meetings considering travel times.

    # We'll model the order of meetings. There are 3! = 6 possible orders.
    # We'll use auxiliary variables to represent the order.

    # Let's define the order as a list of meetings, and then add constraints based on the order.
    # But since Z3 doesn't handle permutations directly, we'll need to encode the possible orders.

    # We'll create variables to represent the order (0: Carol, 1: Karen, 2: Rebecca)
    order = [Int(f'order_{i}') for i in range(3)]
    s.add(Distinct(order[0], order[1], order[2]))
    for i in range(3):
        s.add(order[i] >= 0, order[i] <= 2)

    # Variables to represent the start and end times of each meeting in the sequence
    seq_start = [Int(f'seq_start_{i}') for i in range(3)]
    seq_end = [Int(f'seq_end_{i}') for i in range(3)]
    seq_location = [Int(f'seq_location_{i}') for i in range(3)]
    # Locations: 0: Union Square, 1: Mission District, 2: Bayview, 3: Sunset District

    # Initial state: at Union Square at time 0
    prev_location = 0  # Union Square
    prev_time = 0

    # Constraints for each position in the sequence
    for i in range(3):
        # The i-th meeting in the sequence is determined by order[i]
        # meeting 0: Carol (Sunset District, location 3)
        # meeting 1: Karen (Bayview, location 2)
        # meeting 2: Rebecca (Mission District, location 1)
        s.add(Or(
            And(order[i] == 0, seq_location[i] == 3, seq_start[i] == carol_start, seq_end[i] == carol_end),
            And(order[i] == 1, seq_location[i] == 2, seq_start[i] == karen_start, seq_end[i] == karen_end),
            And(order[i] == 2, seq_location[i] == 1, seq_start[i] == rebecca_start, seq_end[i] == rebecca_end)
        ))

        # Travel time from previous location to current location
        if i == 0:
            # From Union Square (0) to seq_location[i]
            s.add(seq_start[i] >= prev_time + travel[(prev_location, seq_location[i])])
        else:
            s.add(seq_start[i] >= seq_end[i-1] + travel[(seq_location[i-1], seq_location[i])])

    # Ensure all meetings are scheduled
    # This is handled by the Distinct constraint on order variables

    # Now, we need to ensure that the meetings don't overlap in time and that travel times are respected.
    # The sequence constraints above should handle that.

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
                meetings.append(("Carol", m[carol_start].as_long(), m[carol_end].as_long(), 3))
            elif meeting_order[i] == 1:
                meetings.append(("Karen", m[karen_start].as_long(), m[karen_end].as_long(), 2))
            elif meeting_order[i] == 2:
                meetings.append(("Rebecca", m[rebecca_start].as_long(), m[rebecca_end].as_long(), 1))
        # Sort meetings by start time to generate the itinerary
        meetings.sort(key=lambda x: x[1])
        itinerary = []
        for person, start, end, loc in meetings:
            # Convert start and end times from minutes to HH:MM format
            start_h = (540 + start) // 60
            start_m = (540 + start) % 60
            end_h = (540 + end) // 60
            end_m = (540 + end) % 60
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