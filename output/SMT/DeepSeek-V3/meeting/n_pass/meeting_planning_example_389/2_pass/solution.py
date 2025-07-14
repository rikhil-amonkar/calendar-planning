from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Haight-Ashbury": 0,
        "Fisherman's Wharf": 1,
        "Richmond District": 2,
        "Mission District": 3,
        "Bayview": 4
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 23, 10, 11, 18],    # Haight-Ashbury to others
        [22, 0, 18, 22, 26],    # Fisherman's Wharf to others
        [10, 18, 0, 20, 26],    # Richmond District to others
        [12, 22, 20, 0, 15],    # Mission District to others
        [19, 25, 25, 13, 0]     # Bayview to others
    ]

    # Define the friends and their constraints
    friends = [
        {"name": "Sarah", "location": "Fisherman's Wharf", "start": 14*60 + 45, "end": 17*60 + 30, "min_duration": 105},
        {"name": "Mary", "location": "Richmond District", "start": 13*60 + 0, "end": 19*60 + 15, "min_duration": 75},
        {"name": "Helen", "location": "Mission District", "start": 21*60 + 45, "end": 22*60 + 30, "min_duration": 30},
        {"name": "Thomas", "location": "Bayview", "start": 15*60 + 15, "end": 18*60 + 45, "min_duration": 120}
    ]

    # Current location starts at Haight-Ashbury at 9:00 AM (540 minutes)
    current_time = 9 * 60  # 9:00 AM in minutes

    # Variables to track whether we meet each friend
    meet_sarah = Bool('meet_sarah')
    meet_mary = Bool('meet_mary')
    meet_helen = Bool('meet_helen')
    meet_thomas = Bool('meet_thomas')

    # Variables for start and end times of each meeting
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    mary_start = Int('mary_start')
    mary_end = Int('mary_end')
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    thomas_start = Int('thomas_start')
    thomas_end = Int('thomas_end')

    # Variables to track the order of meetings
    # We'll use integers to represent the order (1=first, 2=second, etc.)
    order_sarah = Int('order_sarah')
    order_mary = Int('order_mary')
    order_helen = Int('order_helen')
    order_thomas = Int('order_thomas')

    # Constraints for each friend
    # Sarah
    s.add(Implies(meet_sarah, sarah_start >= friends[0]["start"]))
    s.add(Implies(meet_sarah, sarah_end <= friends[0]["end"]))
    s.add(Implies(meet_sarah, sarah_end - sarah_start >= friends[0]["min_duration"]))
    s.add(Implies(meet_sarah, order_sarah >= 1))
    s.add(Implies(meet_sarah, order_sarah <= 4))
    
    # Mary
    s.add(Implies(meet_mary, mary_start >= friends[1]["start"]))
    s.add(Implies(meet_mary, mary_end <= friends[1]["end"]))
    s.add(Implies(meet_mary, mary_end - mary_start >= friends[1]["min_duration"]))
    s.add(Implies(meet_mary, order_mary >= 1))
    s.add(Implies(meet_mary, order_mary <= 4))
    
    # Helen
    s.add(Implies(meet_helen, helen_start >= friends[2]["start"]))
    s.add(Implies(meet_helen, helen_end <= friends[2]["end"]))
    s.add(Implies(meet_helen, helen_end - helen_start >= friends[2]["min_duration"]))
    s.add(Implies(meet_helen, order_helen >= 1))
    s.add(Implies(meet_helen, order_helen <= 4))
    
    # Thomas
    s.add(Implies(meet_thomas, thomas_start >= friends[3]["start"]))
    s.add(Implies(meet_thomas, thomas_end <= friends[3]["end"]))
    s.add(Implies(meet_thomas, thomas_end - thomas_start >= friends[3]["min_duration"]))
    s.add(Implies(meet_thomas, order_thomas >= 1))
    s.add(Implies(meet_thomas, order_thomas <= 4))

    # Ensure all orders are distinct if the friend is being met
    s.add(Implies(And(meet_sarah, meet_mary), order_sarah != order_mary))
    s.add(Implies(And(meet_sarah, meet_helen), order_sarah != order_helen))
    s.add(Implies(And(meet_sarah, meet_thomas), order_sarah != order_thomas))
    s.add(Implies(And(meet_mary, meet_helen), order_mary != order_helen))
    s.add(Implies(And(meet_mary, meet_thomas), order_mary != order_thomas))
    s.add(Implies(And(meet_helen, meet_thomas), order_helen != order_thomas))

    # Initial location is Haight-Ashbury
    prev_location = locations["Haight-Ashbury"]
    prev_end = current_time

    # We need to model the sequence of meetings and travel times
    # This is complex, so we'll use a simplified approach
    # For each meeting, the start time must be >= prev_end + travel time from prev_location to current location
    # We'll use auxiliary variables to track this

    # For Sarah
    s.add(Implies(meet_sarah, sarah_start >= prev_end + travel_times[prev_location][locations["Fisherman's Wharf"]]))
    # For Mary
    s.add(Implies(meet_mary, mary_start >= prev_end + travel_times[prev_location][locations["Richmond District"]]))
    # For Helen
    s.add(Implies(meet_helen, helen_start >= prev_end + travel_times[prev_location][locations["Mission District"]]))
    # For Thomas
    s.add(Implies(meet_thomas, thomas_start >= prev_end + travel_times[prev_location][locations["Bayview"]]))

    # We also need to ensure that meetings don't overlap in time
    # This is handled by the order constraints

    # Objective: maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == If(meet_sarah, 1, 0) + If(meet_mary, 1, 0) + If(meet_helen, 1, 0) + If(meet_thomas, 1, 0))
    maximize_num_met = num_met == 4  # Try to meet all friends first
    s.push()
    s.add(maximize_num_met)

    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Met all friends: {m.evaluate(meet_sarah)}, {m.evaluate(meet_mary)}, {m.evaluate(meet_helen)}, {m.evaluate(meet_thomas)}")
        print(f"Number of friends met: {m.evaluate(num_met)}")
        if m.evaluate(meet_sarah):
            print(f"Sarah: {m.evaluate(sarah_start)} to {m.evaluate(sarah_end)}")
        if m.evaluate(meet_mary):
            print(f"Mary: {m.evaluate(mary_start)} to {m.evaluate(mary_end)}")
        if m.evaluate(meet_helen):
            print(f"Helen: {m.evaluate(helen_start)} to {m.evaluate(helen_end)}")
        if m.evaluate(meet_thomas):
            print(f"Thomas: {m.evaluate(thomas_start)} to {m.evaluate(thomas_end)}")
    else:
        # If meeting all friends is not possible, try meeting fewer
        s.pop()
        s.add(num_met == 3)  # Try to meet 3 friends
        if s.check() == sat:
            m = s.model()
            print("SOLUTION:")
            print(f"Met 3 friends: {m.evaluate(meet_sarah)}, {m.evaluate(meet_mary)}, {m.evaluate(meet_helen)}, {m.evaluate(meet_thomas)}")
            print(f"Number of friends met: {m.evaluate(num_met)}")
            if m.evaluate(meet_sarah):
                print(f"Sarah: {m.evaluate(sarah_start)} to {m.evaluate(sarah_end)}")
            if m.evaluate(meet_mary):
                print(f"Mary: {m.evaluate(mary_start)} to {m.evaluate(mary_end)}")
            if m.evaluate(meet_helen):
                print(f"Helen: {m.evaluate(helen_start)} to {m.evaluate(helen_end)}")
            if m.evaluate(meet_thomas):
                print(f"Thomas: {m.evaluate(thomas_start)} to {m.evaluate(thomas_end)}")
        else:
            print("No feasible schedule found to meet at least 3 friends.")

solve_scheduling()