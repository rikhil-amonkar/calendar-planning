from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define locations and friends
    locations = [
        "Financial District",
        "Fisherman's Wharf",
        "Presidio",
        "Bayview",
        "Haight-Ashbury",
        "Russian Hill",
        "The Castro",
        "Marina District",
        "Richmond District",
        "Union Square",
        "Sunset District"
    ]

    # Travel times matrix (simplified for this example)
    # We'll use a dictionary to map from (from_loc, to_loc) to travel time
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Union Square"): 30
    }

    # Friends data: name, location, available_start, available_end, min_duration
    friends = [
        ("Mark", "Fisherman's Wharf", 8.25, 10.0, 0.5),
        ("Stephanie", "Presidio", 12.25, 15.0, 1.25),
        ("Betty", "Bayview", 7.25, 20.5, 0.25),
        ("Lisa", "Haight-Ashbury", 15.5, 18.5, 0.75),
        ("William", "Russian Hill", 18.75, 20.0, 1.0),
        ("Brian", "The Castro", 9.25, 13.25, 0.5),
        ("Joseph", "Marina District", 10.75, 15.0, 1.5),
        ("Ashley", "Richmond District", 9.75, 11.25, 0.75),
        ("Patricia", "Union Square", 16.5, 20.0, 2.0),
        ("Karen", "Sunset District", 16.5, 22.0, 1.75)
    ]

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time):
        hours = int(time)
        minutes = (time - hours) * 60
        return hours * 60 + minutes

    # Convert back to readable time
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Initialize variables for each friend: start and end times
    friend_vars = {}
    for name, loc, start, end, dur in friends:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        dur_min = int(dur * 60)
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        s.add(start_var >= start_min)
        s.add(end_var <= end_min)
        s.add(end_var == start_var + dur_min)
        friend_vars[name] = (start_var, end_var, loc)

    # Current location starts at Financial District at 9:00 AM (540 minutes)
    current_time = 540
    current_loc = "Financial District"

    # Ensure meetings are in order with travel times
    # We'll create a list of all possible meeting orders and enforce constraints
    # This is a simplified approach; a more complete solution would consider all permutations
    # For simplicity, we'll assume an order and let Z3 find feasible times

    # For each pair of consecutive meetings, ensure travel time is accounted for
    meeting_names = [name for name, _, _, _, _ in friends]
    for i in range(len(meeting_names) - 1):
        name1 = meeting_names[i]
        name2 = meeting_names[i + 1]
        start1, end1, loc1 = friend_vars[name1]
        start2, end2, loc2 = friend_vars[name2]
        travel_time = travel_times.get((loc1, loc2), 0)
        s.add(start2 >= end1 + travel_time)

    # Also ensure the first meeting starts after arriving at Financial District
    first_name = meeting_names[0]
    start_first, _, _ = friend_vars[first_name]
    s.add(start_first >= current_time + travel_times.get((current_loc, friend_vars[first_name][2]), 0))

    # Try to meet as many friends as possible (soft constraints)
    # For this example, we'll assume we want to meet all friends if possible
    # If not, we can add soft constraints or prioritize certain friends

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in meeting_names:
            start, end, loc = friend_vars[name]
            start_time = m.eval(start).as_long()
            end_time = m.eval(end).as_long()
            schedule.append((name, loc, minutes_to_time(start_time), minutes_to_time(end_time)))
        print("SOLUTION:")
        for meeting in schedule:
            print(f"Meet {meeting[0]} at {meeting[1]} from {meeting[2]} to {meeting[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()