from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each friend's meeting start and end times
    # Ronald (Nob Hill)
    ronald_start = Int('ronald_start')
    ronald_end = Int('ronald_end')
    # Sarah (Russian Hill)
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    # Helen (The Castro)
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    # Joshua (Sunset District)
    joshua_start = Int('joshua_start')
    joshua_end = Int('joshua_end')
    # Margaret (Haight-Ashbury)
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    # Sarah is available from 7:15 AM (435) to 9:30 AM (570)
    # Ronald is available from 10:00 AM (600) to 5:00 PM (1020)
    # Helen is available from 1:30 PM (810) to 5:00 PM (1020)
    # Joshua is available from 2:15 PM (855) to 7:30 PM (1290)
    # Margaret is available from 10:15 AM (615) to 10:00 PM (1320)

    # Constraints for each friend's meeting time within their availability
    s.add(sarah_start >= 435, sarah_end <= 570)  # Sarah's window
    s.add(sarah_end - sarah_start >= 45)         # Sarah's min duration

    s.add(ronald_start >= 600, ronald_end <= 1020)  # Ronald's window
    s.add(ronald_end - ronald_start >= 105)         # Ronald's min duration

    s.add(helen_start >= 810, helen_end <= 1020)  # Helen's window
    s.add(helen_end - helen_start >= 120)         # Helen's min duration

    s.add(joshua_start >= 855, joshua_end <= 1290)  # Joshua's window
    s.add(joshua_end - joshua_start >= 90)         # Joshua's min duration

    s.add(margaret_start >= 615, margaret_end <= 1320)  # Margaret's window
    s.add(margaret_end - margaret_start >= 60)          # Margaret's min duration

    # Starting at Pacific Heights at 9:00 AM (540)
    # We can first meet Sarah (Russian Hill) before 9:30 AM
    # Travel from Pacific Heights to Russian Hill: 7 minutes
    s.add(sarah_start >= 540 + 7)  # Arrive at Russian Hill at earliest 9:07 AM

    # After meeting Sarah, we can go to other friends
    # Define order constraints and travel times
    # We'll assume a sequence: Sarah -> Ronald -> Helen -> Joshua -> Margaret
    # (This is one possible order; the solver will find feasible sequences)

    # Sarah -> Ronald: Russian Hill to Nob Hill: 5 minutes
    s.add(ronald_start >= sarah_end + 5)

    # Ronald -> Helen: Nob Hill to The Castro: 17 minutes
    s.add(helen_start >= ronald_end + 17)

    # Helen -> Joshua: The Castro to Sunset District: 17 minutes
    s.add(joshua_start >= helen_end + 17)

    # Joshua -> Margaret: Sunset District to Haight-Ashbury: 15 minutes
    s.add(margaret_start >= joshua_end + 15)

    # Alternatively, we can try other sequences, but this is one possible path

    # Check if all meetings can fit
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Sarah at Russian Hill: from {m[sarah_start]} to {m[sarah_end]}")
        print(f"Meet Ronald at Nob Hill: from {m[ronald_start]} to {m[ronald_end]}")
        print(f"Meet Helen at The Castro: from {m[helen_start]} to {m[helen_end]}")
        print(f"Meet Joshua at Sunset District: from {m[joshua_start]} to {m[joshua_end]}")
        print(f"Meet Margaret at Haight-Ashbury: from {m[margaret_start]} to {m[margaret_end]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()