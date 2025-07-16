from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each friend's meeting start and end times
    # Also, define variables for travel times between locations
    # Friends: Jessica (Golden Gate Park), Ashley (Bayview), Ronald (Chinatown), William (North Beach), Daniel (Mission District)
    
    # Arrival time at Presidio is fixed at 9:00 AM (540 minutes since midnight)
    arrival_presidio = 540  # 9:00 AM in minutes

    # Variables for meeting Daniel at Mission District
    meet_daniel_start = Int('meet_daniel_start')
    meet_daniel_end = Int('meet_daniel_end')
    # Daniel is available from 7:00 AM (420) to 11:15 AM (675)
    s.add(meet_daniel_start >= 420)
    s.add(meet_daniel_end <= 675)
    s.add(meet_daniel_end - meet_daniel_start >= 105)  # Minimum 105 minutes

    # Travel from Presidio to Mission District takes 26 minutes
    # So, we must arrive at Mission District by meet_daniel_start
    # Assuming we leave Presidio at 9:00 AM (540), arrive at Mission District at 540 + 26 = 566
    # But we need to meet Daniel before 11:15 AM (675)
    s.add(meet_daniel_start >= 540 + 26)  # Arrive at Mission District at 566, meet starts at earliest 566

    # Variables for meeting Ronald at Chinatown
    meet_ronald_start = Int('meet_ronald_start')
    meet_ronald_end = Int('meet_ronald_end')
    # Ronald is available from 7:15 AM (435) to 2:45 PM (885)
    s.add(meet_ronald_start >= 435)
    s.add(meet_ronald_end <= 885)
    s.add(meet_ronald_end - meet_ronald_start >= 90)  # Minimum 90 minutes

    # Travel from Mission District to Chinatown takes 16 minutes
    # So, after meeting Daniel, we can go to Chinatown
    s.add(meet_ronald_start >= meet_daniel_end + 16)

    # Variables for meeting Jessica at Golden Gate Park
    meet_jessica_start = Int('meet_jessica_start')
    meet_jessica_end = Int('meet_jessica_end')
    # Jessica is available from 1:45 PM (825) to 3:00 PM (900)
    s.add(meet_jessica_start >= 825)
    s.add(meet_jessica_end <= 900)
    s.add(meet_jessica_end - meet_jessica_start >= 30)  # Minimum 30 minutes

    # Travel from Chinatown to Golden Gate Park takes 23 minutes
    s.add(meet_jessica_start >= meet_ronald_end + 23)

    # Variables for meeting William at North Beach
    meet_william_start = Int('meet_william_start')
    meet_william_end = Int('meet_william_end')
    # William is available from 1:15 PM (795) to 8:15 PM (1215)
    s.add(meet_william_start >= 795)
    s.add(meet_william_end <= 1215)
    s.add(meet_william_end - meet_william_start >= 15)  # Minimum 15 minutes

    # Travel from Golden Gate Park to North Beach takes 24 minutes
    s.add(meet_william_start >= meet_jessica_end + 24)

    # Variables for meeting Ashley at Bayview
    meet_ashley_start = Int('meet_ashley_start')
    meet_ashley_end = Int('meet_ashley_end')
    # Ashley is available from 5:15 PM (1035) to 8:00 PM (1200)
    s.add(meet_ashley_start >= 1035)
    s.add(meet_ashley_end <= 1200)
    s.add(meet_ashley_end - meet_ashley_start >= 105)  # Minimum 105 minutes

    # Travel from North Beach to Bayview takes 22 minutes
    s.add(meet_ashley_start >= meet_william_end + 22)

    # Objective: Maximize the number of friends met (all in this case)
    # Since we are trying to meet all friends, the objective is to satisfy all constraints

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Daniel at Mission District: {m[meet_daniel_start].as_long() // 60}:{m[meet_daniel_start].as_long() % 60:02d} to {m[meet_daniel_end].as_long() // 60}:{m[meet_daniel_end].as_long() % 60:02d}")
        print(f"Meet Ronald at Chinatown: {m[meet_ronald_start].as_long() // 60}:{m[meet_ronald_start].as_long() % 60:02d} to {m[meet_ronald_end].as_long() // 60}:{m[meet_ronald_end].as_long() % 60:02d}")
        print(f"Meet Jessica at Golden Gate Park: {m[meet_jessica_start].as_long() // 60}:{m[meet_jessica_start].as_long() % 60:02d} to {m[meet_jessica_end].as_long() // 60}:{m[meet_jessica_end].as_long() % 60:02d}")
        print(f"Meet William at North Beach: {m[meet_william_start].as_long() // 60}:{m[meet_william_start].as_long() % 60:02d} to {m[meet_william_end].as_long() // 60}:{m[meet_william_end].as_long() % 60:02d}")
        print(f"Meet Ashley at Bayview: {m[meet_ashley_start].as_long() // 60}:{m[meet_ashley_start].as_long() % 60:02d} to {m[meet_ashley_end].as_long() // 60}:{m[meet_ashley_end].as_long() % 60:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()