import json
from z3 import *

def minutes_to_time(m):
    # Convert an integer minute (minutes from midnight) into an HH:MM string.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Create a Z3 solver instance.
    s = Solver()

    # Decision variables (in minutes from midnight)
    H_start = Int('H_start')  # When to start meeting Helen at North Beach
    K_start = Int('K_start')  # When to start meeting Kimberly at Fisherman's Wharf
    P_start = Int('P_start')  # When to start meeting Patricia at Bayview

    # Define fixed meeting durations (in minutes)
    H_duration = 120
    K_duration = 45
    P_duration = 120

    # Define end time expressions using the start variables and durations
    H_end = H_start + H_duration
    K_end = K_start + K_duration
    P_end = P_start + P_duration

    # Define constant times (in minutes from midnight)
    # You arrive at Nob Hill at 9:00. Then travel from Nob Hill to North Beach takes 8 minutes.
    arrival_NB = 9 * 60 + 8  # 9:08, so H_start cannot be before 9:08.
    
    # Friend availabilities (given in the problem)
    H_avail_start = 7  * 60       # Helen available from 7:00
    H_avail_end   = 16 * 60 + 45   # Helen available until 16:45
    K_avail_start = 16 * 60 + 30   # Kimberly available from 16:30
    K_avail_end   = 21 * 60        # Kimberly available until 21:00
    P_avail_start = 18 * 60        # Patricia available from 18:00
    P_avail_end   = 21 * 60 + 15   # Patricia available until 21:15

    # Travel times between locations (in minutes)
    travel_NB_to_FW = 5   # North Beach to Fisherman's Wharf
    travel_FW_to_BV = 26  # Fisherman's Wharf to Bayview

    # ----- CONSTRAINTS -----

    # Meeting with Helen at North Beach:
    # • You arrive at North Beach no earlier than 9:08.
    s.add(H_start >= arrival_NB)
    # • The meeting must last 120 minutes and finish before Helen leaves (16:45).
    s.add(H_end <= H_avail_end)
    # (Also, Helen is available after 7:00, but your arrival is later so no conflict.)

    # Meeting with Kimberly at Fisherman's Wharf:
    # • Kimberly is available from 16:30 to 21:00.
    s.add(K_start >= K_avail_start)
    s.add(K_end <= K_avail_end)
    # • You must travel from North Beach to Fisherman's Wharf (5 minutes) after finishing with Helen.
    s.add(K_start >= H_end + travel_NB_to_FW)

    # Meeting with Patricia at Bayview:
    # • Patricia is available from 18:00 to 21:15.
    s.add(P_start >= P_avail_start)
    s.add(P_end <= P_avail_end)
    # • You must complete Kimberly’s meeting plus a 26‐minute travel from Fisherman's Wharf to Bayview.
    s.add(P_start >= K_end + travel_FW_to_BV)

    # (No explicit objective is needed since meeting everyone is the goal.
    #  The constraints force a chain that yields a valid itinerary.)

    # Solve the constraints.
    if s.check() == sat:
        model = s.model()
        H_start_val = model[H_start].as_long()
        K_start_val = model[K_start].as_long()
        P_start_val = model[P_start].as_long()
        
        itinerary = [
            {
                "action": "meet",
                "person": "Helen",
                "start_time": minutes_to_time(H_start_val),
                "end_time": minutes_to_time(H_start_val + H_duration)
            },
            {
                "action": "meet",
                "person": "Kimberly",
                "start_time": minutes_to_time(K_start_val),
                "end_time": minutes_to_time(K_start_val + K_duration)
            },
            {
                "action": "meet",
                "person": "Patricia",
                "start_time": minutes_to_time(P_start_val),
                "end_time": minutes_to_time(P_start_val + P_duration)
            }
        ]
        
        # Output the itinerary as a JSON-formatted dictionary.
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()