from z3 import *

def main():
    s = Optimize()
    # Departure time from Nob Hill (minutes after 9:00 AM)
    depart_Nob = Int('depart_Nob')
    s.add(depart_Nob >= 0)  # Cannot leave before 9:00 AM

    # Travel to Presidio takes 17 minutes
    arrival = depart_Nob + 17

    # Robert's availability: 11:15 AM (135 minutes) to 5:45 PM (525 minutes)
    # Meeting start is the later of arrival and 135
    start_meeting = If(arrival >= 135, arrival, 135)
    end_meeting = start_meeting + 120  # Must meet for exactly 120 minutes

    # Meeting must end by 5:45 PM (525 minutes)
    s.add(end_meeting <= 525)
    
    # Maximize departure time to stay at Nob Hill as long as possible
    s.maximize(depart_Nob)

    if s.check() == sat:
        m = s.model()
        depart_Nob_val = m.eval(depart_Nob).as_long()
        arrival_val = depart_Nob_val + 17
        start_meeting_val = max(arrival_val, 135)
        end_meeting_val = start_meeting_val + 120

        # Helper to convert minutes to time string (from 9:00 AM)
        def min_to_time(minutes):
            h = minutes // 60
            mm = minutes % 60
            total_h = 9 + h
            if total_h < 12:
                return f"{total_h}:{mm:02d} AM"
            elif total_h == 12:
                return f"12:{mm:02d} PM"
            else:
                return f"{total_h - 12}:{mm:02d} PM"

        print(f"Depart Nob Hill at {min_to_time(depart_Nob_val)}")
        print(f"Arrive at Presidio at {min_to_time(arrival_val)}")
        print(f"Meet Robert from {min_to_time(start_meeting_val)} to {min_to_time(end_meeting_val)}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()