from z3 import *

def main():
    T_start = Int('T_start')
    T_duration = Int('T_duration')
    T_end = T_start + T_duration

    P_duration = Int('P_duration')
    P_start = 1110  # Fixed start time for Patricia (18:30)
    P_end = P_start + P_duration

    A_start = 1230  # Fixed start time for Ashley (20:30)
    A_end = 1275    # Fixed end time for Ashley (21:15)

    s = Solver()

    # Constraints for Timothy
    s.add(T_start >= 585)        # Available from 9:45
    s.add(T_start <= 945)        # To ensure T_end <= 1065 (17:45)
    s.add(T_duration >= 120)     # Minimum meeting duration
    s.add(T_end <= 1065)         # Available until 17:45
    s.add(T_start >= 540 + 8)    # Travel from Russian Hill to Embarcadero (8 minutes)

    # Constraints for Patricia
    s.add(P_duration >= 90)      # Minimum meeting duration
    s.add(P_duration <= 107)     # To ensure P_end + travel time <= Ashley's start time

    # Travel constraints
    s.add(P_start >= T_end + 10) # Travel from Embarcadero to Nob Hill (10 minutes)
    s.add(A_start >= P_end + 13) # Travel from Nob Hill to Mission District (13 minutes)

    if s.check() == sat:
        m = s.model()
        T_start_val = m[T_start].as_long()
        T_duration_val = m[T_duration].as_long()
        T_end_val = T_start_val + T_duration_val

        P_duration_val = m[P_duration].as_long()
        P_start_val = 1110
        P_end_val = P_start_val + P_duration_val

        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Timothy", "start_time": format_time(T_start_val), "end_time": format_time(T_end_val)},
            {"action": "meet", "person": "Patricia", "start_time": format_time(P_start_val), "end_time": format_time(P_end_val)},
            {"action": "meet", "person": "Ashley", "start_time": "20:30", "end_time": "21:15"}
        ]
        result = {"itinerary": itinerary}
        print(result)
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()