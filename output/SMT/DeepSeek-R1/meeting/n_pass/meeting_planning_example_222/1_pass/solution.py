from z3 import *

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Start at Nob Hill at 9:00 AM, arrive at North Beach at 9:08 AM (8 minutes travel)
    start_time_nob_hill = time_to_minutes("09:00")
    arrival_north_beach = start_time_nob_hill + 8  # 9:08 AM

    # Helen's availability: 7:00 AM to 4:45 PM
    helen_start_min = time_to_minutes("07:00")
    helen_end_min = time_to_minutes("16:45")  # 4:45 PM
    helen_duration = 120  # minutes

    # Kimberly's availability: 4:30 PM to 9:00 PM
    kimberly_start_min = time_to_minutes("16:30")
    kimberly_end_min = time_to_minutes("21:00")
    kimberly_duration = 45  # minutes

    # Patricia's availability: 6:00 PM to 9:15 PM
    patricia_start_min = time_to_minutes("18:00")
    patricia_end_min = time_to_minutes("21:15")
    patricia_duration = 120  # minutes

    # Travel times
    travel_nb_to_fw = 5  # North Beach to Fisherman's Wharf
    travel_fw_to_bv = 26  # Fisherman's Wharf to Bayview

    # Define Z3 integer variables for start times
    H_start = Int('H_start')
    K_start = Int('K_start')
    P_start = Int('P_start')

    s = Solver()

    # Helen constraints
    s.add(H_start >= arrival_north_beach)
    s.add(H_start + helen_duration <= helen_end_min)

    # Kimberly constraints
    s.add(K_start >= kimberly_start_min)
    s.add(K_start + kimberly_duration <= kimberly_end_min)

    # Patricia constraints
    s.add(P_start >= patricia_start_min)
    s.add(P_start + patricia_duration <= patricia_end_min)

    # Travel constraints
    s.add(K_start >= H_start + helen_duration + travel_nb_to_fw)
    s.add(P_start >= K_start + kimberly_duration + travel_fw_to_bv)

    if s.check() == sat:
        m = s.model()
        h_val = m.eval(H_start).as_long()
        k_val = m.eval(K_start).as_long()
        p_val = m.eval(P_start).as_long()

        itinerary = [
            {"action": "meet", "person": "Helen", "start_time": minutes_to_time(h_val), "end_time": minutes_to_time(h_val + helen_duration)},
            {"action": "meet", "person": "Kimberly", "start_time": minutes_to_time(k_val), "end_time": minutes_to_time(k_val + kimberly_duration)},
            {"action": "meet", "person": "Patricia", "start_time": minutes_to_time(p_val), "end_time": minutes_to_time(p_val + patricia_duration)}
        ]

        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()