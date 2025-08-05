import json
from z3 import *

def main():
    # Define the variables
    e_start = Int('e_start')  # Start time for meeting with Emily (minutes from midnight)
    t_emily = Int('t_emily')  # Duration of meeting with Emily (minutes)
    m_start = Int('m_start')  # Start time for meeting with Margaret (minutes from midnight)
    t_margaret = Int('t_margaret')  # Duration of meeting with Margaret (minutes)

    opt = Optimize()

    # Absolute times in minutes from midnight
    # Emily's window: 16:00 (960) to 17:15 (1035)
    emily_window_start = 16 * 60
    emily_window_end = 17 * 60 + 15

    # Margaret's window: 19:00 (1140) to 21:00 (1260)
    margaret_window_start = 19 * 60
    margaret_window_end = 21 * 60

    # Constraints for Emily
    opt.add(e_start >= emily_window_start)
    opt.add(e_start + t_emily <= emily_window_end)
    opt.add(t_emily >= 45)

    # Constraints for Margaret
    opt.add(m_start >= margaret_window_start)
    opt.add(m_start + t_margaret <= margaret_window_end)
    opt.add(t_margaret >= 120)

    # Travel constraints
    # Start at North Beach at 9:00 (540 minutes from midnight)
    # Travel to Union Square: 7 minutes -> arrive at 547
    # Travel from Union Square to Russian Hill: 13 minutes
    # Therefore, must arrive at Russian Hill by m_start
    # The arrival time at Russian Hill is: e_start + t_emily + 13
    opt.add(m_start >= e_start + t_emily + 13)

    # Maximize the total meeting time
    opt.maximize(t_emily + t_margaret)

    if opt.check() == sat:
        m = opt.model()
        e_start_val = m[e_start].as_long()
        t_emily_val = m[t_emily].as_long()
        e_end_val = e_start_val + t_emily_val

        m_start_val = m[m_start].as_long()
        t_margaret_val = m[t_margaret].as_long()
        m_end_val = m_start_val + t_margaret_val

        # Convert minutes to HH:MM format
        def format_time(total_minutes):
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"

        emily_start_str = format_time(e_start_val)
        emily_end_str = format_time(e_end_val)
        margaret_start_str = format_time(m_start_val)
        margaret_end_str = format_time(m_end_val)

        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": emily_start_str, "end_time": emily_end_str},
            {"action": "meet", "person": "Margaret", "start_time": margaret_start_str, "end_time": margaret_end_str}
        ]

        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()