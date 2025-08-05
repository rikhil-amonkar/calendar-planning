from z3 import *
import json

def main():
    # Convert times to minutes since midnight
    # Start at North Beach: 9:00 AM -> 540 minutes
    start_time_total = 9 * 60  # 9:00 AM in minutes

    # Mark's availability: 1:00 PM to 5:45 PM -> 13:00 to 17:45
    mark_start_min = 13 * 60  # 780 minutes
    mark_end_min = 17 * 60 + 45  # 1065 minutes

    # Karen's meeting: 6:45 PM to 8:15 PM -> 18:45 to 20:15
    karen_start_min = 18 * 60 + 45  # 1125 minutes
    karen_end_min = 20 * 60 + 15  # 1215 minutes

    # Create Z3 variables for Mark's meeting
    m_start = Int('m_start')
    m_end = Int('m_end')

    s = Solver()
    # Constraints for Mark's meeting
    s.add(m_start >= mark_start_min)
    s.add(m_end <= mark_end_min)
    s.add(m_end - m_start >= 120)  # 120 minutes minimum

    if s.check() == sat:
        model = s.model()
        m_start_val = model[m_start].as_long()
        m_end_val = model[m_end].as_long()

        # Convert minutes to HH:MM string
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        mark_start = format_time(m_start_val)
        mark_end = format_time(m_end_val)
        karen_start = format_time(karen_start_min)
        karen_end = format_time(karen_end_min)

        itinerary = [
            {"action": "meet", "person": "Mark", "start_time": mark_start, "end_time": mark_end},
            {"action": "meet", "person": "Karen", "start_time": karen_start, "end_time": karen_end}
        ]

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()