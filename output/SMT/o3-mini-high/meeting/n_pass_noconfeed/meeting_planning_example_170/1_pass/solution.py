from z3 import Optimize, Int, sat
import json

def minutes_to_str(m):
    # Convert minutes (offset from 9:00 AM) to 24-hour format
    total = 9 * 60 + m  # 9:00 AM is the baseline
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define integer variables for meeting times (minutes offset from 9:00 AM)
    # Emily's meeting at Union Square
    E_start = Int('E_start')  # start time of meeting with Emily
    E_end = Int('E_end')      # end time of meeting with Emily

    # Margaret's meeting at Russian Hill
    M_start = Int('M_start')  # start time of meeting with Margaret
    M_end = Int('M_end')      # end time of meeting with Margaret

    # Travel times in minutes between locations
    travel_NB_to_US = 7       # North Beach to Union Square
    travel_US_to_RH = 13      # Union Square to Russian Hill

    # Define availability windows (in minutes since 9:00 AM)
    # Emily is available from 16:00 (420) to 17:15 (495)
    EMILY_AVAILABLE_START = 420
    EMILY_AVAILABLE_END   = 495

    # Margaret is available from 19:00 (600) to 21:00 (720)
    MARGARET_AVAILABLE_START = 600
    MARGARET_AVAILABLE_END   = 720

    # Minimum meeting durations in minutes
    MIN_DURATION_EMILY = 45
    MIN_DURATION_MARGARET = 120

    # Constraints for Emily's meeting at Union Square:
    # Arriving from North Beach (arrival at 9:00 + travel) implies we can be at Union Square by minute 7,
    # but Emily is only available starting at 420. Thus, we require:
    opt.add(E_start >= max(EMILY_AVAILABLE_START, travel_NB_to_US))
    opt.add(E_end <= EMILY_AVAILABLE_END)
    opt.add(E_end - E_start >= MIN_DURATION_EMILY)

    # Travel constraint: After meeting Emily, you need to travel to Russian Hill.
    # The travel from Union Square to Russian Hill takes 13 minutes.
    # To have a full meeting with Margaret from her available start, we require:
    opt.add(E_end + travel_US_to_RH <= MARGARET_AVAILABLE_START)

    # Constraints for Margaret's meeting at Russian Hill:
    # Even if you arrive early, Margaret is available only from 19:00. Thus, we set:
    opt.add(M_start == MARGARET_AVAILABLE_START)
    opt.add(M_end <= MARGARET_AVAILABLE_END)
    opt.add(M_end - M_start >= MIN_DURATION_MARGARET)

    # For an optimal schedule, maximize total meeting time (even though the windows force a unique solution)
    total_meeting_time = (E_end - E_start) + (M_end - M_start)
    opt.maximize(total_meeting_time)

    # Check the constraints and extract the model if satisfiable
    if opt.check() == sat:
        model = opt.model()
        emily_start = model[E_start].as_long()
        emily_end = model[E_end].as_long()
        margaret_start = model[M_start].as_long()
        margaret_end = model[M_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Union Square",
                "person": "Emily",
                "start_time": minutes_to_str(emily_start),
                "end_time": minutes_to_str(emily_end)
            },
            {
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": minutes_to_str(margaret_start),
                "end_time": minutes_to_str(margaret_end)
            }
        ]

        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No feasible schedule found."}, indent=2))

if __name__ == "__main__":
    main()