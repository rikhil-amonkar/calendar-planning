import json
from z3 import *

def minutes_to_time_string(minutes):
    # Convert minutes (offset from 9:00) to a 24-hour time string.
    total_minutes = 9 * 60 + minutes
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Define meeting time variables (in minutes from 9:00AM)
    # Carol's meeting at Marina District must be between 11:30 (150) and 15:00 (360)
    tC_start = Int('tC_start')  # Carol meeting start time
    tC_end = Int('tC_end')      # Carol meeting end time

    # Jessica's meeting at Pacific Heights must be between 15:30 (390) and 16:45 (465)
    tJ_start = Int('tJ_start')  # Jessica meeting start time
    tJ_end = Int('tJ_end')      # Jessica meeting end time

    # Constraints for Carol
    opt.add(tC_start >= 150)         # Carol is available from 11:30 (150 minutes from 9:00)
    opt.add(tC_end <= 360)           # Carol must finish by 15:00
    opt.add(tC_end - tC_start >= 60)  # Must meet Carol for at least 60 minutes

    # Constraints for Jessica
    opt.add(tJ_start >= 390)         # Jessica is available from 15:30
    opt.add(tJ_end <= 465)           # Jessica must be done by 16:45
    opt.add(tJ_end - tJ_start >= 45)  # Must meet Jessica for at least 45 minutes

    # Travel times (in minutes):
    # From Richmond District (arrival at 9:00) to Marina District is 9 minutes.
    # Although this constraint is dominated by Carol's availability window, we add it for completeness.
    opt.add(tC_start >= 9)
    
    # From Marina District to Pacific Heights is 7 minutes.
    # Jessica's meeting cannot start before finishing Carol's meeting plus travel time.
    opt.add(tJ_start >= tC_end + 7)

    # Objective: minimize the overall finish time (tJ_end) to yield an efficient schedule.
    opt.minimize(tJ_end)

    if opt.check() == sat:
        model = opt.model()
        carol_start_val = model[tC_start].as_long()
        carol_end_val = model[tC_end].as_long()
        jessica_start_val = model[tJ_start].as_long()
        jessica_end_val = model[tJ_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Carol",
                "start_time": minutes_to_time_string(carol_start_val),
                "end_time": minutes_to_time_string(carol_end_val)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Jessica",
                "start_time": minutes_to_time_string(jessica_start_val),
                "end_time": minutes_to_time_string(jessica_end_val)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()