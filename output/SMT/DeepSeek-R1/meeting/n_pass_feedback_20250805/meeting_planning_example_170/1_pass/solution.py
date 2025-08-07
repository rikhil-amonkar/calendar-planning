from z3 import *
import json

def main():
    # Convert time windows to minutes since 9:00 AM
    emily_window_start = 7 * 60  # 16:00
    emily_window_end = 8 * 60 + 15  # 17:15
    margaret_window_start = 10 * 60  # 19:00
    margaret_window_end = 12 * 60  # 21:00

    # Travel times in minutes
    NB_to_US = 7
    US_to_RH = 13

    # Define variables for meeting start times and durations
    emily_start = Int('emily_start')
    emily_duration = Int('emily_duration')
    margaret_start = Int('margaret_start')
    margaret_duration = Int('margaret_duration')

    # Create an optimizer instance
    opt = Optimize()

    # Emily's constraints
    opt.add(emily_start >= emily_window_start)
    opt.add(emily_start + emily_duration <= emily_window_end)
    opt.add(emily_duration >= 45)

    # Margaret's constraints
    opt.add(margaret_start >= margaret_window_start)
    opt.add(margaret_start + margaret_duration <= margaret_window_end)
    opt.add(margaret_duration >= 120)

    # Travel constraint: finish meeting Emily and travel to RH before Margaret's meeting
    opt.add(emily_start + emily_duration + US_to_RH <= margaret_start)

    # Maximize total meeting time
    total_meeting = emily_duration + margaret_duration
    opt.maximize(total_meeting)

    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        emily_start_val = m[emily_start].as_long()
        emily_duration_val = m[emily_duration].as_long()
        emily_end_val = emily_start_val + emily_duration_val

        margaret_start_val = m[margaret_start].as_long()
        margaret_duration_val = m[margaret_duration].as_long()
        margaret_end_val = margaret_start_val + margaret_duration_val

        # Convert minutes since 9:00 AM to HH:MM format
        def format_time(minutes):
            total_minutes = minutes
            hour = 9 + total_minutes // 60
            minute = total_minutes % 60
            return f"{hour:02d}:{minute:02d}"

        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "person": "Emily",
                "start_time": format_time(emily_start_val),
                "end_time": format_time(emily_end_val)
            },
            {
                "action": "meet",
                "person": "Margaret",
                "start_time": format_time(margaret_start_val),
                "end_time": format_time(margaret_end_val)
            }
        ]

        # Output the solution
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()