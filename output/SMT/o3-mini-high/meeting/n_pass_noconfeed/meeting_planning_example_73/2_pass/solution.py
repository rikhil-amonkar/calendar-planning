from z3 import Optimize, Int, sat
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define time constants in minutes from midnight
    arrival_russian_hill = 9 * 60          # 9:00 AM -> 540 minutes
    travel_rh_to_ph = 7                   # 7 minutes travel time
    barbara_start = 7 * 60 + 15           # 7:15 AM -> 435 minutes
    barbara_end = 22 * 60                 # 10:00 PM -> 1320 minutes
    min_meet_duration = 60                # 60 minutes

    # Create Z3 optimizer instance
    opt = Optimize()

    # Decision variables for meeting start and end times (in minutes from midnight)
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add constraints:
    # 1. You arrive at Russian Hill at 9:00 and must travel 7 minutes to Pacific Heights.
    #    So meeting can't start before 9:00 + 7 = 547 minutes (i.e., 9:07).
    opt.add(meeting_start >= arrival_russian_hill + travel_rh_to_ph)

    # 2. Barbara is available from 7:15 to 22:00.
    #    The meeting must occur while she is at Pacific Heights.
    opt.add(meeting_start >= barbara_start)  # This is automatically satisfied since 547 > 435
    opt.add(meeting_end <= barbara_end)

    # 3. The meeting duration must be at least 60 minutes.
    opt.add(meeting_end - meeting_start >= min_meet_duration)

    # Set objective: maximize meeting duration
    duration = meeting_end - meeting_start
    opt.maximize(duration)

    # Check and get the model
    if opt.check() == sat:
        model = opt.model()
        start_time_val = model[meeting_start].as_long()
        end_time_val = model[meeting_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": minutes_to_time_str(start_time_val),
                "end_time": minutes_to_time_str(end_time_val)
            }
        ]

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid schedule found"}, indent=2))

if __name__ == "__main__":
    main()