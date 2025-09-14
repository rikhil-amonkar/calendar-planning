from z3 import Optimize, Int, sat
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define schedule parameters in minutes from midnight
    # Arrival at Russian Hill: 9:00 -> 9*60 = 540
    arrival_russian_hill = 9 * 60  # 540 minutes
    # Travel times (in minutes)
    travel_RH_to_PH = 7
    travel_PH_to_RH = 7  # (if needed for further scheduling)
    
    # Barbara's availability at Pacific Heights:
    # 7:15 AM -> 7*60 + 15 = 435 minutes, 10:00 PM -> 22*60 = 1320 minutes
    barbara_avail_start = 7 * 60 + 15  # 435
    barbara_avail_end = 22 * 60          # 1320

    # Earliest we can start meeting Barbara is when we can be at Pacific Heights
    # Minimum departure is at arrival at Russian Hill (9:00) plus travel time
    earliest_meet_time = arrival_russian_hill + travel_RH_to_PH  # 540 + 7 = 547 minutes (9:07)

    # Define SMT variables for meeting start and end times (in minutes)
    meeting_start = Int('meeting_start')
    meeting_end   = Int('meeting_end')

    # Create an optimizer
    opt = Optimize()

    # Add constraints:
    # 1. Meeting must start no earlier than when we can arrive at Pacific Heights.
    opt.add(meeting_start >= earliest_meet_time)
    # 2. Meeting must also be within Barbara's availability window.
    opt.add(meeting_start >= barbara_avail_start)
    opt.add(meeting_end <= barbara_avail_end)
    # 3. The meeting duration must be at least 60 minutes.
    opt.add(meeting_end - meeting_start >= 60)
    # 4. The meeting's start occurs before its end.
    opt.add(meeting_start < meeting_end)
    # Extra variable bounds (optional, to keep values within a day's schedule)
    opt.add(meeting_start >= 0, meeting_start <= 24 * 60)
    opt.add(meeting_end >= 0, meeting_end <= 24 * 60)

    # Define the objective: maximize the meeting duration (i.e., meet Barbara as long as possible).
    meeting_duration = meeting_end - meeting_start
    opt.maximize(meeting_duration)

    # Check and solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        start = model[meeting_start].as_long()
        end = model[meeting_end].as_long()
        
        itinerary = [
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Barbara",
                "start_time": format_time(start),
                "end_time": format_time(end)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No solution found."}))

if __name__ == "__main__":
    main()