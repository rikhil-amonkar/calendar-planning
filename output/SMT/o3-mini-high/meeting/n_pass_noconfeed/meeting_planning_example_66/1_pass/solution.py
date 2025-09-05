from z3 import Optimize, Int, sat
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define time constants (in minutes from midnight)
    arrival_nob_hill = 9 * 60            # 9:00 AM -> 540 minutes
    travel_nob_to_presidio = 17          # Travel time from Nob Hill to Presidio
    robert_available_start = 11 * 60 + 15  # 11:15 AM -> 675 minutes
    robert_available_end = 17 * 60 + 45    # 17:45 -> 1065 minutes

    # Create SMT variables for the meeting start and end times (in minutes from midnight)
    meet_start = Int('meet_start')
    meet_end = Int('meet_end')

    opt = Optimize()

    # Constraint: You can only start meeting Robert when he is available.
    opt.add(meet_start >= robert_available_start)
    # Constraint: The meeting must finish by the time Robert leaves.
    opt.add(meet_end <= robert_available_end)
    # Constraint: You want at least 120 minutes with Robert.
    opt.add(meet_end - meet_start >= 120)
    # Constraint: Account for travel from Nob Hill to Presidio. 
    # You arrive at Nob Hill at 9:00 and traveling to Presidio takes 17 minutes.
    opt.add(meet_start >= arrival_nob_hill + travel_nob_to_presidio)

    # Optimization objective: Maximize the meeting duration (to meet as many friends as possible,
    # in this case, maximize the time you get with Robert).
    meeting_duration = meet_end - meet_start
    opt.maximize(meeting_duration)

    # Check if the constraints are satisfiable and get the optimal model.
    if opt.check() == sat:
        model = opt.model()
        start_time_val = model[meet_start].as_long()
        end_time_val = model[meet_end].as_long()
        
        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Robert",
                    "start_time": minutes_to_time(start_time_val),
                    "end_time": minutes_to_time(end_time_val)
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid schedule found."}, indent=2))

if __name__ == "__main__":
    main()