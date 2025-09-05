from z3 import Optimize, Int, sat
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Constants (in minutes after midnight)
    arrival_russian_hill = 9 * 60            # 9:00 AM = 540 minutes
    barbara_available_start = 13 * 60 + 15    # 13:15 = 795 minutes
    barbara_available_end = 18 * 60 + 15      # 18:15 = 1095 minutes

    # Travel durations (in minutes)
    travel_russian_hill_to_richmond = 14      # minutes
    # travel_richmond_to_russian_hill = 13    # provided but not used in this meeting schedule

    # Create an optimizer instance
    opt = Optimize()

    # Define SMT variables (all represent minutes after midnight)
    depart_time = Int("depart_time")   # Time to depart Russian Hill
    meet_start = Int("meet_start")     # Meeting start time with Barbara at Richmond District
    meet_end = Int("meet_end")         # Meeting end time with Barbara

    # Add constraints:
    # 1. You can only depart after arriving at Russian Hill
    opt.add(depart_time >= arrival_russian_hill)
    
    # 2. You must arrive at Richmond District before you can start meeting Barbara.
    #    Arrival time = depart_time + travel time.
    opt.add(meet_start >= depart_time + travel_russian_hill_to_richmond)
    
    # 3. Barbara is only available between her available start and end times.
    opt.add(meet_start >= barbara_available_start)
    opt.add(meet_end <= barbara_available_end)
    
    # 4. You want to meet Barbara for at least 45 minutes.
    opt.add(meet_end - meet_start >= 45)

    # Define the objective: maximize the meeting duration with Barbara.
    meeting_duration = meet_end - meet_start
    opt.maximize(meeting_duration)

    # Solve the constraints
    if opt.check() == sat:
        model = opt.model()
        depart_val = model[depart_time].as_long()
        meet_start_val = model[meet_start].as_long()
        meet_end_val = model[meet_end].as_long()

        # Format times into H:MM (24-hour format, no leading zeros in hour)
        formatted_meet_start = minutes_to_time(meet_start_val)
        formatted_meet_end = minutes_to_time(meet_end_val)

        # Build the itinerary as required
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": formatted_meet_start,
                "end_time": formatted_meet_end
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()