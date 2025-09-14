import json
from z3 import Optimize, Int, And, If, sat

def minutes_to_time(m):
    # Convert minutes since midnight to "H:MM" format (24-hour, no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # Define time variables in minutes since midnight.
    # t_depart_NB: when you depart from North Beach (arrival at NB is 9:00 = 540 minutes)
    t_depart_NB = Int('t_depart_NB')
    # James meeting times at Mission District
    J_start = Int('J_start')
    J_end = Int('J_end')
    # Robert meeting times at The Castro
    R_start = Int('R_start')
    R_end = Int('R_end')
    
    # Constants for times (in minutes)
    start_NB = 9 * 60  # 9:00 AM => 540
    # James is available at Mission District from 12:45 (765) to 14:00 (840)
    J_avail_start = 12 * 60 + 45  # 765
    J_avail_end = 14 * 60         # 840
    # Robert is available at The Castro from 12:45 (765) to 15:15 (915)
    R_avail_start = 12 * 60 + 45  # 765
    R_avail_end = 15 * 60 + 15    # 915
    
    # Travel times (in minutes)
    NB_to_Mission = 18
    Mission_to_Castro = 7

    # Constraints for departure from North Beach:
    opt.add(t_depart_NB >= start_NB)
    # You must have enough time to travel from North Beach to Mission District before starting the meeting with James.
    opt.add(t_depart_NB + NB_to_Mission <= J_start)
    
    # Constraints for James meeting at Mission District:
    opt.add(J_start >= J_avail_start)
    opt.add(J_end <= J_avail_end)
    opt.add(J_end - J_start >= 75)
    
    # After finishing James meeting, travel from Mission District to The Castro.
    # Robert meeting can only start after you arrive at The Castro.
    opt.add(R_start >= J_end + Mission_to_Castro)
    
    # Constraints for Robert meeting at The Castro:
    opt.add(R_start >= R_avail_start)
    opt.add(R_end <= R_avail_end)
    opt.add(R_end - R_start >= 30)
    
    # Optional: Minimize waiting time before meetings. Define slack variables.
    slack_J = Int('slack_J')
    slack_R = Int('slack_R')
    opt.add(slack_J == J_start - J_avail_start)
    opt.add(slack_R == R_start - (J_end + Mission_to_Castro))
    opt.minimize(slack_J + slack_R)
    
    # Check for a solution that meets all constraints
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        
        # Extract computed times for James meeting
        j_start_val = model[J_start].as_long()
        j_end_val   = model[J_end].as_long()
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": minutes_to_time(j_start_val),
            "end_time": minutes_to_time(j_end_val)
        })
        
        # Extract computed times for Robert meeting
        r_start_val = model[R_start].as_long()
        r_end_val   = model[R_end].as_long()
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": minutes_to_time(r_start_val),
            "end_time": minutes_to_time(r_end_val)
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        # In case no feasible schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()