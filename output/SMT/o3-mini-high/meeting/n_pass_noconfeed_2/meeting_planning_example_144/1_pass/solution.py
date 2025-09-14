import json
from z3 import Optimize, Int, Bool, If, Not, Implies, is_true

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define time variables (in minutes from midnight)
    # Arrival at The Castro is 9:00AM, i.e., 540 minutes after midnight.
    arrival = 540

    # Meeting with Laura (at Mission District)
    L_start = Int("L_start")  # start time of meeting with Laura
    L_end = Int("L_end")      # end time of meeting with Laura

    # Meeting with Anthony (at Financial District)
    A_start = Int("A_start")  # start time of meeting with Anthony
    A_end = Int("A_end")      # end time of meeting with Anthony

    # Boolean decision: if True, then meet Laura first then Anthony; if False, vice versa.
    laura_first = Bool("laura_first")
    
    # Constraints for available schedules:
    # Laura's constraints: available at Mission District from 12:15 (735) to 19:45 (1185), minimum 75 minutes.
    # Anthony's constraints: available at Financial District from 12:30 (750) to 14:45 (885), minimum 30 minutes.
    
    # When meeting Laura first:
    opt.add(Implies(laura_first, L_start >= 735))             # Laura meeting cannot start before 12:15.
    opt.add(Implies(laura_first, L_end >= L_start + 75))         # Meet Laura for at least 75 minutes.
    opt.add(Implies(laura_first, L_end <= 1185))                 # Laura meeting must end by 19:45.
    
    # After meeting Laura, travel from Mission District to Financial District: 17 minutes.
    opt.add(Implies(laura_first, A_start >= L_end + 17))
    opt.add(Implies(laura_first, A_start >= 750))                # Anthony available from 12:30.
    opt.add(Implies(laura_first, A_end >= A_start + 30))         # Meet Anthony for at least 30 minutes.
    opt.add(Implies(laura_first, A_end <= 885))                  # Anthony meeting must finish by 14:45.
    
    # When meeting Anthony first:
    opt.add(Implies(Not(laura_first), A_start >= 750))           # Anthony meeting cannot start before 12:30.
    opt.add(Implies(Not(laura_first), A_end >= A_start + 30))      # Meet Anthony for at least 30 minutes.
    opt.add(Implies(Not(laura_first), A_end <= 885))             # Anthony meeting must finish by 14:45.
    
    # Then travel from Financial District to Mission District: 17 minutes.
    opt.add(Implies(Not(laura_first), L_start >= A_end + 17))
    opt.add(Implies(Not(laura_first), L_start >= 735))           # Laura available from 12:15.
    opt.add(Implies(Not(laura_first), L_end >= L_start + 75))      # Meet Laura for at least 75 minutes.
    opt.add(Implies(Not(laura_first), L_end <= 1185))              # Laura meeting must end by 19:45.
    
    # Travel times from The Castro (initial location) to the first meeting location:
    # If meeting Laura first, travel from The Castro to Mission District takes 7 minutes.
    opt.add(Implies(laura_first, L_start >= arrival + 7))
    # If meeting Anthony first, travel from The Castro to Financial District takes 20 minutes.
    opt.add(Implies(Not(laura_first), A_start >= arrival + 20))
    
    # Define overall finish time depending on the order:
    finish_time = If(laura_first, A_end, L_end)
    # Objective: minimize the finish time of the schedule.
    opt.minimize(finish_time)

    # Solve the optimization problem
    if opt.check() == "sat":
        m = opt.model()
        laura_first_val = m.evaluate(laura_first)
        L_start_val = m.evaluate(L_start).as_long()
        L_end_val = m.evaluate(L_end).as_long()
        A_start_val = m.evaluate(A_start).as_long()
        A_end_val = m.evaluate(A_end).as_long()

        itinerary = []
        if is_true(laura_first_val):
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(L_start_val),
                "end_time": format_time(L_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(A_start_val),
                "end_time": format_time(A_end_val)
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(A_start_val),
                "end_time": format_time(A_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(L_start_val),
                "end_time": format_time(L_end_val)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()