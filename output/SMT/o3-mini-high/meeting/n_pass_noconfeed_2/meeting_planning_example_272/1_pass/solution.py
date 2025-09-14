from z3 import Optimize, Int, If, Implies, And, Distinct, sat
import json

def to_time(minutes_offset):
    # Given minutes offset from 9:00, convert to 24-hour time string.
    # 9:00 AM is 9*60 = 540 minutes from midnight.
    total = minutes_offset + 540
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def travel_time(from_loc, to_loc):
    # Travel distances in minutes.
    if from_loc == "Russian Hill" and to_loc == "Nob Hill":
        return 5
    if from_loc == "Russian Hill" and to_loc == "Mission District":
        return 16
    if from_loc == "Russian Hill" and to_loc == "Embarcadero":
        return 8
    if from_loc == "Nob Hill" and to_loc == "Russian Hill":
        return 5
    if from_loc == "Nob Hill" and to_loc == "Mission District":
        return 13
    if from_loc == "Nob Hill" and to_loc == "Embarcadero":
        return 9
    if from_loc == "Mission District" and to_loc == "Russian Hill":
        return 15
    if from_loc == "Mission District" and to_loc == "Nob Hill":
        return 12
    if from_loc == "Mission District" and to_loc == "Embarcadero":
        return 19
    if from_loc == "Embarcadero" and to_loc == "Russian Hill":
        return 8
    if from_loc == "Embarcadero" and to_loc == "Nob Hill":
        return 10
    if from_loc == "Embarcadero" and to_loc == "Mission District":
        return 20
    return 0

def main():
    opt = Optimize()

    # Decision variables for meeting start and end times (minutes after 9:00)
    # Timothy (located at Embarcadero), available from 9:45 (45) to 17:45 (525); min meeting = 120 minutes.
    t_start = Int('t_start')
    t_end = Int('t_end')
    opt.add(t_start >= 45)
    opt.add(t_end <= 525)
    opt.add(t_end - t_start >= 120)

    # Patricia (located at Nob Hill), available from 18:30 (570) to 21:45 (765); min meeting = 90 minutes.
    p_start = Int('p_start')
    p_end = Int('p_end')
    opt.add(p_start >= 570)
    opt.add(p_end <= 765)
    opt.add(p_end - p_start >= 90)

    # Ashley (located at Mission District), available from 20:30 (690) to 21:15 (735); min meeting = 45 minutes.
    a_start = Int('a_start')
    a_end = Int('a_end')
    opt.add(a_start >= 690)
    opt.add(a_end <= 735)
    opt.add(a_end - a_start >= 45)

    # Ordering variables for the meetings (values in {1,2,3})
    # Lower value means earlier in the day.
    t_order = Int('t_order')
    p_order = Int('p_order')
    a_order = Int('a_order')
    opt.add(t_order >= 1, t_order <= 3)
    opt.add(p_order >= 1, p_order <= 3)
    opt.add(a_order >= 1, a_order <= 3)
    opt.add(Distinct(t_order, p_order, a_order))
    
    # If a meeting is first, ensure travel from Russian Hill is accounted for.
    opt.add(Implies(t_order == 1, t_start >= travel_time("Russian Hill", "Embarcadero")))
    opt.add(Implies(p_order == 1, p_start >= travel_time("Russian Hill", "Nob Hill")))
    opt.add(Implies(a_order == 1, a_start >= travel_time("Russian Hill", "Mission District")))
    
    # Ordering constraints between meetings:
    # For any two meetings, if one is scheduled before the other then
    # its meeting end time plus travel time from its location to the next must be <= the other meeting's start.
    # Timothy (Embarcadero) and Patricia (Nob Hill)
    opt.add(If(t_order < p_order,
               t_end + travel_time("Embarcadero", "Nob Hill") <= p_start,
               p_end + travel_time("Nob Hill", "Embarcadero") <= t_start))
    # Timothy (Embarcadero) and Ashley (Mission District)
    opt.add(If(t_order < a_order,
               t_end + travel_time("Embarcadero", "Mission District") <= a_start,
               a_end + travel_time("Mission District", "Embarcadero") <= t_start))
    # Patricia (Nob Hill) and Ashley (Mission District)
    opt.add(If(p_order < a_order,
               p_end + travel_time("Nob Hill", "Mission District") <= a_start,
               a_end + travel_time("Mission District", "Nob Hill") <= p_start))
    
    # To choose an optimal schedule that minimizes idle gaps between meetings,
    # define idle times for the pairs that are consecutive in order.
    idle_gap_tp = If(And(t_order < p_order, p_order == t_order + 1),
                     p_start - (t_end + travel_time("Embarcadero", "Nob Hill")), 0)
    idle_gap_pa = If(And(p_order < a_order, a_order == p_order + 1),
                     a_start - (p_end + travel_time("Nob Hill", "Mission District")), 0)
    total_idle = idle_gap_tp + idle_gap_pa
    opt.minimize(total_idle)

    # In this scenario, our goal is to meet as many friends as possible.
    # The constraints allow meetings with Timothy, Patricia, and Ashley.
    # We now check for a solution.
    if opt.check() == sat:
        model = opt.model()
        # Extract meeting times from the model.
        t_start_val = model.evaluate(t_start).as_long()
        t_end_val = model.evaluate(t_end).as_long()
        p_start_val = model.evaluate(p_start).as_long()
        p_end_val = model.evaluate(p_end).as_long()
        a_start_val = model.evaluate(a_start).as_long()
        a_end_val = model.evaluate(a_end).as_long()
        
        # Extract ordering values.
        t_order_val = model.evaluate(t_order).as_long()
        p_order_val = model.evaluate(p_order).as_long()
        a_order_val = model.evaluate(a_order).as_long()
        
        # Prepare the itinerary with meeting details.
        meetings = []
        meetings.append((t_order_val, {
            "action": "meet", 
            "location": "Embarcadero", 
            "person": "Timothy", 
            "start_time": to_time(t_start_val), 
            "end_time": to_time(t_end_val)
        }))
        meetings.append((p_order_val, {
            "action": "meet", 
            "location": "Nob Hill", 
            "person": "Patricia", 
            "start_time": to_time(p_start_val), 
            "end_time": to_time(p_end_val)
        }))
        meetings.append((a_order_val, {
            "action": "meet", 
            "location": "Mission District", 
            "person": "Ashley", 
            "start_time": to_time(a_start_val), 
            "end_time": to_time(a_end_val)
        }))
        
        # Sort meetings by their scheduled order.
        meetings_sorted = sorted(meetings, key=lambda x: x[0])
        itinerary = [meeting[1] for meeting in meetings_sorted]
        
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()