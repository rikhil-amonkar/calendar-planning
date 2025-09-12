import json
from z3 import *

def main():
    # Convert all times to minutes since 9:00 AM
    james_start = (12 * 60 + 45) - (9 * 60)  # 225 minutes
    james_end = (14 * 60) - (9 * 60)          # 300 minutes
    robert_start = (12 * 60 + 45) - (9 * 60)  # 225 minutes
    robert_end = (15 * 60 + 15) - (9 * 60)    # 375 minutes

    # Travel times in minutes
    travel_times = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "Mission District"): 7,
    }

    # Create solver
    s = Solver()

    # Meeting duration variables
    james_duration = Int('james_duration')
    robert_duration = Int('robert_duration')

    # Meeting start time variables
    james_meet_start = Int('james_meet_start')
    robert_meet_start = Int('robert_meet_start')

    # Travel start time from North Beach
    depart_north_beach = Int('depart_north_beach')

    # Order variable: 0 = James first, 1 = Robert first
    order = Int('order')

    # Constraints for meeting durations
    s.add(james_duration >= 75)
    s.add(robert_duration >= 30)

    # Constraints for meeting within availability
    s.add(james_meet_start >= james_start)
    s.add(james_meet_start + james_duration <= james_end)
    s.add(robert_meet_start >= robert_start)
    s.add(robert_meet_start + robert_duration <= robert_end)

    # Departure time constraint
    s.add(depart_north_beach >= 0)

    # Order constraints
    s.add(Or(order == 0, order == 1))

    # Constraints based on order
    # James first then Robert
    cond1 = And(order == 0,
               james_meet_start >= depart_north_beach + travel_times[("North Beach", "Mission District")],
               robert_meet_start >= james_meet_start + james_duration + travel_times[("Mission District", "The Castro")])
    
    # Robert first then James
    cond2 = And(order == 1,
               robert_meet_start >= depart_north_beach + travel_times[("North Beach", "The Castro")],
               james_meet_start >= robert_meet_start + robert_duration + travel_times[("The Castro", "Mission District")])
    
    s.add(Or(cond1, cond2))

    # Try to maximize number of meetings by allowing both
    if s.check() == sat:
        m = s.model()
        j_start = m.evaluate(james_meet_start).as_long()
        j_dur = m.evaluate(james_duration).as_long()
        r_start = m.evaluate(robert_meet_start).as_long()
        r_dur = m.evaluate(robert_duration).as_long()
        ord_val = m.evaluate(order).as_long()

        itinerary = []
        if ord_val == 0:
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": format_time(j_start),
                "end_time": format_time(j_start + j_dur)
            })
            itinerary.append({
                "action": "meet",
                "location": "The Castro",
                "person": "Robert",
                "start_time": format_time(r_start),
                "end_time": format_time(r_start + r_dur)
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "The Castro",
                "person": "Robert",
                "start_time": format_time(r_start),
                "end_time": format_time(r_start + r_dur)
            })
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": format_time(j_start),
                "end_time": format_time(j_start + j_dur)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Fallback to single meeting if both not possible
        s2 = Solver()
        s2.add(james_duration >= 75)
        s2.add(james_meet_start >= james_start)
        s2.add(james_meet_start + james_duration <= james_end)
        s2.add(james_meet_start >= depart_north_beach + travel_times[("North Beach", "Mission District")])
        
        itinerary = []
        if s2.check() == sat:
            m = s2.model()
            j_start = m.evaluate(james_meet_start).as_long()
            j_dur = m.evaluate(james_duration).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "James",
                "start_time": format_time(j_start),
                "end_time": format_time(j_start + j_dur)
            })
        else:
            s3 = Solver()
            s3.add(robert_duration >= 30)
            s3.add(robert_meet_start >= robert_start)
            s3.add(robert_meet_start + robert_duration <= robert_end)
            s3.add(robert_meet_start >= depart_north_beach + travel_times[("North Beach", "The Castro")])
            
            if s3.check() == sat:
                m = s3.model()
                r_start = m.evaluate(robert_meet_start).as_long()
                r_dur = m.evaluate(robert_duration).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": "The Castro",
                    "person": "Robert",
                    "start_time": format_time(r_start),
                    "end_time": format_time(r_start + r_dur)
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))

def format_time(minutes):
    total_minutes = minutes
    hours = (total_minutes // 60) + 9
 minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()