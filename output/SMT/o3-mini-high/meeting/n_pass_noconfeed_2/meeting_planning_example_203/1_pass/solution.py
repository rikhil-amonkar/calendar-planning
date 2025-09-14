import json
from z3 import Optimize, Int, And, Distinct, Implies, sat

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Meeting start time variables (minutes after 9:00)
    t_T = Int('t_T')  # Timothy at Pacific Heights
    t_D = Int('t_D')  # David at Fisherman's Wharf
    t_R = Int('t_R')  # Robert at Mission District

    # Order variables: 1 for the first meeting, 2 for second, 3 for third.
    order_T = Int('order_T')
    order_D = Int('order_D')
    order_R = Int('order_R')

    # Meeting durations in minutes
    dur_T = 75  # Timothy
    dur_D = 15  # David
    dur_R = 90  # Robert

    # Availability windows (relative to 9:00 AM)
    # Timothy: available from 9:00 (0) to 15:30 (390); 
    # David: available from 10:45 (105) to 15:30 (390);
    # Robert: available from 12:15 (195) to 19:45 (645).
    opt.add(t_T >= 0, t_T + dur_T <= 390)
    opt.add(t_D >= 105, t_D + dur_D <= 390)
    opt.add(t_R >= 195, t_R + dur_R <= 645)

    # Order variables must be 1, 2, or 3 and all different.
    opt.add(And(order_T >= 1, order_T <= 3))
    opt.add(And(order_D >= 1, order_D <= 3))
    opt.add(And(order_R >= 1, order_R <= 3))
    opt.add(Distinct(order_T, order_D, order_R))

    # Travel times from the starting point (Financial District) in minutes:
    # FD -> Pacific Heights = 13, FD -> Fisherman's Wharf = 10, FD -> Mission District = 17.
    # If a meeting is the first one (order == 1) then arrival cannot occur before travel time.
    opt.add(Implies(order_T == 1, t_T >= 13))
    opt.add(Implies(order_D == 1, t_D >= 10))
    opt.add(Implies(order_R == 1, t_R >= 17))

    # Travel times between meeting locations:
    # Pacific Heights to Fisherman's Wharf = 13;   Fisherman's Wharf to Pacific Heights = 13.
    # Pacific Heights to Mission District = 15;      Mission District to Pacific Heights = 16.
    # Fisherman's Wharf to Mission District = 22;     Mission District to Fisherman's Wharf = 22.
    #
    # Ordering constraints: If meeting f comes before meeting g then:
    # (start_f + duration_f + travel_time(f, g)) <= start_g.
    #
    # Timothy (Pacific Heights) and David (Fisherman's Wharf)
    opt.add(Implies(order_T < order_D, t_T + dur_T + 13 <= t_D))
    opt.add(Implies(order_D < order_T, t_D + dur_D + 13 <= t_T))
    # Timothy (Pacific Heights) and Robert (Mission District)
    opt.add(Implies(order_T < order_R, t_T + dur_T + 15 <= t_R))
    opt.add(Implies(order_R < order_T, t_R + dur_R + 16 <= t_T))
    # David (Fisherman's Wharf) and Robert (Mission District)
    opt.add(Implies(order_D < order_R, t_D + dur_D + 22 <= t_R))
    opt.add(Implies(order_R < order_D, t_R + dur_R + 22 <= t_D))

    # Define a makespan variable (end time of the last meeting)
    m = Int('m')
    opt.add(m >= t_T + dur_T, m >= t_D + dur_D, m >= t_R + dur_R)
    # Objective: minimize the overall finish time.
    opt.minimize(m)

    if opt.check() == sat:
        model = opt.model()

        # Retrieve start times and order values from the model.
        t_T_val = model[t_T].as_long()
        t_D_val = model[t_D].as_long()
        t_R_val = model[t_R].as_long()
        order_T_val = model[order_T].as_long()
        order_D_val = model[order_D].as_long()
        order_R_val = model[order_R].as_long()

        f_T_val = t_T_val + dur_T
        f_D_val = t_D_val + dur_D
        f_R_val = t_R_val + dur_R

        # Helper function to convert minutes offset (from 9:00) to 24-hour "H:MM" format.
        def format_time(offset):
            total_minutes = 9 * 60 + offset
            hour = total_minutes // 60
            minute = total_minutes % 60
            return f"{hour}:{minute:02d}"

        # Prepare meeting details.
        meetings = [
            {"order": order_T_val, "person": "Timothy", "location": "Pacific Heights",
             "start": t_T_val, "end": f_T_val},
            {"order": order_D_val, "person": "David", "location": "Fisherman's Wharf",
             "start": t_D_val, "end": f_D_val},
            {"order": order_R_val, "person": "Robert", "location": "Mission District",
             "start": t_R_val, "end": f_R_val}
        ]
        # Sort meetings by their scheduled order.
        meetings.sort(key=lambda x: x["order"])

        itinerary = []
        for item in meetings:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": format_time(item["start"]),
                "end_time": format_time(item["end"])
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # In case no schedule is feasible, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()