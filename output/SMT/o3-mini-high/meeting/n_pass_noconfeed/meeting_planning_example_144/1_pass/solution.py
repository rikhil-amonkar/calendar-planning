from z3 import *
import json

# Convert minutes since midnight to "H:MM" string format (24-hour format, no leading zero on hour)
def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize instance
    opt = Optimize()

    # Define integer variables for start and end times (in minutes past midnight)
    # Ls,Le: meeting with Laura at Mission District; As,Ae: meeting with Anthony at Financial District.
    Ls = Int('Ls')  # Laura meeting start
    Le = Int('Le')  # Laura meeting end
    As = Int('As')  # Anthony meeting start
    Ae = Int('Ae')  # Anthony meeting end

    # Boolean variable to decide the ordering.
    # orderLAfirst == True means: First go to Mission District to meet Laura, then travel to Financial District to meet Anthony.
    # orderLAfirst == False means: First go to Financial District to meet Anthony, then travel to Mission District to meet Laura.
    orderLAfirst = Bool('orderLAfirst')

    # Constants in minutes (from midnight)
    castro_arrival = 9 * 60  # 9:00 AM -> 540 minutes
    laura_avail_start = 12 * 60 + 15  # 12:15 PM -> 735 minutes
    laura_avail_end   = 19 * 60 + 45  # 7:45 PM -> 1185 minutes
    anthony_avail_start = 12 * 60 + 30  # 12:30 PM -> 750 minutes
    anthony_avail_end   = 14 * 60 + 45  # 2:45 PM -> 885 minutes

    # Minimum meeting durations
    laura_min_meeting = 75
    anthony_min_meeting = 30

    # Travel times (in minutes)
    # Castro <-> Mission District and Financial District travel times given below:
    travel_castro_to_mission = 7
    travel_castro_to_financial = 20
    travel_mission_to_financial = 17
    travel_financial_to_mission = 17

    # Constraints for the two possible orderings:

    # Order: Meet Laura first at Mission District, then Anthony at Financial District.
    # Travel: Castro -> Mission District = 7 minutes, then Mission -> Financial = 17 minutes.
    opt.add(Implies(orderLAfirst, Ls >= castro_arrival + travel_castro_to_mission))
    opt.add(Implies(orderLAfirst, Ls >= laura_avail_start))  # Must wait for Laura's availability
    opt.add(Implies(orderLAfirst, Le >= Ls + laura_min_meeting))
    opt.add(Implies(orderLAfirst, Le <= laura_avail_end))
    opt.add(Implies(orderLAfirst, As >= Le + travel_mission_to_financial))
    opt.add(Implies(orderLAfirst, As >= anthony_avail_start))
    opt.add(Implies(orderLAfirst, Ae >= As + anthony_min_meeting))
    opt.add(Implies(orderLAfirst, Ae <= anthony_avail_end))

    # Order: Meet Anthony first at Financial District, then Laura at Mission District.
    # Travel: Castro -> Financial District = 20 minutes, then Financial -> Mission = 17 minutes.
    opt.add(Implies(Not(orderLAfirst), As >= castro_arrival + travel_castro_to_financial))
    opt.add(Implies(Not(orderLAfirst), As >= anthony_avail_start))
    opt.add(Implies(Not(orderLAfirst), Ae >= As + anthony_min_meeting))
    opt.add(Implies(Not(orderLAfirst), Ae <= anthony_avail_end))
    opt.add(Implies(Not(orderLAfirst), Ls >= Ae + travel_financial_to_mission))
    opt.add(Implies(Not(orderLAfirst), Ls >= laura_avail_start))
    opt.add(Implies(Not(orderLAfirst), Le >= Ls + laura_min_meeting))
    opt.add(Implies(Not(orderLAfirst), Le <= laura_avail_end))

    # Define an overall finish time variable and objective to minimize it.
    # For orderLAfirst=True, finish = Anthony's meeting end (Ae);
    # otherwise finish = Laura's meeting end (Le).
    finish = Int('finish')
    opt.add(finish == If(orderLAfirst, Ae, Le))
    # Minimize the finishing time (i.e. finish the schedule as early as possible)
    h1 = opt.minimize(finish)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        # Retrieve solution values (they are integers representing minutes since midnight)
        ls_val = model.evaluate(Ls).as_long()
        le_val = model.evaluate(Le).as_long()
        as_val = model.evaluate(As).as_long()
        ae_val = model.evaluate(Ae).as_long()
        order_val = is_true(model.evaluate(orderLAfirst))

        itinerary = []
        if order_val:
            # Order: Meet Laura first, then Anthony
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(ls_val),
                "end_time": format_time(le_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(as_val),
                "end_time": format_time(ae_val)
            })
        else:
            # Order: Meet Anthony first, then Laura
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": format_time(as_val),
                "end_time": format_time(ae_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Laura",
                "start_time": format_time(ls_val),
                "end_time": format_time(le_val)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No feasible schedule found."}))

if __name__ == '__main__':
    main()