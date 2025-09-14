#!/usr/bin/env python3
import json
from z3 import Optimize, Int, Bool, If, Not, Implies, is_true, sat

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define time variables (in minutes from midnight)
    # Arrival at The Castro is 9:00 AM, i.e., 540 minutes after midnight.
    arrival = 540

    # Meeting with Laura (in Mission District)
    L_start = Int("L_start")  # start time for meeting with Laura
    L_end = Int("L_end")      # end time for meeting with Laura

    # Meeting with Anthony (in Financial District)
    A_start = Int("A_start")  # start time for meeting with Anthony
    A_end = Int("A_end")      # end time for meeting with Anthony

    # Boolean decision: if True, then meet Laura first then Anthony; if False, vice versa.
    laura_first = Bool("laura_first")

    # --- Constraints for available schedules and travel times  ---

    # When meeting Laura first:
    # * Laura is available from 12:15 (735) to 19:45 (1185) and must be met for at least 75 minutes.
    opt.add(Implies(laura_first, L_start >= 735))
    opt.add(Implies(laura_first, L_end >= L_start + 75))
    opt.add(Implies(laura_first, L_end <= 1185))
    # * After her meeting, travel from Mission District to Financial District takes 17 minutes.
    opt.add(Implies(laura_first, A_start >= L_end + 17))
    # * Anthony’s available from 12:30 (750) to 14:45 (885) and must be met for at least 30 minutes.
    opt.add(Implies(laura_first, A_start >= 750))
    opt.add(Implies(laura_first, A_end >= A_start + 30))
    opt.add(Implies(laura_first, A_end <= 885))
    # * Also, from The Castro, travel to Mission District takes 7 minutes.
    opt.add(Implies(laura_first, L_start >= arrival + 7))

    # When meeting Anthony first:
    opt.add(Implies(Not(laura_first), A_start >= 750))
    opt.add(Implies(Not(laura_first), A_end >= A_start + 30))
    opt.add(Implies(Not(laura_first), A_end <= 885))
    # * Then travel from Financial District to Mission District takes 17 minutes.
    opt.add(Implies(Not(laura_first), L_start >= A_end + 17))
    # * And Laura is available from 12:15 (735) to 19:45 (1185) for at least 75 minutes.
    opt.add(Implies(Not(laura_first), L_start >= 735))
    opt.add(Implies(Not(laura_first), L_end >= L_start + 75))
    opt.add(Implies(Not(laura_first), L_end <= 1185))
    # * From The Castro, travel to Financial District takes 20 minutes.
    opt.add(Implies(Not(laura_first), A_start >= arrival + 20))

    # Define the overall finish time (if Laura is met first then finish is when Anthony ends, otherwise when Laura ends)
    finish_time = If(laura_first, A_end, L_end)
    opt.minimize(finish_time)

    # --- Solve the optimization problem ---
    result = opt.check()
    if result == sat:
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

        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()