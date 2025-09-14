from z3 import Optimize, Int, Bool, If, And, Implies, Not, sat
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Initialize the optimizer
    opt = Optimize()

    # Define meeting time variables (in minutes from midnight)
    # Kenneth is available at Mission District from 12:00 (720) to 15:45 (945) with min meeting duration 45 minutes.
    kenneth_start = Int("kenneth_start")
    kenneth_end = Int("kenneth_end")
    # Thomas is available at Pacific Heights from 15:30 (930) to 19:15 (1155) with min meeting duration 75 minutes.
    thomas_start = Int("thomas_start")
    thomas_end = Int("thomas_end")

    # Define booleans for whether we meet each person.
    meetKenneth = Bool("meetKenneth")
    meetThomas = Bool("meetThomas")

    # Starting point: Nob Hill at 9:00 (540 minutes)
    start_time = 540

    # Travel times (in minutes)
    travel_NH_to_PD = 8     # Nob Hill to Pacific Heights
    travel_NH_to_MD = 13     # Nob Hill to Mission District
    travel_MD_to_PD = 16     # Mission District to Pacific Heights

    # Constraints for Kenneth's meeting at Mission District:
    # He is available from 12:00 (720) to 15:45 (945)
    opt.add(Implies(meetKenneth, kenneth_start >= 720))
    opt.add(Implies(meetKenneth, kenneth_end <= 945))
    opt.add(Implies(meetKenneth, kenneth_end - kenneth_start >= 45))
    # Must account for travel from Nob Hill (starting at 9:00) to Mission District
    opt.add(Implies(meetKenneth, kenneth_start >= start_time + travel_NH_to_MD))

    # Constraints for Thomas's meeting at Pacific Heights:
    # He is available from 15:30 (930) to 19:15 (1155)
    opt.add(Implies(meetThomas, thomas_start >= 930))
    opt.add(Implies(meetThomas, thomas_end <= 1155))
    opt.add(Implies(meetThomas, thomas_end - thomas_start >= 75))
    # If we meet Kenneth first and then Thomas, account for travel time from Mission District to Pacific Heights.
    opt.add(Implies(And(meetKenneth, meetThomas), thomas_start >= kenneth_end + travel_MD_to_PD))
    # If we only meet Thomas, then travel is from Nob Hill to Pacific Heights.
    opt.add(Implies(And(Not(meetKenneth), meetThomas), thomas_start >= start_time + travel_NH_to_PD))

    # For completeness, if a meeting is not scheduled, set its times to 0.
    opt.add(Implies(Not(meetKenneth), kenneth_start == 0))
    opt.add(Implies(Not(meetKenneth), kenneth_end == 0))
    opt.add(Implies(Not(meetThomas), thomas_start == 0))
    opt.add(Implies(Not(meetThomas), thomas_end == 0))

    # Objective: maximize the number of friends met.
    friend_count = If(meetKenneth, 1, 0) + If(meetThomas, 1, 0)
    opt.maximize(friend_count)

    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        # If meeting Kenneth is chosen, add his meeting event.
        if m.evaluate(meetKenneth):
            k_start = m[kenneth_start].as_long()
            k_end = m[kenneth_end].as_long()
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Kenneth",
                "start_time": minutes_to_time(k_start),
                "end_time": minutes_to_time(k_end)
            })
        # If meeting Thomas is chosen, add his meeting event.
        if m.evaluate(meetThomas):
            t_start = m[thomas_start].as_long()
            t_end = m[thomas_end].as_long()
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Thomas",
                "start_time": minutes_to_time(t_start),
                "end_time": minutes_to_time(t_end)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()