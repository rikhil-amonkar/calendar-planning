from z3 import Optimize, Int, Bool, If, And, Or, Not, sat, is_true
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define time constants (in minutes from midnight)
    start_time_bayview = 9 * 60  # 9:00 AM -> 540 minutes
    # Friend availability windows (in minutes)
    # Richard is at Union Square from 8:45 (525) to 13:00 (780)
    richard_avail_start = 525
    richard_avail_end = 780
    # Charles is at Presidio from 9:45 (585) to 13:00 (780)
    charles_avail_start = 585
    charles_avail_end = 780
    # Minimum meeting duration (120 minutes)
    meeting_duration = 120

    # Travel times (in minutes)
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }

    opt = Optimize()

    # Decision booleans for scheduling meetings
    meet_richard = Bool("meet_richard")
    meet_charles = Bool("meet_charles")

    # Start times for the meetings (in minutes from midnight)
    r_start = Int("r_start")
    c_start = Int("c_start")

    # Ordering variable if both meetings are scheduled.
    # True if Richard meeting is scheduled before Charles meeting.
    richard_first = Bool("richard_first")

    # Constraints for meeting with Richard (Union Square)
    # Must travel from Bayview to Union Square
    opt.add(Or(Not(meet_richard),
               r_start >= start_time_bayview + travel_times[('Bayview', 'Union Square')]))
    # Meeting must end by 13:00, so start + meeting_duration <= 780.
    opt.add(Or(Not(meet_richard),
               r_start <= richard_avail_end - meeting_duration))

    # Constraints for meeting with Charles (Presidio)
    # Must travel from Bayview to Presidio, and also wait until Charles is available.
    opt.add(Or(Not(meet_charles),
               c_start >= max(start_time_bayview + travel_times[('Bayview', 'Presidio')],
                             charles_avail_start)))
    opt.add(Or(Not(meet_charles),
               c_start <= charles_avail_end - meeting_duration))

    # If both meetings are scheduled, enforce an ordering constraint.
    # If meeting with Richard is first then add travel time from Union Square to Presidio,
    # otherwise, if meeting with Charles is first add travel time from Presidio to Union Square.
    opt.add(Or(
        Not(And(meet_richard, meet_charles)),
        If(richard_first,
           c_start >= r_start + meeting_duration + travel_times[('Union Square', 'Presidio')],
           r_start >= c_start + meeting_duration + travel_times[('Presidio', 'Union Square')])
    ))

    # Compute total travel time based on which meeting(s) is scheduled.
    total_travel = If(And(meet_richard, meet_charles),
                      If(richard_first,
                         travel_times[('Bayview', 'Union Square')] + travel_times[('Union Square', 'Presidio')],
                         travel_times[('Bayview', 'Presidio')] + travel_times[('Presidio', 'Union Square')]),
                      If(meet_richard,
                         travel_times[('Bayview', 'Union Square')],
                         If(meet_charles,
                            travel_times[('Bayview', 'Presidio')],
                            0)))

    # Total number of meetings scheduled.
    total_meetings = If(meet_richard, 1, 0) + If(meet_charles, 1, 0)

    # Optimization objectives:
    # 1. Maximize the number of friends met.
    # 2. Minimize total travel time as a tie-breaker.
    opt.maximize(total_meetings)
    opt.minimize(total_travel)

    if opt.check() == sat:
        model = opt.model()
    else:
        print(json.dumps({"itinerary": []}))
        return

    itinerary = []

    # Build itinerary based on the model.
    if is_true(model.evaluate(meet_richard)) and is_true(model.evaluate(meet_charles)):
        r_s = model.evaluate(r_start).as_long()
        c_s = model.evaluate(c_start).as_long()
        if r_s < c_s:
            meeting1 = {
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time_str(r_s),
                "end_time": minutes_to_time_str(r_s + meeting_duration)
            }
            meeting2 = {
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time_str(c_s),
                "end_time": minutes_to_time_str(c_s + meeting_duration)
            }
            itinerary.extend([meeting1, meeting2])
        else:
            meeting1 = {
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time_str(c_s),
                "end_time": minutes_to_time_str(c_s + meeting_duration)
            }
            meeting2 = {
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time_str(r_s),
                "end_time": minutes_to_time_str(r_s + meeting_duration)
            }
            itinerary.extend([meeting1, meeting2])
    elif is_true(model.evaluate(meet_richard)):
        r_s = model.evaluate(r_start).as_long()
        meeting = {
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": minutes_to_time_str(r_s),
            "end_time": minutes_to_time_str(r_s + meeting_duration)
        }
        itinerary.append(meeting)
    elif is_true(model.evaluate(meet_charles)):
        c_s = model.evaluate(c_start).as_long()
        meeting = {
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": minutes_to_time_str(c_s),
            "end_time": minutes_to_time_str(c_s + meeting_duration)
        }
        itinerary.append(meeting)

    # Output the result as a JSON-formatted dictionary.
    result = {
        "itinerary": itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()