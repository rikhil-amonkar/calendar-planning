import json
from z3 import *

def minutes_to_time(m):
    total = 9 * 60 + m  # offset from 9:00 AM
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Define Boolean decision variables for scheduling each meeting.
    b_meet = Bool('b_meet')    # Meeting with Betty
    d_meet = Bool('d_meet')    # Meeting with David
    ba_meet = Bool('ba_meet')  # Meeting with Barbara

    # Define integer variables for start and end times (in minutes after 9:00 AM) for each meeting.
    b_start, b_end = Int('b_start'), Int('b_end')
    d_start, d_end = Int('d_start'), Int('d_end')
    ba_start, ba_end = Int('ba_start'), Int('ba_end')

    # Define integer variables to represent the order of the meetings (if scheduled).
    order_b = Int('order_b')
    order_d = Int('order_d')
    order_ba = Int('order_ba')

    # Define travel times (in minutes) between locations.
    # Locations: "Embarcadero", "Presidio", "Richmond District", "Fisherman's Wharf"
    travel = {
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18
    }

    # Meeting constraints (availability windows and minimum meeting durations):
    # Betty is at Presidio from 10:15 (75) to 21:30 (750) with a minimum meeting duration of 45 minutes.
    opt.add(Implies(b_meet, b_start >= 75))
    opt.add(Implies(b_meet, b_end <= 750))
    opt.add(Implies(b_meet, b_end - b_start >= 45))
    # David is at Richmond District from 13:00 (240) to 20:15 (675) with a minimum meeting duration of 90 minutes.
    opt.add(Implies(d_meet, d_start >= 240))
    opt.add(Implies(d_meet, d_end <= 675))
    opt.add(Implies(d_meet, d_end - d_start >= 90))
    # Barbara is at Fisherman's Wharf from 9:15 (15) to 20:15 (675) with a minimum meeting duration of 120 minutes.
    opt.add(Implies(ba_meet, ba_start >= 15))
    opt.add(Implies(ba_meet, ba_end <= 675))
    opt.add(Implies(ba_meet, ba_end - ba_start >= 120))

    # Order variable constraints.
    # If a meeting is scheduled then its order must be between 1 and 3.
    # If not scheduled, then we fix its order to 0.
    opt.add(Implies(b_meet, And(order_b >= 1, order_b <= 3)))
    opt.add(Implies(Not(b_meet), order_b == 0))
    opt.add(Implies(d_meet, And(order_d >= 1, order_d <= 3)))
    opt.add(Implies(Not(d_meet), order_d == 0))
    opt.add(Implies(ba_meet, And(order_ba >= 1, order_ba <= 3)))
    opt.add(Implies(Not(ba_meet), order_ba == 0))
    # Ensure that at least one scheduled meeting is the first (order == 1).
    opt.add(Or(And(b_meet, order_b == 1), And(d_meet, order_d == 1), And(ba_meet, order_ba == 1)))
    # Ensure distinct orders for any two scheduled meetings.
    opt.add(Implies(And(b_meet, d_meet), order_b != order_d))
    opt.add(Implies(And(b_meet, ba_meet), order_b != order_ba))
    opt.add(Implies(And(d_meet, ba_meet), order_d != order_ba))

    # Travel constraints:
    # For the first scheduled meeting, ensure arrival from Embarcadero is accounted for.
    opt.add(Implies(And(b_meet, order_b == 1), b_start >= travel[("Embarcadero", "Presidio")]))
    opt.add(Implies(And(d_meet, order_d == 1), d_start >= travel[("Embarcadero", "Richmond District")]))
    opt.add(Implies(And(ba_meet, order_ba == 1), ba_start >= travel[("Embarcadero", "Fisherman's Wharf")]))
    
    # For any two scheduled meetings, ensure that after one meeting ends and travel is done,
    # the next meeting can start.
    # Betty and David:
    opt.add(Implies(And(b_meet, d_meet, order_b < order_d),
                    b_end + travel[("Presidio", "Richmond District")] <= d_start))
    opt.add(Implies(And(b_meet, d_meet, order_d < order_b),
                    d_end + travel[("Richmond District", "Presidio")] <= b_start))
    # Betty and Barbara:
    opt.add(Implies(And(b_meet, ba_meet, order_b < order_ba),
                    b_end + travel[("Presidio", "Fisherman's Wharf")] <= ba_start))
    opt.add(Implies(And(b_meet, ba_meet, order_ba < order_b),
                    ba_end + travel[("Fisherman's Wharf", "Presidio")] <= b_start))
    # David and Barbara:
    opt.add(Implies(And(d_meet, ba_meet, order_d < order_ba),
                    d_end + travel[("Richmond District", "Fisherman's Wharf")] <= ba_start))
    opt.add(Implies(And(d_meet, ba_meet, order_ba < order_d),
                    ba_end + travel[("Fisherman's Wharf", "Richmond District")] <= d_start))

    # Ensure meeting start and end times are non-negative.
    opt.add(b_start >= 0, b_end >= 0, d_start >= 0, d_end >= 0, ba_start >= 0, ba_end >= 0)

    # Set the primary objective: maximize the number of meetings scheduled.
    objective = If(b_meet, 1, 0) + If(d_meet, 1, 0) + If(ba_meet, 1, 0)
    opt.maximize(objective)
    # Secondary objective: minimize the sum of start times for scheduled meetings (achieve an early schedule).
    opt.minimize(If(b_meet, b_start, 0) + If(d_meet, d_start, 0) + If(ba_meet, ba_start, 0))

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meetings = []
        # For each meeting, if scheduled, record its order, person, location, start, and end times.
        if is_true(model.evaluate(b_meet)):
            meetings.append((model.evaluate(order_b).as_long(), "Betty", "Presidio",
                             model.evaluate(b_start).as_long(), model.evaluate(b_end).as_long()))
        if is_true(model.evaluate(d_meet)):
            meetings.append((model.evaluate(order_d).as_long(), "David", "Richmond District",
                             model.evaluate(d_start).as_long(), model.evaluate(d_end).as_long()))
        if is_true(model.evaluate(ba_meet)):
            meetings.append((model.evaluate(order_ba).as_long(), "Barbara", "Fisherman's Wharf",
                             model.evaluate(ba_start).as_long(), model.evaluate(ba_end).as_long()))
        # Sort meetings by their scheduled order.
        meetings.sort(key=lambda x: x[0])
        for order_val, person, location, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()