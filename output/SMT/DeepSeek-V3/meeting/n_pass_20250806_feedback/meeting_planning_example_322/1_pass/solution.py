from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since 9:00 AM (540 minutes in 24-hour format)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Base time is 9:00 AM (540 minutes)
    base_time = 540

    # Define meeting variables for each friend
    # William: Russian Hill 18:30-20:45 (1110-1245 minutes), min 105
    william_start = Int('william_start')
    william_end = Int('william_end')
    s.add(william_start >= 1110 - base_time)  # 18:30 is 1110 minutes
    s.add(william_end <= 1245 - base_time)    # 20:45 is 1245 minutes
    s.add(william_end - william_start >= 105)

    # Michelle: Chinatown 8:15-14:00 (495-840 minutes), min 15
    michelle_start = Int('michelle_start')
    michelle_end = Int('michelle_end')
    s.add(michelle_start >= 495 - base_time)  # 8:15 is 495 minutes
    s.add(michelle_end <= 840 - base_time)    # 14:00 is 840 minutes
    s.add(michelle_end - michelle_start >= 15)

    # George: Presidio 10:30-18:45 (630-1125 minutes), min 30
    george_start = Int('george_start')
    george_end = Int('george_end')
    s.add(george_start >= 630 - base_time)    # 10:30 is 630 minutes
    s.add(george_end <= 1125 - base_time)     # 18:45 is 1125 minutes
    s.add(george_end - george_start >= 30)

    # Robert: Fisherman's Wharf 9:00-13:45 (540-825 minutes), min 30
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')
    s.add(robert_start >= 0)                  # 9:00 is 540 minutes (base_time)
    s.add(robert_end <= 825 - base_time)      # 13:45 is 825 minutes
    s.add(robert_end - robert_start >= 30)

    # Define the order of meetings and travel times
    # We need to decide the sequence of meetings. Possible sequences could be:
    # 1. Robert, Michelle, George, William
    # 2. Michelle, Robert, George, William
    # etc. We'll model possible sequences and pick one that fits.

    # For simplicity, let's assume the order is Robert -> Michelle -> George -> William
    # and add constraints accordingly.

    # Travel times from Sunset District to Fisherman's Wharf: 29 minutes
    # So Robert's start >= 29 (since we start at Sunset at 0 minutes)
    s.add(robert_start >= 29)

    # After Robert, travel to Michelle in Chinatown: Fisherman's Wharf to Chinatown: 8 minutes
    s.add(michelle_start >= robert_end + 8)

    # After Michelle, travel to George in Presidio: Chinatown to Presidio: 19 minutes
    s.add(george_start >= michelle_end + 19)

    # After George, travel to William in Russian Hill: Presidio to Russian Hill: 14 minutes
    s.add(william_start >= george_end + 14)

    # Check if all meetings can be scheduled
    if s.check() == sat:
        model = s.model()
        itinerary = []

        # Collect meeting times
        robert_s = model.evaluate(robert_start).as_long()
        robert_e = model.evaluate(robert_end).as_long()
        michelle_s = model.evaluate(michelle_start).as_long()
        michelle_e = model.evaluate(michelle_end).as_long()
        george_s = model.evaluate(george_start).as_long()
        george_e = model.evaluate(george_end).as_long()
        william_s = model.evaluate(william_start).as_long()
        william_e = model.evaluate(william_end).as_long()

        # Convert to absolute times (HH:MM)
        robert_start_time = minutes_to_time(base_time + robert_s)
        robert_end_time = minutes_to_time(base_time + robert_e)
        michelle_start_time = minutes_to_time(base_time + michelle_s)
        michelle_end_time = minutes_to_time(base_time + michelle_e)
        george_start_time = minutes_to_time(base_time + george_s)
        george_end_time = minutes_to_time(base_time + george_e)
        william_start_time = minutes_to_time(base_time + william_s)
        william_end_time = minutes_to_time(base_time + william_e)

        # Add to itinerary
        itinerary.append({"action": "meet", "person": "Robert", "start_time": robert_start_time, "end_time": robert_end_time})
        itinerary.append({"action": "meet", "person": "Michelle", "start_time": michelle_start_time, "end_time": michelle_end_time})
        itinerary.append({"action": "meet", "person": "George", "start_time": george_start_time, "end_time": george_end_time})
        itinerary.append({"action": "meet", "person": "William", "start_time": william_start_time, "end_time": william_end_time})

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
solution = solve_scheduling()
print(solution)