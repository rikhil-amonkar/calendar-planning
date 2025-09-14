from z3 import Int, Optimize, If, sat
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Constants (all times in minutes since midnight)
    start_RussianHill = 9 * 60             # 9:00 -> 540
    travel_RH_to_RD = 14                   # minutes from Russian Hill to Richmond District
    barbara_avail_start = 13 * 60 + 15       # 13:15 -> 795
    barbara_avail_end = 18 * 60 + 15         # 18:15 -> 1095
    barbara_min_duration = 45              # minimum meeting minutes with Barbara

    # We'll also assume you can meet another friend ("Alice") at Russian Hill before leaving.
    # The goal is to maximize total meeting time (Alice + Barbara) while respecting Barbara's constraints.
    #
    # Decision variables:
    #   d      : departure time from Russian Hill when leaving to meet Barbara (in minutes)
    #   b_end  : end time of the meeting with Barbara (must be <= barbara_avail_end)
    #
    # The meeting with Alice happens at Russian Hill from start_RussianHill to d.
    # The meeting with Barbara will be scheduled at Richmond District.
    # However, because Barbara only arrives at her location at barbara_avail_start,
    # the actual start of her meeting is defined as:
    #
    #   b_start = if(d + travel_RH_to_RD < barbara_avail_start) then barbara_avail_start else d + travel_RH_to_RD
    #
    # To secure the maximum meeting time with Barbara we would like to arrive by 13:15
    # (i.e. d + travel_RH_to_RD <= barbara_avail_start), but later departure might extend Alice's meeting.
    # Note that if d > (barbara_avail_start - travel_RH_to_RD), then Barbara's meeting will shift later.
    
    opt = Optimize()

    d = Int("d")       # departure time from Russian Hill (in minutes)
    b_end = Int("b_end")  # end time of Barbara meeting (in minutes)

    # Define Barbara meeting start time based on travel and her availability.
    b_start = If(d + travel_RH_to_RD < barbara_avail_start, barbara_avail_start, d + travel_RH_to_RD)

    # Add constraints:
    opt.add(d >= start_RussianHill)  # You cannot depart before arriving at Russian Hill.
    # Ensure Barbara meeting lasts at least the minimum required time.
    opt.add(b_end <= barbara_avail_end)
    opt.add(b_end - b_start >= barbara_min_duration)

    # To guarantee a proper meeting with Barbara, if we depart so late that travel pushes b_start past 1095 - 45,
    # the meeting would become impossible. So we constrain d to an upper bound.
    # Case: if d + travel_RH_to_RD >= barbara_avail_start then we require:
    #          b_end (max 1095) - (d + travel_RH_to_RD) >= 45  => d <= 1095 - travel_RH_to_RD - 45
    # Here, 1095 - 14 - 45 = 1036.
    opt.add(d <= 1036)

    # Define total meeting time as the sum of:
    #   (meeting with Alice) + (meeting with Barbara)
    total_meeting_time = (d - start_RussianHill) + (b_end - b_start)
    
    # Our objective is to maximize total meeting time.
    # Then, as a secondary objective, we maximize Barbara's meeting duration.
    # (This will encourage a schedule where you meet Barbara as long as possible within her window.)
    h1 = opt.maximize(total_meeting_time)
    h2 = opt.maximize(b_end - b_start)
    h3 = opt.maximize(d)  # Encourage a later departure (so that you can maximize your morning meeting at Russian Hill)
    
    # For optimal total meeting time, set b_end to the latest available time.
    # In an optimum solution, b_end will be 1095 (18:15). The solver will decide d.
    # Note: When d + travel_RH_to_RD <= barbara_avail_start, then b_start = barbara_avail_start.
    #       The best choice is to depart as late as possible while still arriving on time.
    #       That is, d = barbara_avail_start - travel_RH_to_RD = 795 - 14 = 781.
    # In that case, the schedule becomes:
    #    - Alice meeting: from 9:00 (540) to 13:01 (781) → 241 minutes.
    #    - Barbara meeting: from 13:15 (795) to 18:15 (1095) → 300 minutes.
    
    if opt.check() == sat:
        model = opt.model()
        d_val = model[d].as_long()
        b_end_val = model[b_end].as_long()
        # Evaluate b_start from the model (using simplify to get an integer)
        b_start_val = model.evaluate(b_start)
        if b_start_val is None:
            b_start_val = 0
        else:
            b_start_val = int(b_start_val.as_long())
        
        # Prepare times as formatted strings
        alice_start_str = minutes_to_time(start_RussianHill)
        alice_end_str = minutes_to_time(d_val)
        barbara_start_str = minutes_to_time(b_start_val)
        barbara_end_str = minutes_to_time(b_end_val)

        itinerary = [
            {
                "action": "meet",
                "location": "Russian Hill",
                "person": "Alice",
                "start_time": alice_start_str,
                "end_time": alice_end_str
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": barbara_start_str,
                "end_time": barbara_end_str
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no solution is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()