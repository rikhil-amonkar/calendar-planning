import json
from z3 import *

def minutes_to_time(minutes):
    # Convert minutes from midnight into "H:MM" 24-hour string (no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()

    # Ordering decision:
    # If order is True, the planned order will be:
    #    1. Meet Karen at Fisherman's Wharf
    #    2. Then meet Anthony at Financial District
    #    3. Then meet Betty at Embarcadero.
    # If order is False, the order will be:
    #    1. Meet Anthony at Financial District
    #    2. Then meet Karen at Fisherman's Wharf
    #    3. Then meet Betty at Embarcadero.
    order = Bool("order")

    # Define meeting start and end times (in minutes from midnight)
    A_start = Int("A_start")
    A_end = Int("A_end")
    K_start = Int("K_start")
    K_end = Int("K_end")
    B_start = Int("B_start")
    B_end = Int("B_end")

    # Constant: Bayview arrival time is 9:00 (540 minutes)
    bayview_start = 9 * 60  # 540

    # Friend availability windows (in minutes from midnight)
    # Betty: 7:45PM to 9:45PM  -> 19:45 = 1185, 21:45 = 1305
    betty_avail_start = 19 * 60 + 45   # 1185
    betty_avail_end   = 21 * 60 + 45     # 1305
    # Karen: 8:45AM to 3:00PM -> 8:45 = 525, 15:00 = 900
    karen_avail_start = 8 * 60 + 45      # 525
    karen_avail_end   = 15 * 60          # 900
    # Anthony: 9:15AM to 9:30PM -> 9:15 = 555, 21:30 = 1290
    anthony_avail_start = 9 * 60 + 15    # 555
    anthony_avail_end   = 21 * 60 + 30   # 1290

    # Minimum meeting durations (in minutes)
    meeting_duration = {
        "Karen": 30,
        "Anthony": 105,
        "Betty": 15
    }

    # Travel times between locations (in minutes)
    travel = {
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Financial District"): 19,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10
    }

    # --- Define constraints for the two possible orders ---

    # Option 1: Order = True --> (Karen, then Anthony, then Betty)
    # 1. Travel from Bayview to Fisherman's Wharf for Karen
    cons_K_first = K_start >= bayview_start + travel[("Bayview", "Fisherman's Wharf")]
    cons_K_duration = K_end >= K_start + meeting_duration["Karen"]
    cons_K_avail = And(K_start >= karen_avail_start, K_end <= karen_avail_end)

    # 2. Travel from Fisherman's Wharf to Financial District for Anthony
    cons_A_after_K = A_start >= K_end + travel[("Fisherman's Wharf", "Financial District")]
    cons_A_duration = A_end >= A_start + meeting_duration["Anthony"]
    cons_A_avail = And(A_start >= anthony_avail_start, A_end <= anthony_avail_end)

    # 3. Travel from Financial District to Embarcadero for Betty
    cons_B_after_A = B_start >= A_end + travel[("Financial District", "Embarcadero")]

    option1 = And(cons_K_first, cons_K_duration, cons_K_avail,
                  cons_A_after_K, cons_A_duration, cons_A_avail,
                  cons_B_after_A)

    # Option 2: Order = False --> (Anthony, then Karen, then Betty)
    # 1. Travel from Bayview to Financial District for Anthony
    cons_A_first = A_start >= bayview_start + travel[("Bayview", "Financial District")]
    cons_A_duration2 = A_end >= A_start + meeting_duration["Anthony"]
    cons_A_avail2 = And(A_start >= anthony_avail_start, A_end <= anthony_avail_end)

    # 2. Travel from Financial District to Fisherman's Wharf for Karen
    cons_K_after_A = K_start >= A_end + travel[("Financial District", "Fisherman's Wharf")]
    cons_K_duration2 = K_end >= K_start + meeting_duration["Karen"]
    cons_K_avail2 = And(K_start >= karen_avail_start, K_end <= karen_avail_end)

    # 3. Travel from Fisherman's Wharf to Embarcadero for Betty
    cons_B_after_K = B_start >= K_end + travel[("Fisherman's Wharf", "Embarcadero")]

    option2 = And(cons_A_first, cons_A_duration2, cons_A_avail2,
                  cons_K_after_A, cons_K_duration2, cons_K_avail2,
                  cons_B_after_K)

    # Betty's meeting constraints (apply to both orders)
    cons_B_duration = B_end >= B_start + meeting_duration["Betty"]
    cons_B_avail = And(B_start >= betty_avail_start, B_end <= betty_avail_end)

    # Combine constraints with ordering choice
    opt.add(
        If(order, option1, option2)
    )
    opt.add(cons_B_duration, cons_B_avail)

    # --- Define an objective to optimize the travel time and final finishing time ---
    # Total travel time depends on the order:
    # For option1 (Karen, Anthony, Betty):
    #    Bayview->Fisherman's Wharf + Fisherman's Wharf->Financial District + Financial District->Embarcadero
    # For option2 (Anthony, Karen, Betty):
    #    Bayview->Financial District + Financial District->Fisherman's Wharf + Fisherman's Wharf->Embarcadero
    total_travel = If(order,
                      travel[("Bayview", "Fisherman's Wharf")] +
                      travel[("Fisherman's Wharf", "Financial District")] +
                      travel[("Financial District", "Embarcadero")],
                      travel[("Bayview", "Financial District")] +
                      travel[("Financial District", "Fisherman's Wharf")] +
                      travel[("Fisherman's Wharf", "Embarcadero")]
                     )
    # We minimize total travel time first; then we try to finish the schedule early (minimize Betty's end time)
    opt.minimize(total_travel)
    opt.minimize(B_end)

    # Check if the optimization has a solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Depending on the chosen ordering, construct the itinerary accordingly.
        if is_true(model.evaluate(order)):
            # Order: Karen then Anthony then Betty
            k_start_val = model.evaluate(K_start).as_long()
            k_end_val   = model.evaluate(K_end).as_long()
            a_start_val = model.evaluate(A_start).as_long()
            a_end_val   = model.evaluate(A_end).as_long()
            b_start_val = model.evaluate(B_start).as_long()
            b_end_val   = model.evaluate(B_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Karen",
                "start_time": minutes_to_time(k_start_val),
                "end_time": minutes_to_time(k_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": minutes_to_time(a_start_val),
                "end_time": minutes_to_time(a_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": minutes_to_time(b_start_val),
                "end_time": minutes_to_time(b_end_val)
            })
        else:
            # Order: Anthony then Karen then Betty
            a_start_val = model.evaluate(A_start).as_long()
            a_end_val   = model.evaluate(A_end).as_long()
            k_start_val = model.evaluate(K_start).as_long()
            k_end_val   = model.evaluate(K_end).as_long()
            b_start_val = model.evaluate(B_start).as_long()
            b_end_val   = model.evaluate(B_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": minutes_to_time(a_start_val),
                "end_time": minutes_to_time(a_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Karen",
                "start_time": minutes_to_time(k_start_val),
                "end_time": minutes_to_time(k_end_val)
            })
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": minutes_to_time(b_start_val),
                "end_time": minutes_to_time(b_end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()