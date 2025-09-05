from z3 import Optimize, Int, sat
import json

def minutes_to_str(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02}"

def main():
    opt = Optimize()

    # Times are in minutes after midnight.
    # Fixed arrival at Bayview at 9:00 (540 minutes)
    bayview_arrival = 9 * 60  # 540

    # Travel times (in minutes)
    travel_bayview_to_fisher = 25
    travel_fisher_to_financial = 11
    travel_financial_to_embar = 4

    # Availability windows (in minutes after midnight)
    # Karen at Fisherman's Wharf: available from 8:45 (525) to 15:00 (900)
    karen_start_avail = 8 * 60 + 45   # 525
    karen_end_avail = 15 * 60         # 900

    # Anthony at Financial District: available from 9:15 (555) to 21:30 (1290)
    anthony_start_avail = 9 * 60 + 15  # 555
    anthony_end_avail = 21 * 60 + 30   # 1290

    # Betty at Embarcadero: available from 19:45 (1185) to 21:45 (1305)
    betty_start_avail = 19 * 60 + 45  # 1185
    betty_end_avail   = 21 * 60 + 45  # 1305

    # Minimum meeting durations (in minutes)
    min_duration_karen = 30
    min_duration_anthony = 105
    min_duration_betty = 15

    # Define decision variables for meeting start and end times.
    # Karen meeting (at Fisherman's Wharf)
    K_start = Int('K_start')
    K_end   = Int('K_end')
    # Anthony meeting (at Financial District)
    A_start = Int('A_start')
    A_end   = Int('A_end')
    # Betty meeting (at Embarcadero)
    B_start = Int('B_start')
    B_end   = Int('B_end')

    # Force meetings to last exactly the minimum required duration (optimal finish time)
    opt.add(K_end == K_start + min_duration_karen)
    opt.add(A_end == A_start + min_duration_anthony)
    opt.add(B_end == B_start + min_duration_betty)

    # CONSTRAINTS for Karen at Fisherman's Wharf:
    # Must depart Bayview and travel to Fisherman's Wharf.
    opt.add(K_start >= bayview_arrival + travel_bayview_to_fisher)
    # Must be within her availability window.
    opt.add(K_start >= karen_start_avail)
    opt.add(K_end <= karen_end_avail)

    # CONSTRAINTS for Anthony at Financial District:
    # Travel from Fisherman's Wharf to Financial District.
    opt.add(A_start >= K_end + travel_fisher_to_financial)
    # Must be within Anthony's availability window.
    opt.add(A_start >= anthony_start_avail)
    opt.add(A_end <= anthony_end_avail)

    # CONSTRAINTS for Betty at Embarcadero:
    # Travel from Financial District to Embarcadero.
    opt.add(B_start >= A_end + travel_financial_to_embar)
    # Must be within Betty's availability window.
    opt.add(B_start >= betty_start_avail)
    opt.add(B_end <= betty_end_avail)

    # To get the earliest possible finish for the schedule, minimize Betty's meeting end time.
    h1 = opt.minimize(B_end)
    # Additionally, to have a natural schedule given the friends’ time windows,
    # we prefer to meet Karen as late as possible (she's only available until 15:00)
    # and then meet Anthony as late as possible so that Betty's meeting starts at her window's opening.
    h2 = opt.maximize(K_start)
    h3 = opt.maximize(A_start)

    if opt.check() == sat:
        model = opt.model()
        # Extract solution values.
        k_start_val = model[K_start].as_long()
        k_end_val   = model[K_end].as_long()
        a_start_val = model[A_start].as_long()
        a_end_val   = model[A_end].as_long()
        b_start_val = model[B_start].as_long()
        b_end_val   = model[B_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Karen",
                "start_time": minutes_to_str(k_start_val),
                "end_time": minutes_to_str(k_end_val)
            },
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Anthony",
                "start_time": minutes_to_str(a_start_val),
                "end_time": minutes_to_str(a_end_val)
            },
            {
                "action": "meet",
                "location": "Embarcadero",
                "person": "Betty",
                "start_time": minutes_to_str(b_start_val),
                "end_time": minutes_to_str(b_end_val)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()