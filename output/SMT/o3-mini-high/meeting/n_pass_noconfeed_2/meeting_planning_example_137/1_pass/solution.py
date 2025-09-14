from z3 import *
import json

def format_time(t):
    # Convert integer minutes from midnight to "H:MM" string.
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Time constants (in minutes from midnight)
    fd_arrival = 9 * 60         # 9:00 AM = 540
    k_avail_start = 12 * 60     # 12:00 PM = 720
    k_avail_end = 15 * 60       # 15:00 PM = 900
    b_avail_start = 8 * 60 + 15 # 8:15 AM = 495
    b_avail_end = 19 * 60       # 19:00 = 1140

    # Travel times (in minutes)
    fd_to_chinatown = 5
    fd_to_golden = 23
    chin_to_golden = 23
    golden_to_chinatown = 23

    # Meeting durations (in minutes)
    k_dur = 90   # Kenneth: at least 90 minutes
    b_dur = 45   # Barbara: at least 45 minutes

    # Create an optimizer
    opt = Optimize()

    # Decision variables:
    # order_b_first == True means visit Barbara (Golden Gate Park) first then Kenneth (Chinatown)
    order_b_first = Bool('order_b_first')
    B_start = Int('B_start')  # Start time for meeting Barbara
    K_start = Int('K_start')  # Start time for meeting Kenneth

    # Define finish_time objective depending on order:
    finish_time = If(order_b_first, K_start + k_dur, B_start + b_dur)

    # Sequence A: Meet Barbara first then Kenneth.
    cond_A = And(
        # Travel from FD to Golden Gate Park
        B_start >= fd_arrival + fd_to_golden,
        B_start >= b_avail_start,
        B_start + b_dur <= b_avail_end,
        # Kenneth's availability and meeting duration constraints
        K_start >= k_avail_start,
        K_start + k_dur <= k_avail_end,
        # Travel from Golden Gate Park to Chinatown
        K_start >= B_start + b_dur + golden_to_chinatown
    )

    # Sequence B: Meet Kenneth first then Barbara.
    cond_B = And(
        # Travel from FD to Chinatown
        K_start >= fd_arrival + fd_to_chinatown,
        K_start >= k_avail_start,
        K_start + k_dur <= k_avail_end,
        # Barbara's availability and meeting duration constraints
        B_start >= b_avail_start,
        B_start + b_dur <= b_avail_end,
        # Travel from Chinatown to Golden Gate Park
        B_start >= K_start + k_dur + chin_to_golden
    )

    # Enforce that one of the two scheduling orders is chosen.
    opt.add(Or(And(order_b_first, cond_A), And(Not(order_b_first), cond_B)))

    # Set objective: minimize the finish time of the last meeting.
    opt.minimize(finish_time)

    if opt.check() == sat:
        model = opt.model()
        # Extract variable values
        order_val = is_true(model[order_b_first])
        B_time = model[B_start].as_long() if model[B_start] is not None else None
        K_time = model[K_start].as_long() if model[K_start] is not None else None

        itinerary = []
        if order_val:
            # Schedule: Meet Barbara first at Golden Gate Park, then Kenneth at Chinatown.
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(B_time),
                "end_time": format_time(B_time + b_dur)
            })
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(K_time),
                "end_time": format_time(K_time + k_dur)
            })
        else:
            # Schedule: Meet Kenneth first at Chinatown, then Barbara at Golden Gate Park.
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": format_time(K_time),
                "end_time": format_time(K_time + k_dur)
            })
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": format_time(B_time),
                "end_time": format_time(B_time + b_dur)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()