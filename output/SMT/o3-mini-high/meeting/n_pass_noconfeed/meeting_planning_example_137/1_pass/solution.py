import json
from z3 import *

def minutes_to_time_str(m):
    h = m // 60
    min_part = m % 60
    return f"{h}:{min_part:02d}"

def main():
    # Travel time constants (in minutes)
    FD_to_Chinatown = 5
    FD_to_GGP = 23
    Chinatown_to_FD = 5
    Chinatown_to_GGP = 23
    GGP_to_FD = 26
    GGP_to_Chinatown = 23

    # Time availability (in minutes from midnight)
    arrival_FD = 9 * 60             # 9:00 -> 540
    Kenneth_avail_start = 12 * 60     # 12:00 -> 720
    Kenneth_avail_end = 15 * 60       # 15:00 -> 900
    Barbara_avail_start = 8 * 60 + 15   # 8:15 -> 495
    Barbara_avail_end = 19 * 60       # 19:00 -> 1140

    # Minimum meeting durations
    min_meet_K = 90
    min_meet_B = 45

    # Create an Optimize instance
    opt = Optimize()

    # Decision variable: orderBFirst is True if meeting Barbara first (at Golden Gate Park)
    # then meeting Kenneth (at Chinatown). Otherwise, Kenneth first then Barbara.
    orderBFirst = Bool("orderBFirst")

    # Define meeting start and end times (in minutes from midnight)
    start_B = Int("start_B")
    end_B = Int("end_B")
    start_K = Int("start_K")
    end_K = Int("end_K")

    # Define the final finish time as the end time of the last meeting in the itinerary
    final_time = Int("final_time")
    # In our model, if orderBFirst then last meeting is Kenneth's meeting; otherwise Barbara's.
    opt.add(final_time == If(orderBFirst, end_K, end_B))

    # --- Constraints for when Barbara is met first (at Golden Gate Park), then Kenneth ---
    opt.add(Implies(orderBFirst,
                    And(
                        # Travel from Financial District to Golden Gate Park
                        start_B >= arrival_FD + FD_to_GGP,
                        # Barbara must be available at Golden Gate Park
                        start_B >= Barbara_avail_start,
                        end_B <= Barbara_avail_end,
                        end_B - start_B >= min_meet_B,
                        # Then travel from Golden Gate Park to Chinatown for Kenneth
                        start_K >= end_B + GGP_to_Chinatown,
                        # Kenneth is available in Chinatown starting at 12:00
                        start_K >= Kenneth_avail_start,
                        end_K <= Kenneth_avail_end,
                        end_K - start_K >= min_meet_K
                    )
                   ))

    # --- Constraints for when Kenneth is met first (at Chinatown), then Barbara ---
    opt.add(Implies(Not(orderBFirst),
                    And(
                        # Travel from Financial District to Chinatown
                        start_K >= arrival_FD + FD_to_Chinatown,
                        # Kenneth availability in Chinatown
                        start_K >= Kenneth_avail_start,
                        end_K <= Kenneth_avail_end,
                        end_K - start_K >= min_meet_K,
                        # Then travel from Chinatown to Golden Gate Park for Barbara
                        start_B >= end_K + Chinatown_to_GGP,
                        # Barbara is available at Golden Gate Park
                        start_B >= Barbara_avail_start,
                        end_B <= Barbara_avail_end,
                        end_B - start_B >= min_meet_B
                    )
                   ))

    # Objective: minimize the finishing time of the last meeting
    opt.minimize(final_time)

    # Check and extract a model from the optimizer
    if opt.check() == sat:
        model = opt.model()
        order = model.evaluate(orderBFirst)
        sb = model.evaluate(start_B).as_long()
        eb = model.evaluate(end_B).as_long()
        sk = model.evaluate(start_K).as_long()
        ek = model.evaluate(end_K).as_long()

        itinerary = []
        if is_true(order):
            # Order: Meet Barbara at Golden Gate Park, then Kenneth in Chinatown.
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": minutes_to_time_str(sb),
                "end_time": minutes_to_time_str(eb)
            })
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": minutes_to_time_str(sk),
                "end_time": minutes_to_time_str(ek)
            })
        else:
            # Order: Meet Kenneth in Chinatown, then Barbara at Golden Gate Park.
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": minutes_to_time_str(sk),
                "end_time": minutes_to_time_str(ek)
            })
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": minutes_to_time_str(sb),
                "end_time": minutes_to_time_str(eb)
            })

        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()