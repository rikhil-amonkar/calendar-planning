from z3 import Solver, Int, sat
import json

def main():
    # We represent time in minutes after midnight.
    # For reference:
    #  7:15  → 435, 9:00 → 540, 10:00 → 600, 10:15 → 615,
    #  13:30 → 810, 14:15 → 855, 17:00 → 1020, 19:30 → 1170, 22:00 → 1320

    # Our friends and requirements (location, window, minimum meeting duration):
    # Ronald  (Nob Hill): available [10:00, 17:00] and needs 105 minutes.
    # Sarah   (Russian Hill): [7:15, 9:30] and 45 minutes required.
    # Helen   (The Castro): [13:30, 17:00] and 120 minutes required.
    # Joshua  (Sunset District): [14:15, 19:30] and 90 minutes required.
    # Margaret(Haight-Ashbury): [10:15, 22:00] and 60 minutes required.
    #
    # You arrive at Pacific Heights at 9:00 (i.e. time = 540).
    #
    # Travel times (in minutes) between neighborhoods:
    #   Pacific Heights → Nob Hill: 8
    #   Pacific Heights → Russian Hill: 7
    #   Pacific Heights → The Castro: 16
    #   Pacific Heights → Sunset District: 21
    #   Pacific Heights → Haight-Ashbury: 11
    #
    #   Nob Hill → Haight-Ashbury: 13
    #   Haight-Ashbury → The Castro: 6
    #   The Castro → Sunset District: 17
    #
    # We quickly observe that meeting Sarah is infeasible,
    # because even leaving Pacific Heights immediately for Russian Hill (7 min travel)
    # would get you there at 9:07, leaving only 23 minutes until 9:30 which is less than 45 minutes.
    #
    # Thus, the best schedule meets 4 friends: Ronald, Margaret, Helen, and Joshua.
    #
    # We now decide on an ordering that respects both time‐windows and travel:
    #   1. Start at Pacific Heights (9:00). Travel 8 min → Nob Hill.
    #      Meet Ronald at Nob Hill no earlier than 10:00 until at least 105 minutes.
    #   2. Then travel from Nob Hill to Haight-Ashbury (13 min) for Margaret’s meeting.
    #      Margaret is available from 10:15; we must meet for 60 minutes.
    #   3. Next, travel from Haight-Ashbury to The Castro (6 min) so that
    #      after waiting for Helen’s window (from 13:30 on) you can meet her for 120 minutes.
    #   4. Finally, from The Castro travel (17 min) to Sunset District for Joshua,
    #      whose window begins at 14:15, and meet for 90 minutes.
    
    # Define start time variables for each meeting (in minutes from midnight)
    s_R = Int('s_R')  # Ronald (Nob Hill)
    s_M = Int('s_M')  # Margaret (Haight-Ashbury)
    s_H = Int('s_H')  # Helen (The Castro)
    s_J = Int('s_J')  # Joshua (Sunset District)
    # (Sarah is skipped as her minimum meeting duration cannot be met.)

    # Meeting durations
    d_R = 105  # Ronald's required minutes
    d_M = 60   # Margaret's required minutes
    d_H = 120  # Helen's required minutes
    d_J = 90   # Joshua's required minutes

    solver = Solver()

    # -------------------------
    # Time window constraints:
    # Ronald is available from 10:00 (600) to 17:00 (1020).
    solver.add(s_R >= 600)
    solver.add(s_R + d_R <= 1020)

    # Margaret is available [10:15 (615) to 22:00 (1320)].
    solver.add(s_M >= 615)
    solver.add(s_M + d_M <= 1320)

    # Helen is available [13:30 (810) to 17:00 (1020)].
    solver.add(s_H >= 810)
    solver.add(s_H + d_H <= 1020)

    # Joshua is available [14:15 (855) to 19:30 (1170)].
    solver.add(s_J >= 855)
    solver.add(s_J + d_J <= 1170)

    # -------------------------
    # Travel constraints:
    # You start at Pacific Heights at 9:00 (540 minutes).
    # To get to Nob Hill for Ronald, you need 8 minutes:
    #   -> s_R must be at least max(540+8, 600) = 600. (Already enforced above.)
    
    # From Ronald (Nob Hill) to Margaret (Haight-Ashbury): travel time = 13 minutes.
    # So Margaret's meeting must start after Ronald’s meeting ends plus 13 minutes.
    solver.add(s_M >= s_R + d_R + 13)
    
    # From Margaret (Haight-Ashbury) to Helen (The Castro): travel time = 6 minutes.
    solver.add(s_H >= s_M + d_M + 6)
    
    # From Helen (The Castro) to Joshua (Sunset District): travel time = 17 minutes.
    solver.add(s_J >= s_H + d_H + 17)

    # -------------------------
    # Check if the constraints are satisfiable:
    if solver.check() == sat:
        model = solver.model()
        sol_s_R = model[s_R].as_long()
        sol_s_M = model[s_M].as_long()
        sol_s_H = model[s_H].as_long()
        sol_s_J = model[s_J].as_long()

        # Helper function to convert minutes to "HH:MM" 24-hour format.
        def format_time(t):
            hours = t // 60
            minutes = t % 60
            return f"{hours:02d}:{minutes:02d}"

        itinerary = [
            {"action": "meet", "person": "Ronald", "start_time": format_time(sol_s_R), "end_time": format_time(sol_s_R + d_R)},
            {"action": "meet", "person": "Margaret", "start_time": format_time(sol_s_M), "end_time": format_time(sol_s_M + d_M)},
            {"action": "meet", "person": "Helen", "start_time": format_time(sol_s_H), "end_time": format_time(sol_s_H + d_H)},
            {"action": "meet", "person": "Joshua", "start_time": format_time(sol_s_J), "end_time": format_time(sol_s_J + d_J)}
        ]
        schedule = {"itinerary": itinerary}
        print(json.dumps(schedule, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()