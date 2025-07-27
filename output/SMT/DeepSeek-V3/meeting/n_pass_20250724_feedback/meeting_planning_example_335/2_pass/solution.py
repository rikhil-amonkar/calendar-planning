from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define time variables for each meeting in minutes since 9:00 AM (540 minutes)
    # Helen: North Beach 9:00AM-5:00PM (540-1020)
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    # Kevin: Mission District 10:45AM-2:45PM (645-885)
    kevin_start = Int('kevin_start')
    kevin_end = Int('kevin_end')
    # Amanda: Alamo Square 7:45PM-9:00PM (1185-1260)
    amanda_start = Int('amanda_start')
    amanda_end = Int('amanda_end')
    # Betty: Financial District 7:00PM-9:45PM (1140-1305)
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')

    # Add constraints for each meeting
    # Helen: min 15 minutes, between 540-1020
    s.add(helen_start >= 540)
    s.add(helen_end <= 1020)
    s.add(helen_end - helen_start >= 15)

    # Kevin: min 45 minutes, between 645-885
    s.add(kevin_start >= 645)
    s.add(kevin_end <= 885)
    s.add(kevin_end - kevin_start >= 45)

    # Amanda: min 60 minutes, between 1185-1260
    s.add(amanda_start >= 1185)
    s.add(amanda_end <= 1260)
    s.add(amanda_end - amanda_start >= 60)

    # Betty: min 90 minutes, between 1140-1305
    s.add(betty_start >= 1140)
    s.add(betty_end <= 1305)
    s.add(betty_end - betty_start >= 90)

    # Initial location: Pacific Heights at 540 (9:00 AM)
    # Try different sequences to find a feasible schedule
    # Sequence 1: Helen -> Kevin -> Amanda -> Betty
    # Travel times:
    # Pacific Heights to North Beach: 9 minutes (for Helen)
    s.add(helen_start >= 540 + 9)
    # North Beach to Mission District: 18 minutes (after Helen)
    s.add(kevin_start >= helen_end + 18)
    # Mission District to Alamo Square: 11 minutes (after Kevin)
    s.add(amanda_start >= kevin_end + 11)
    # Alamo Square to Financial District: 17 minutes (after Amanda)
    s.add(betty_start >= amanda_end + 17)

    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Convert minutes to HH:MM format
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        helen_s = m.eval(helen_start).as_long()
        helen_e = m.eval(helen_end).as_long()
        kevin_s = m.eval(kevin_start).as_long()
        kevin_e = m.eval(kevin_end).as_long()
        amanda_s = m.eval(amanda_start).as_long()
        amanda_e = m.eval(amanda_end).as_long()
        betty_s = m.eval(betty_start).as_long()
        betty_e = m.eval(betty_end).as_long()

        itinerary = [
            {"action": "meet", "person": "Helen", "start_time": minutes_to_time(helen_s), "end_time": minutes_to_time(helen_e)},
            {"action": "meet", "person": "Kevin", "start_time": minutes_to_time(kevin_s), "end_time": minutes_to_time(kevin_e)},
            {"action": "meet", "person": "Amanda", "start_time": minutes_to_time(amanda_s), "end_time": minutes_to_time(amanda_e)},
            {"action": "meet", "person": "Betty", "start_time": minutes_to_time(betty_s), "end_time": minutes_to_time(betty_e)}
        ]
        return {"itinerary": itinerary}
    else:
        # Try a different sequence if the first one fails
        s.reset()
        s = Solver()

        # Define variables again
        helen_start = Int('helen_start')
        helen_end = Int('helen_end')
        kevin_start = Int('kevin_start')
        kevin_end = Int('kevin_end')
        amanda_start = Int('amanda_start')
        amanda_end = Int('amanda_end')
        betty_start = Int('betty_start')
        betty_end = Int('betty_end')

        # Add constraints for each meeting
        s.add(helen_start >= 540)
        s.add(helen_end <= 1020)
        s.add(helen_end - helen_start >= 15)

        s.add(kevin_start >= 645)
        s.add(kevin_end <= 885)
        s.add(kevin_end - kevin_start >= 45)

        s.add(amanda_start >= 1185)
        s.add(amanda_end <= 1260)
        s.add(amanda_end - amanda_start >= 60)

        s.add(betty_start >= 1140)
        s.add(betty_end <= 1305)
        s.add(betty_end - betty_start >= 90)

        # Sequence 2: Kevin -> Helen -> Amanda -> Betty
        # Pacific Heights to Mission District: 15 minutes (for Kevin)
        s.add(kevin_start >= 540 + 15)
        # Mission District to North Beach: 17 minutes (after Kevin)
        s.add(helen_start >= kevin_end + 17)
        # North Beach to Alamo Square: 16 minutes (after Helen)
        s.add(amanda_start >= helen_end + 16)
        # Alamo Square to Financial District: 17 minutes (after Amanda)
        s.add(betty_start >= amanda_end + 17)

        if s.check() == sat:
            m = s.model()
            def minutes_to_time(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"

            kevin_s = m.eval(kevin_start).as_long()
            kevin_e = m.eval(kevin_end).as_long()
            helen_s = m.eval(helen_start).as_long()
            helen_e = m.eval(helen_end).as_long()
            amanda_s = m.eval(amanda_start).as_long()
            amanda_e = m.eval(amanda_end).as_long()
            betty_s = m.eval(betty_start).as_long()
            betty_e = m.eval(betty_end).as_long()

            itinerary = [
                {"action": "meet", "person": "Kevin", "start_time": minutes_to_time(kevin_s), "end_time": minutes_to_time(kevin_e)},
                {"action": "meet", "person": "Helen", "start_time": minutes_to_time(helen_s), "end_time": minutes_to_time(helen_e)},
                {"action": "meet", "person": "Amanda", "start_time": minutes_to_time(amanda_s), "end_time": minutes_to_time(amanda_e)},
                {"action": "meet", "person": "Betty", "start_time": minutes_to_time(betty_s), "end_time": minutes_to_time(betty_e)}
            ]
            return {"itinerary": itinerary}
        else:
            return {"error": "No feasible schedule found"}

result = solve_scheduling_problem()
print(json.dumps(result, indent=2))