import json
from z3 import *

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    opt = Optimize()

    # Define variables
    met_M = Bool('met_M')
    met_N = Bool('met_N')
    met_E = Bool('met_E')

    s_M = Int('s_M')
    e_M = Int('e_M')
    s_N = Int('s_N')
    e_N = Int('e_N')
    s_E = Int('s_E')
    e_E = Int('e_E')

    # Constraints for Melissa (M)
    opt.add(Implies(met_M, s_M >= 510))  # 8:30 AM
    opt.add(Implies(met_M, e_M == s_M + 15))
    opt.add(Implies(met_M, e_M <= 1200))  # 8:00 PM

    opt.add(Implies(met_M, Or(
        s_M >= 540 + 25,  # FW to GGP: 25
        And(met_N, s_M >= e_N + 12),  # Presidio to GGP: 12
        And(met_E, s_M >= e_E + 9)  # RD to GGP: 9
    )))

    # Constraints for Nancy (N)
    opt.add(Implies(met_N, s_N >= 1185))  # 7:45 PM
    opt.add(Implies(met_N, e_N == s_N + 105))
    opt.add(Implies(met_N, e_N <= 1320))  # 10:00 PM

    opt.add(Implies(met_N, Or(
        s_N >= 540 + 17,  # FW to Presidio: 17
        And(met_M, s_N >= e_M + 11),  # GGP to Presidio: 11
        And(met_E, s_N >= e_E + 7)  # RD to Presidio: 7
    )))

    # Constraints for Emily (E)
    opt.add(Implies(met_E, s_E >= 1005))  # 4:45 PM
    opt.add(Implies(met_E, e_E == s_E + 120))
    opt.add(Implies(met_E, e_E <= 1320))  # 10:00 PM

    opt.add(Implies(met_E, Or(
        s_E >= 540 + 18,  # FW to RD: 18
        And(met_M, s_E >= e_M + 7),  # GGP to RD: 7
        And(met_N, s_E >= e_N + 7)  # Presidio to RD: 7
    )))

    # Pairwise constraints
    opt.add(Implies(And(met_M, met_N), Or(
        s_M >= e_N + 12,  # Presidio to GGP
        s_N >= e_M + 11  # GGP to Presidio
    )))
    opt.add(Implies(And(met_M, met_E), Or(
        s_M >= e_E + 9,  # RD to GGP
        s_E >= e_M + 7  # GGP to RD
    )))
    opt.add(Implies(And(met_N, met_E), Or(
        s_N >= e_E + 7,  # RD to Presidio
        s_E >= e_N + 7  # Presidio to RD
    )))

    # Objective: maximize the number of friends met
    objective = If(met_M, 1, 0) + If(met_N, 1, 0) + If(met_E, 1, 0)
    opt.maximize(objective)

    # Check satisfiability
    if opt.check() == sat:
        model = opt.model()
        met_M_val = is_true(model.eval(met_M))
        met_N_val = is_true(model.eval(met_N))
        met_E_val = is_true(model.eval(met_E))

        # Collect the meetings
        meetings = []
        if met_M_val:
            s = model.eval(s_M).as_long()
            e = model.eval(e_M).as_long()
            meetings.append((s, 'meet', 'Golden Gate Park', 'Melissa', e))
        if met_N_val:
            s = model.eval(s_N).as_long()
            e = model.eval(e_N).as_long()
            meetings.append((s, 'meet', 'Presidio', 'Nancy', e))
        if met_E_val:
            s = model.eval(s_E).as_long()
            e = model.eval(e_E).as_long()
            meetings.append((s, 'meet', 'Richmond District', 'Emily', e))

        # Sort meetings by start time
        meetings.sort()

        # Build itinerary
        itinerary = []
        for s, action, location, person, e in meetings:
            itinerary.append({
                "action": action,
                "location": location,
                "person": person,
                "start_time": to_time_str(s),
                "end_time": to_time_str(e)
            })

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()