import z3
import json

def main():
    solver = z3.Solver()

    depart_GGP = z3.Int('depart_GGP')
    S = z3.Int('S')
    E = z3.Int('E')

    solver.add(depart_GGP >= 540)  # 9:00 AM
    solver.add(S >= 960)  # 4:00 PM
    solver.add(E == S + 105)
    solver.add(E <= 1305)  # 9:45 PM
    solver.add(depart_GGP + 23 <= S)

    if solver.check() == z3.sat:
        model = solver.model()
        depart_GGP_val = model.evaluate(depart_GGP).as_long()
        S_val = model.evaluate(S).as_long()
        E_val = model.evaluate(E).as_long()

        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        itinerary = [
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": to_time_str(S_val),
                "end_time": to_time_str(E_val)
            }
        ]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()