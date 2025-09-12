import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    solver = z3.Solver()

    # Variables
    barbara_first = z3.Bool('barbara_first')
    B_start = z3.Int('B_start')
    B_end = z3.Int('B_end')
    K_start = z3.Int('K_start')
    K_end = z3.Int('K_end')
    arrival_B = z3.Int('arrival_B')  # arrival time at GGP before meeting Barbara
    arrival_K = z3.Int('arrival_K')  # arrival time at Chinatown before meeting Kenneth

    # Constraints for Barbara's meeting
    solver.add(B_end - B_start >= 45)
    solver.add(B_end <= 1140)  # 7:00 PM is 19*60=1140
    solver.add(B_start >= arrival_B)

    # Constraints for Kenneth's meeting
    solver.add(K_end - K_start >= 90)
    solver.add(K_end <= 900)   # 3:00 PM is 15*60=900
    solver.add(K_start >= arrival_K)
    solver.add(K_start >= 720) # 12:00 PM is 12*60=720

    # Constraints for arrival_B and arrival_K based on barbara_first
    solver.add(z3.Implies(barbara_first, arrival_B == 540 + 23))  # FD to GGP is 23 min
    solver.add(z3.Implies(z3.Not(barbara_first), arrival_B == K_end + 23))  # from Chinatown to GGP is 23 min

    solver.add(z3.Implies(barbara_first, arrival_K == B_end + 23))  # GGP to Chinatown is 23 min
    solver.add(z3.Implies(z3.Not(barbara_first), arrival_K == 540 + 5))  # FD to Chinatown is 5 min

    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        bf = model.eval(barbara_first).as_string() == 'True'

        b_start = model.eval(B_start).as_long()
        b_end = model.eval(B_end).as_long()
        k_start = model.eval(K_start).as_long()
        k_end = model.eval(K_end).as_long()

        # Build the itinerary
        itinerary = []
        if bf:
            # Barbara first
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": to_time_str(b_start),
                "end_time": to_time_str(b_end)
            })
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": to_time_str(k_start),
                "end_time": to_time_str(k_end)
            })
        else:
            # Kenneth first
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Kenneth",
                "start_time": to_time_str(k_start),
                "end_time": to_time_str(k_end)
            })
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Barbara",
                "start_time": to_time_str(b_start),
                "end_time": to_time_str(b_end)
            })

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()