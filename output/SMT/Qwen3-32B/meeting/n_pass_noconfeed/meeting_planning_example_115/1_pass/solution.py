import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    solver = z3.Solver()

    # Variables
    carol_start = z3.Int('carol_start')
    carol_end = z3.Int('carol_end')
    jessica_start = z3.Int('jessica_start')
    jessica_end = z3.Int('jessica_end')

    # Carol's constraints (11:30 AM to 3:00 PM)
    solver.add(carol_start >= 690)  # 11:30 AM in minutes
    solver.add(carol_end <= 900)    # 3:00 PM in minutes
    solver.add(carol_end - carol_start >= 60)  # Minimum 60 minutes

    # Jessica's constraints (3:30 PM to 4:45 PM)
    solver.add(jessica_start >= 930)  # 3:30 PM in minutes
    solver.add(jessica_end <= 1005)   # 4:45 PM in minutes
    solver.add(jessica_end - jessica_start >= 45)  # Minimum 45 minutes

    # Timeline constraints
    # Travel from Richmond to Marina (9 minutes)
    # Carol's meeting must start after arrival at Marina (9:00 AM + 9 min = 9:09 AM = 549)
    # But Carol's earliest availability is 11:30 AM (690), so no need to add
    # Travel from Marina to Pacific Heights (7 minutes)
    solver.add(jessica_start >= carol_end + 7)
    solver.add(jessica_start >= 930)  # Jessica's earliest start time

    if solver.check() == z3.sat:
        model = solver.model()
        c_start = model.eval(carol_start).as_long()
        c_end = model.eval(carol_end).as_long()
        j_start = model.eval(jessica_start).as_long()
        j_end = model.eval(jessica_end).as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Carol",
                "start_time": to_time_str(c_start),
                "end_time": to_time_str(c_end)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Jessica",
                "start_time": to_time_str(j_start),
                "end_time": to_time_str(j_end)
            }
        ]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()