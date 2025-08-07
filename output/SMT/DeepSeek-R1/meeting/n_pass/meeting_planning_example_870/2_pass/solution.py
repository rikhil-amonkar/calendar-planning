import z3
import sys

def main():
    if len(sys.argv) != 2:
        print("Usage: python solution.py <input_file>")
        return

    input_file = sys.argv[1]
    with open(input_file, 'r') as f:
        num_participants = int(f.readline().strip())
        num_days = int(f.readline().strip())
        num_time_slots = int(f.readline().strip())
        
        availability = []
        for _ in range(num_participants):
            participant_availability = []
            for _ in range(num_days):
                day_availability = list(map(int, f.readline().split()))
                participant_availability.append(day_availability)
            availability.append(participant_availability)
        
        requires_meeting = []
        for _ in range(num_participants):
            meeting_days = list(map(int, f.readline().split()))
            requires_meeting.append(meeting_days)

    solver = z3.Solver()
    schedule = [[z3.Int(f"schedule_{d}_{t}") for t in range(num_time_slots)] for d in range(num_days)]
    
    constraints = []
    
    # Constraint: Each time slot is either free or assigned to one participant
    for d in range(num_days):
        for t in range(num_time_slots):
            constraints.append(z3.And(schedule[d][t] >= 0, schedule[d][t] <= num_participants))
    
    # Constraint: A meeting can only be scheduled if the participant is available
    for p in range(num_participants):
        for d in range(num_days):
            for t in range(num_time_slots):
                constraints.append(z3.Implies(schedule[d][t] == p, availability[p][d][t] == 1))
    
    # Constraint: If a participant requires a meeting on a day, they must have at least one meeting
    for p in range(num_participants):
        for d in range(num_days):
            if requires_meeting[p][d] == 1:
                day_constraints = []
                for t in range(num_time_slots):
                    day_constraints.append(z3.And(availability[p][d][t] == 1, schedule[d][t] == p))
                constraints.append(z3.Or(day_constraints))
    
    # Add all constraints to the solver
    solver.add(constraints)
    
    # Check for satisfiability
    if solver.check() == z3.sat:
        model = solver.model()
        output = []
        for d in range(num_days):
            day_schedule = []
            for t in range(num_time_slots):
                slot_val = model.evaluate(schedule[d][t])
                day_schedule.append(str(slot_val))
            output.append(" ".join(day_schedule))
        print("\n".join(output))
    else:
        print("No solution exists.")

if __name__ == "__main__":
    main()