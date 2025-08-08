import z3
import sys

def main():
    lines = []
    if len(sys.argv) >= 2:
        # Read from input file
        with open(sys.argv[1], 'r') as f:
            lines = f.readlines()
    else:
        # Read from standard input
        lines = sys.stdin.readlines()

    # Process input data
    num_participants = int(lines[0].strip())
    num_days = int(lines[1].strip())
    num_time_slots = int(lines[2].strip())
    
    index = 3
    availability = []
    for _ in range(num_participants):
        participant_availability = []
        for _ in range(num_days):
            day_availability = list(map(int, lines[index].split()))
            participant_availability.append(day_availability)
            index += 1
        availability.append(participant_availability)
    
    requires_meeting = []
    for _ in range(num_participants):
        meeting_days = list(map(int, lines[index].split()))
        requires_meeting.append(meeting_days)
        index += 1

    solver = z3.Solver()
    schedule = [[z3.Int(f"schedule_{d}_{t}") for t in range(num_time_slots)] for d in range(num_days)]
    
    constraints = []
    
    # Constraint: Each time slot is either free (0) or assigned to one participant (1..num_participants)
    for d in range(num_days):
        for t in range(num_time_slots):
            constraints.append(z3.And(schedule[d][t] >= 0, schedule[d][t] <= num_participants))
    
    # Constraint: Meetings can only be scheduled when participants are available
    for p in range(num_participants):
        for d in range(num_days):
            for t in range(num_time_slots):
                constraints.append(z3.Implies(schedule[d][t] == p+1, availability[p][d][t] == 1))
    
    # Constraint: Participants must have meetings on required days
    for p in range(num_participants):
        for d in range(num_days):
            if requires_meeting[p][d] == 1:
                day_constraints = []
                for t in range(num_time_slots):
                    if availability[p][d][t] == 1:
                        day_constraints.append(schedule[d][t] == p+1)
                constraints.append(z3.Or(day_constraints))
    
    solver.add(constraints)
    
    # Solve and output results
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