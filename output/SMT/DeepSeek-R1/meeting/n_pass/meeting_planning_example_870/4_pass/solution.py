import z3
import sys

def main():
    lines = []
    if len(sys.argv) >= 2:
        with open(sys.argv[1], 'r') as f:
            lines = f.readlines()
    else:
        lines = sys.stdin.readlines()

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

    # Calculate required bits for BitVec (log2(num_participants+1))
    n_bits = (num_participants + 1).bit_length()
    solver = z3.Solver()
    schedule = [[z3.BitVec(f"schedule_{d}_{t}", n_bits) for t in range(num_time_slots)] for d in range(num_days)]
    
    constraints = []
    
    # Domain constraint: 0 (free) to num_participants (inclusive)
    for d in range(num_days):
        for t in range(num_time_slots):
            constraints.append(z3.And(schedule[d][t] >= 0, schedule[d][t] <= num_participants))
    
    # Availability constraint
    for p in range(num_participants):
        p_val = p + 1  # Participant value (1-indexed)
        for d in range(num_days):
            for t in range(num_time_slots):
                # Only enforce if participant is not available
                if availability[p][d][t] == 0:
                    constraints.append(z3.Implies(schedule[d][t] == p_val, False))
    
    # Required meetings constraint (optimized)
    for p in range(num_participants):
        p_val = p + 1
        for d in range(num_days):
            if requires_meeting[p][d] == 1:
                # Precompute available slots
                available_slots = []
                for t in range(num_time_slots):
                    if availability[p][d][t] == 1:
                        available_slots.append(schedule[d][t] == p_val)
                
                if not available_slots:
                    # Early termination if no available slots
                    print("No solution exists.")
                    return
                
                constraints.append(z3.Or(available_slots))
    
    solver.add(constraints)
    
    # Set timeout (10 seconds)
    solver.set("timeout", 10000)
    
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