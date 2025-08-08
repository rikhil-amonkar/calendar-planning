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

    # Calculate required bits for BitVec
    n_bits = (num_participants + 1).bit_length()
    solver = z3.Solver()
    schedule = [[z3.BitVec(f"schedule_{d}_{t}", n_bits) for t in range(num_time_slots)] for d in range(num_days)]
    
    # Precompute allowed values for each time slot
    allowed_values = [[[] for t in range(num_time_slots)] for d in range(num_days)]
    for d in range(num_days):
        for t in range(num_time_slots):
            # Always allow 0 (free slot)
            allowed_values[d][t].append(z3.BitVecVal(0, n_bits))
            # Allow participants who are available
            for p in range(num_participants):
                if availability[p][d][t] == 1:
                    allowed_values[d][t].append(z3.BitVecVal(p+1, n_bits))
    
    constraints = []
    
    # Domain constraint: Each time slot must be one of the allowed values
    for d in range(num_days):
        for t in range(num_time_slots):
            constraints.append(z3.Or([schedule[d][t] == val for val in allowed_values[d][t]]))
    
    # Required meetings constraint
    for p in range(num_participants):
        for d in range(num_days):
            if requires_meeting[p][d] == 1:
                slot_constraints = []
                for t in range(num_time_slots):
                    if availability[p][d][t] == 1:
                        slot_constraints.append(schedule[d][t] == z3.BitVecVal(p+1, n_bits))
                if not slot_constraints:
                    # Immediately return if no available slots
                    print("No solution exists.")
                    return
                constraints.append(z3.Or(slot_constraints))
    
    solver.add(constraints)
    solver.set("timeout", 30000)  # 30 seconds timeout
    
    # Solve and output
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