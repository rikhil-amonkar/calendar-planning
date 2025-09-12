# Constraints for consecutive flights
for i in range(9):
    # (order[i], order[i+1]) must be in allowed_flights
    allowed_conditions = []
    for a, b in allowed_flights:
        allowed_conditions.append(z3.And(order[i] == a, order[i+1] == b))
    solver.add(z3.Or(allowed_conditions))