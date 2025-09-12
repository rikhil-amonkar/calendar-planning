# Define required durations for each city
required_duration = {0: 2, 1: 7, 2: 3, 3: 4}

for i in range(4):
    city = seq[i]
    si = s[i]
    in_transitions = 1 if i > 0 else 0
    out_transitions = 1 if i < 3 else 0

    # Use Z3 If to express the duration conditionally
    rd = z3.If(city == 0, required_duration[0],
               z3.If(city == 1, required_duration[1],
                     z3.If(city == 2, required_duration[2],
                           required_duration[3])))

    solver.add(si + in_transitions + out_transitions == rd)