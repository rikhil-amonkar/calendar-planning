for step in range(6):
    meet = Bool(f'meet_{step}')
    person = Int(f'person_{step}')
    start = Int(f'start_{step}')
    meet_vars.append(meet)
    person_vars.append(person)
    start_vars.append(start)
    end = end_vars[step]
    loc = loc_vars[step]

    # Determine previous end and loc based on step
    if step == 0:
        prev_end = 540  # Starting at 9:00 AM
        prev_loc = 0    # Embarcadero
    else:
        prev_end = end_vars[step-1]
        prev_loc = loc_vars[step-1]

    # If meet is true, person must be between 0 and 5
    solver.add(Implies(meet, And(person >= 0, person <= 5)))

    # For each possible person, add constraints
    for p in range(6):
        p_loc = friends[p]['location']
        p_start = friends[p]['available_start']
        p_end_time = friends[p]['available_end']
        p_duration = friends[p]['duration']

        # Compute travel_time
        if step == 0:
            # prev_loc is a concrete integer (0)
            travel_time = travel_time_matrix[0][p_loc]
        else:
            # prev_loc is a Z3 variable, build the If chain
            tt = travel_time_matrix[0][p_loc]
            for i in range(1, 7):
                tt = If(prev_loc == i, travel_time_matrix[i][p_loc], tt)
            travel_time = tt

        solver.add(Implies(And(meet, person == p), start >= prev_end + travel_time))
        solver.add(Implies(And(meet, person == p), start >= p_start))
        solver.add(Implies(And(meet, person == p), start + p_duration <= p_end_time))
        solver.add(Implies(And(meet, person == p), end == start + p_duration))
        solver.add(Implies(And(meet, person == p), loc == p_loc))

    # If not meet, then end is prev_end and loc is prev_loc
    solver.add(Implies(Not(meet), end == prev_end))
    solver.add(Implies(Not(meet), loc == prev_loc))