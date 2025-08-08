# Fixed flight constraints
for i in range(25):
    solver.add(Or(
        s[i] == s[i+1],
        And(s[i] != s[i+1], valid_flight(s[i], s[i+1]))
    ))  # Added missing parenthesis here