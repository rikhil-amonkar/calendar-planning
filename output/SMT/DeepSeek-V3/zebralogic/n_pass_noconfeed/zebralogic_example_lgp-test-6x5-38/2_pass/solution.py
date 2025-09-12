# Clue 10: Alice is directly left of the person who owns a BMW 3 Series.
for i in houses:
    # Fixed: Check that Alice is not in the last house before accessing i+1
    solver.add(Implies(name_vars[i-1] == name_idx['Alice'], 
                      And(i < 6, car_model_vars[i] == car_model_idx['bmw 3 series'])))